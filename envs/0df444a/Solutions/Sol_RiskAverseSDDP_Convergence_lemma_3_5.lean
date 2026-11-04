-- Prove2me | solution 1 for RiskAverseSDDP.Convergence.lemma_3_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:31:58.111322+00:00
-- url     : https://prove2.me/submissions/a4792cae-d768-4d68-8cb3-0fd897ac37af
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Convergence_Run
import Theorems.Thm_RiskAverseSDDP_Convergence_proposition_3_1
import Theorems.Thm_RiskAverseSDDP_Convergence_lemma_3_4
open Filter Topology
open RiskAverseSDDP.Convergence

namespace RASDDPLem35

lemma mul_add_coe {w : ℝ} (hw : 0 ≤ w) (z : EReal) (c : ℝ) :
    (w : EReal) * (z + (c : EReal)) = (w : EReal) * z + ((w * c : ℝ) : EReal) := by
  rw [EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hw) (EReal.coe_ne_top w),
    EReal.coe_mul]

lemma sum_add_coe {M : ℕ} (a : Fin M → EReal) (b : Fin M → ℝ) :
    ∑ j, (a j + ((b j : ℝ) : EReal)) = (∑ j, a j) + ((∑ j, b j : ℝ) : EReal) := by
  rw [Finset.sum_add_distrib]
  congr 1
  induction (Finset.univ : Finset (Fin M)) using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, EReal.coe_add]

lemma stageVal_mono {T n M q p : ℕ} (D : Model T n M q p) (s : ℕ) (j : Fin M)
    {V W : Hist n (s + 1) → EReal} (h : ∀ y, V y ≤ W y) (x : Hist n s) :
    D.stageVal s j V x ≤ D.stageVal s j W x := by
  unfold Model.stageVal
  exact iInf₂_mono fun y _ => add_le_add_right (h _) _

lemma Q_last {T n M q p : ℕ} (D : Model T n M q p) (x : Hist n T) : D.Q T x = 0 := by
  simp [Model.Q, Model.Qaux]

lemma Q_succ {T n M q p : ℕ} (D : Model T n M q p) (s : ℕ) (hs : s + 2 ≤ T)
    (x : Hist n (s + 1)) :
    D.Q (s + 1) x = D.rho (s + 2) (fun j => D.stageVal (s + 1) j (D.Q (s + 2)) x) := by
  have h : T - (s + 1) = (T - (s + 2)) + 1 := by omega
  rw [Model.Q, h, Model.Qaux]
  rfl

/-- Validity of the cuts (Lemma 3.2(a), everywhere): `𝒬^k_h ≤ 𝒬_h`. -/
lemma valid {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (hS : D.Standing) (R : Rules n M)
    (ys : ℕ → ℕ → Fin M) (r : RunData n M) (hr : D.IsRun R ys r) :
    ∀ d h, h + d = T → 1 ≤ h → ∀ k y, r.Qm k h y ≤ D.Q h y := by
  obtain ⟨hQ0, hQT, _, hcut⟩ := hr
  intro d
  induction d with
  | zero =>
    intro h hh _ k y
    have hh' : h = T := by omega
    subst hh'
    rw [hQT k, Q_last]
  | succ d ih =>
    intro h hh h1 k y
    obtain ⟨s, rfl⟩ : ∃ s, h = s + 1 := ⟨h - 1, by omega⟩
    have hs : s + 2 ≤ T := by omega
    have ih' := ih (s + 2) (by omega) (by omega)
    induction k generalizing y with
    | zero => rw [hQ0 (s + 1) h1 (by omega)]; exact bot_le
    | succ k ihk =>
      obtain ⟨hpk, _, hπ, hθ, hβ, hupd⟩ := hcut k s hs
      rw [hupd]
      refine max_le (ihk y) ?_
      set xt := r.hist (k + 1) s (sampNode ys (k + 1) s)
      set Z : Fin M → EReal := fun j => D.stageVal (s + 1) j (r.Qm k (s + 2)) xt
      set pk := R.pRule (s + 2) Z
      set d' := y - xt
      have hw : ∀ j, 0 ≤ pk j * D.Φ (s + 2) j := by
        intro j
        have hS' := hS (s + 2) (by omega) hs
        exact mul_nonneg ((hS'.2.2.1 hpk).1 j) (hS'.1 j).le
      have hinner : inner ℝ (r.β (k + 1) s) d' =
          ∑ j, (pk j * D.Φ (s + 2) j) * inner ℝ (r.π (k + 1) s j) d' := by
        rw [hβ, sum_inner]
        simp only [real_inner_smul_left]
      have hsub : ∀ j, Z j + ((inner ℝ (r.π (k + 1) s j) d' : ℝ) : EReal) ≤
          D.stageVal (s + 1) j (D.Q (s + 2)) y := by
        intro j
        exact ((hπ j).2 y).trans (stageVal_mono D (s + 1) j (ih' k) _)
      calc r.θ (k + 1) s + ((inner ℝ (r.β (k + 1) s) d' : ℝ) : EReal)
          = ∑ j, (((pk j * D.Φ (s + 2) j : ℝ) : EReal) * Z j +
              (((pk j * D.Φ (s + 2) j) * inner ℝ (r.π (k + 1) s j) d' : ℝ) : EReal)) := by
            rw [sum_add_coe, hθ, hinner]; rfl
        _ = ∑ j, ((pk j * D.Φ (s + 2) j : ℝ) : EReal) *
              (Z j + ((inner ℝ (r.π (k + 1) s j) d' : ℝ) : EReal)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [mul_add_coe (hw j)]
        _ ≤ ∑ j, ((pk j * D.Φ (s + 2) j : ℝ) : EReal) * D.stageVal (s + 1) j (D.Q (s + 2)) y := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact mul_le_mul_of_nonneg_left (hsub j) (by exact_mod_cast hw j)
        _ = D.wsum (s + 2) pk (fun j => D.stageVal (s + 1) j (D.Q (s + 2)) y) := rfl
        _ ≤ D.rho (s + 2) (fun j => D.stageVal (s + 1) j (D.Q (s + 2)) y) := by
            unfold Model.rho
            exact le_iSup₂ (f := fun π _ => D.wsum (s + 2) π
              (fun j => D.stageVal (s + 1) j (D.Q (s + 2)) y)) pk hpk
        _ = D.Q (s + 1) y := (Q_succ D s hs y).symm

lemma snoc_continuous {n s : ℕ} (x : Hist n s) : Continuous (fun y => x.snoc y) := by
  unfold Hist.snoc
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]; exact continuous_id
  · simp only [Fin.snoc_castSucc]; exact continuous_const

lemma snoc_mem_prodSet {T n M q p : ℕ} (D : Model T n M q p) (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ D.Xc 1) : (Hist.empty n).snoc y ∈ D.prodSet 1 := by
  intro i
  have hi : i = Fin.last 0 := Subsingleton.elim _ _
  subst hi
  show (WithLp.toLp 2 _ : Hist n 1) (Fin.last 0) ∈ D.Xc ((Fin.last 0).val + 1)
  rw [PiLp.toLp_apply, Fin.snoc_last]
  simpa using hy

lemma snoc_mem_prodSet' {T n M q p s : ℕ} (D : Model T n M q p) {x : Hist n s}
    {y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ D.prodSet s) (hy : y ∈ D.Xc (s + 1)) :
    x.snoc y ∈ D.prodSet (s + 1) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Hist.snoc, PiLp.toLp_apply, Fin.snoc_last, Fin.val_last]; exact hy
  · simp only [Hist.snoc, PiLp.toLp_apply, Fin.snoc_castSucc, Fin.coe_castSucc]; exact hx j

lemma hist_mem {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (R : Rules n M)
    (ys : ℕ → ℕ → Fin M) (r : RunData n M) (hr : D.IsRun R ys r) (k : ℕ) :
    ∀ s, s < T → ∀ ν : Fin s → Fin M, r.hist (k + 1) s ν ∈ D.prodSet (s + 1) := by
  intro s
  induction s with
  | zero =>
    intro hs ν
    have h := (hr.2.2.1 k 0 ν hs).2.1
    exact snoc_mem_prodSet' D (fun i => Fin.elim0 i) h.1
  | succ s ih =>
    intro hs ν
    have h := (hr.2.2.1 k (s + 1) ν hs).2.1
    exact snoc_mem_prodSet' D (ih (by omega) (Fin.init ν)) h.1

lemma sum_ne_bot {M : ℕ} (a : Fin M → EReal) (h : ∀ j, a j ≠ ⊥) : ∑ j, a j ≠ ⊥ := by
  induction (Finset.univ : Finset (Fin M)) using Finset.induction_on with
  | empty => simp
  | insert b t hb ih =>
    rw [Finset.sum_insert hb]
    exact EReal.add_ne_bot_iff.2 ⟨h b, ih⟩

lemma coe_mul_ne_bot {w : ℝ} (hw : 0 ≤ w) {z : EReal} (hz : z ≠ ⊥) : (w : EReal) * z ≠ ⊥ := by
  induction z using EReal.rec with
  | bot => exact absurd rfl hz
  | top =>
    rcases hw.eq_or_lt with h | h
    · subst h; simp
    · rw [EReal.coe_mul_top_of_pos h]; exact top_ne_bot
  | coe c => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _

lemma prodSet_compact {T n M q p : ℕ} (D : Model T n M q p) (h : ℕ)
    (hc : ∀ i, i < h → IsCompact (D.Xc (i + 1))) : IsCompact (D.prodSet h) := by
  have hEq : D.prodSet h =
      WithLp.toLp 2 '' Set.univ.pi (fun i : Fin h => D.Xc (i.val + 1)) := by
    ext z
    constructor
    · intro hz
      exact ⟨WithLp.ofLp z, fun i _ => hz i, by simp⟩
    · rintro ⟨w, hw, rfl⟩ i
      exact hw i (Set.mem_univ _)
  rw [hEq]
  exact (isCompact_univ_pi fun i : Fin h => hc i.val i.isLt).image (PiLp.continuous_toLp 2 _)


lemma cont_of_lip {E : Type*} [SeminormedAddCommGroup E] (g : E → ℝ) (C : ℝ)
    (h : ∀ y z, |g y - g z| ≤ C * ‖y - z‖) : Continuous g := by
  refine (LipschitzWith.of_dist_le_mul (K := ⟨max C 0, le_max_right _ _⟩) fun y z => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm]
  exact (h y z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

lemma coe_max' (a b : ℝ) : max (a : EReal) (b : EReal) = ((max a b : ℝ) : EReal) := by
  rcases le_total a b with hab | hab
  · rw [max_eq_right hab, max_eq_right (by exact_mod_cast hab)]
  · rw [max_eq_left hab, max_eq_left (by exact_mod_cast hab)]

lemma sum_bot {M : ℕ} (w : Fin M → ℝ) (hw : ∃ j, 0 < w j) :
    ∑ j, (w j : EReal) * ⊥ = ⊥ := by
  obtain ⟨j, hj⟩ := hw
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), EReal.coe_mul_bot_of_pos hj, EReal.bot_add]

/-- Weights of an element of `𝒫_t` are nonnegative, sum to one, and one of them is positive. -/
lemma weights {T n M q p : ℕ} (D : Model T n M q p) (hS : D.Standing) (t : ℕ) (ht2 : 2 ≤ t)
    (htT : t ≤ T) (π : Fin M → ℝ) (hπ : π ∈ D.Prisk t) :
    (∀ j, 0 ≤ π j * D.Φ t j) ∧ ∑ j, π j * D.Φ t j = 1 ∧ ∃ j, 0 < π j * D.Φ t j := by
  have hS' := hS t ht2 htT
  have hd := hS'.2.2.1 hπ
  have hw : ∀ j, 0 ≤ π j * D.Φ t j := fun j => mul_nonneg (hd.1 j) (hS'.1 j).le
  refine ⟨hw, hd.2, ?_⟩
  by_contra hne
  push_neg at hne
  have : ∑ j, π j * D.Φ t j = 0 :=
    Finset.sum_eq_zero fun j _ => le_antisymm (hne j) (hw j)
  rw [hd.2] at this; exact one_ne_zero this


lemma cut_lip {n s : ℕ} (θ : EReal) (hθ1 : θ ≠ ⊥) (hθ2 : θ ≠ ⊤) (β x : Hist n s) :
    (∀ y, θ + ((inner ℝ β (y - x) : ℝ) : EReal) ≠ ⊥ ∧ θ + ((inner ℝ β (y - x) : ℝ) : EReal) ≠ ⊤) ∧
    ∀ y z, |(θ + ((inner ℝ β (y - x) : ℝ) : EReal)).toReal -
      (θ + ((inner ℝ β (z - x) : ℝ) : EReal)).toReal| ≤ ‖β‖ * ‖y - z‖ := by
  lift θ to ℝ using ⟨hθ2, hθ1⟩ with t
  refine ⟨fun y => ?_, fun y z => ?_⟩
  · rw [← EReal.coe_add]; exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩
  · rw [← EReal.coe_add, ← EReal.coe_add, EReal.toReal_coe, EReal.toReal_coe]
    have : t + inner ℝ β (y - x) - (t + inner ℝ β (z - x)) = inner ℝ β (y - z) := by
      simp only [inner_sub_right]; ring
    rw [this]
    exact abs_real_inner_le_norm _ _

lemma lip_max {E : Type*} [SeminormedAddCommGroup E] (a b : E → EReal)
    (ha : ∀ y, a y ≠ ⊥ ∧ a y ≠ ⊤) (hb : ∀ y, b y ≠ ⊥ ∧ b y ≠ ⊤) (Ca Cb : ℝ)
    (hla : ∀ y z, |(a y).toReal - (a z).toReal| ≤ Ca * ‖y - z‖)
    (hlb : ∀ y z, |(b y).toReal - (b z).toReal| ≤ Cb * ‖y - z‖) :
    (∀ y, max (a y) (b y) ≠ ⊥ ∧ max (a y) (b y) ≠ ⊤) ∧
    ∀ y z, |(max (a y) (b y)).toReal - (max (a z) (b z)).toReal| ≤ max Ca Cb * ‖y - z‖ := by
  have hm : ∀ y, max (a y) (b y) = ((max (a y).toReal (b y).toReal : ℝ) : EReal) := by
    intro y
    rw [← coe_max', EReal.coe_toReal (ha y).2 (ha y).1, EReal.coe_toReal (hb y).2 (hb y).1]
  refine ⟨fun y => by rw [hm y]; exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩, fun y z => ?_⟩
  rw [hm y, hm z, EReal.toReal_coe, EReal.toReal_coe]
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · exact (hla y z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · exact (hlb y z).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

section main
variable {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ)
    (hS : D.Standing) (hH2 : D.H2 ε) (R : Rules n M) (ys : ℕ → ℕ → Fin M) (r : RunData n M)
    (hr : D.IsRun R ys r)
include hS hH2 hr

lemma rlz_all (s : ℕ) (j : Fin M) : j ∈ Model.Rlz (M := M) (s + 1 + 1) := by
  simp [Model.Rlz]

omit hS hH2 hr in
lemma rlz_all' (s : ℕ) (j : Fin M) : j ∈ Model.Rlz (M := M) (s + 1 + 1) := by
  simp [Model.Rlz]

/-- Claim A: `𝒬^k_h ≡ -∞` while `k + h + 1 ≤ T`. -/
lemma claimA : ∀ k h, 1 ≤ h → k + h + 1 ≤ T → ∀ y, r.Qm k h y = ⊥ := by
  intro k
  induction k with
  | zero => intro h h1 hk y; rw [hr.1 h h1 (by omega)]
  | succ k ih =>
    intro h h1 hk y
    obtain ⟨s, rfl⟩ : ∃ s, h = s + 1 := ⟨h - 1, by omega⟩
    obtain ⟨hpk, -, -, hθ, -, hupd⟩ := hr.2.2.2 k s (by omega)
    rw [hupd]
    beta_reduce
    obtain ⟨-, -, -, -, hne, -⟩ := hH2.2 (s + 1) (by omega)
    have hxt := hist_mem D R ys r hr k s (by omega) (sampNode ys (k + 1) s)
    have hZ : ∀ j, D.stageVal (s + 1) j (r.Qm k (s + 2))
        (r.hist (k + 1) s (sampNode ys (k + 1) s)) = ⊥ := by
      intro j
      obtain ⟨y0, hy0⟩ := hne j (rlz_all' s j) _ (Metric.self_subset_cthickening _ hxt)
      refine le_bot_iff.1 (iInf₂_le_of_le y0 hy0 ?_)
      rw [ih (s + 2) (by omega) (by omega) _]; simp
    have hθb : r.θ (k + 1) s = ⊥ := by
      rw [hθ]
      set Z : Fin M → EReal := fun j => D.stageVal (s + 1) j (r.Qm k (s + 2))
        (r.hist (k + 1) s (sampNode ys (k + 1) s)) with hZdef
      set pk := R.pRule (s + 2) Z
      have hZ' : ∀ j, Z j = ⊥ := hZ
      have hw := (weights D hS (s + 2) (by omega) (by omega) pk hpk).2.2
      unfold Model.wsum
      simp only [hZ']
      exact sum_bot _ hw
    rw [ih (s + 1) h1 (by omega) y, hθb, EReal.bot_add, max_self]

/-- Lower bound: a stage value with a finite continuous cost-to-go is `> -∞` on `𝒳_{1:s+1}`. -/
lemma stageVal_ne_bot (s : ℕ) (hs : s + 2 ≤ T) (j : Fin M) (V : Hist n (s + 2) → EReal)
    (hV : ∀ y, V y ≠ ⊥ ∧ V y ≠ ⊤) (hVc : Continuous fun y => (V y).toReal)
    (x : Hist n (s + 1)) : D.stageVal (s + 1) j V x ≠ ⊥ := by
  obtain ⟨hX, hf, -, -, -, -⟩ := hH2.2 (s + 1) (by omega)
  obtain ⟨hprop, -, hlsc⟩ := hf j (rlz_all' s j)
  obtain ⟨y0, -, hy0⟩ := ((hlsc.comp (snoc_continuous x)).lowerSemicontinuousOn _).exists_isMinOn
    hX.1 hX.2.2
  obtain ⟨y1, -, hy1⟩ := hX.2.2.exists_isMinOn hX.1
    ((hVc.comp (snoc_continuous x)).continuousOn)
  have hlow : D.f (s + 1 + 1) j (x.snoc y0) + (((V (x.snoc y1)).toReal : ℝ) : EReal) ≤
      D.stageVal (s + 1) j V x := by
    refine le_iInf₂ fun y hy => add_le_add (hy0 hy.1) ?_
    have h1 := hy1 hy.1
    simp only [Set.mem_setOf_eq, Function.comp] at h1
    calc (((V (x.snoc y1)).toReal : ℝ) : EReal) ≤ ((V (x.snoc y)).toReal : EReal) := by
          exact_mod_cast h1
      _ = V (x.snoc y) := EReal.coe_toReal (hV _).2 (hV _).1
  exact ne_bot_of_le_ne_bot (EReal.add_ne_bot_iff.2 ⟨hprop.1 _, EReal.coe_ne_bot _⟩) hlow

/-- Claim B0: finiteness and some Lipschitz constant for `k + h ≥ T`. -/
lemma claimB0 : ∀ d h, h + d = T → 1 ≤ h → ∀ k, T ≤ k + h →
    (∀ y, r.Qm k h y ≠ ⊥ ∧ r.Qm k h y ≠ ⊤) ∧
    ∃ C : ℝ, ∀ y z, |(r.Qm k h y).toReal - (r.Qm k h z).toReal| ≤ C * ‖y - z‖ := by
  intro d
  induction d with
  | zero =>
    intro h hh _ k _
    have hh' : h = T := by omega
    subst hh'
    rw [hr.2.1 k]
    exact ⟨fun _ => ⟨by simp, by simp⟩, 0, fun _ _ => by simp⟩
  | succ d ihd =>
    intro h hh h1 k
    obtain ⟨s, rfl⟩ : ∃ s, h = s + 1 := ⟨h - 1, by omega⟩
    have hs : s + 2 ≤ T := by omega
    have hε : 0 < ε := hH2.1
    induction k with
    | zero => intro hk; omega
    | succ k ihk =>
      intro hk
      obtain ⟨hpk, -, -, hθ, -, hupd⟩ := hr.2.2.2 k s hs
      rw [hupd]
      set xt := r.hist (k + 1) s (sampNode ys (k + 1) s)
      have hxt := hist_mem D R ys r hr k s (by omega) (sampNode ys (k + 1) s)
      -- θ is finite
      have hθt : r.θ (k + 1) s ≠ ⊤ := by
        have h34 := RiskAverseSDDP.Convergence.lemma_3_4 D ε hS hH2 R ys r hr s hs (k + 1) (by omega)
        rw [← h34]
        refine ne_top_of_le_ne_top ?_ (valid D hS R ys r hr (T - (s + 1)) (s + 1) (by omega)
          (by omega) (k + 1) _)
        exact ((proposition_3_1 D ε hS hH2 (s + 1) (by omega) (by omega) (ε / 2) (by linarith)
          (by linarith)).2.1 _ (Metric.self_subset_cthickening _ hxt)).2
      have hθb : r.θ (k + 1) s ≠ ⊥ := by
        obtain ⟨hVf, C, hVl⟩ := ihd (s + 2) (by omega) (by omega) k (by omega)
        rw [hθ]
        refine sum_ne_bot _ fun j => coe_mul_ne_bot
          ((weights D hS (s + 2) (by omega) hs _ hpk).1 j) ?_
        exact stageVal_ne_bot D ε hS hH2 R ys r hr s hs j _ hVf (cont_of_lip _ C hVl) xt
      obtain ⟨hcf, hcl⟩ := cut_lip _ hθb hθt (r.β (k + 1) s) xt
      by_cases hk' : T ≤ k + (s + 1)
      · obtain ⟨hf', C, hl'⟩ := ihk hk'
        obtain ⟨h1', h2'⟩ := lip_max _ _ hf' hcf C _ hl' hcl
        exact ⟨h1', _, h2'⟩
      · have hb := claimA D ε hS hH2 R ys r hr k (s + 1) h1 (by omega)
        simp only [hb, bot_le, max_eq_right]
        exact ⟨hcf, _, hcl⟩

lemma mono_Qm (s : ℕ) (hs : s + 2 ≤ T) : ∀ a b, a ≤ b → ∀ y, r.Qm a (s + 1) y ≤ r.Qm b (s + 1) y := by
  intro a b hab y
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih =>
    refine ih.trans ?_
    obtain ⟨-, -, -, -, -, hupd⟩ := hr.2.2.2 b s hs
    rw [hupd]; exact le_max_left _ _

lemma theta_fin (s : ℕ) (hs : s + 2 ≤ T) (k : ℕ) (hk : T ≤ k + 1 + (s + 1)) :
    r.θ (k + 1) s ≠ ⊥ ∧ r.θ (k + 1) s ≠ ⊤ := by
  have hε : 0 < ε := hH2.1
  obtain ⟨hpk, -, -, hθ, -, -⟩ := hr.2.2.2 k s hs
  have hxt := hist_mem D R ys r hr k s (by omega) (sampNode ys (k + 1) s)
  refine ⟨?_, ?_⟩
  · obtain ⟨hVf, C, hVl⟩ := claimB0 D ε hS hH2 R ys r hr (T - (s + 2)) (s + 2) (by omega)
      (by omega) k (by omega)
    rw [hθ]
    refine sum_ne_bot _ fun j => coe_mul_ne_bot
      ((weights D hS (s + 2) (by omega) hs _ hpk).1 j) ?_
    exact stageVal_ne_bot D ε hS hH2 R ys r hr s hs j _ hVf (cont_of_lip _ C hVl) _
  · have h34 := RiskAverseSDDP.Convergence.lemma_3_4 D ε hS hH2 R ys r hr s hs (k + 1) (by omega)
    rw [← h34]
    refine ne_top_of_le_ne_top ?_ (valid D hS R ys r hr (T - (s + 1)) (s + 1) (by omega)
      (by omega) (k + 1) _)
    exact ((proposition_3_1 D ε hS hH2 (s + 1) (by omega) (by omega) (ε / 2) (by linarith)
      (by linarith)).2.1 _ (Metric.self_subset_cthickening _ hxt)).2

lemma beta_bound (s : ℕ) (hs : s + 2 ≤ T) (k : ℕ) (hk : T ≤ k + 1 + (s + 1)) (S I : ℝ)
    (hsup : ∀ x ∈ Metric.cthickening (ε / 2) (D.prodSet (s + 1)), D.Q (s + 1) x ≤ (S : EReal))
    (hinf : ∀ x ∈ D.prodSet (s + 1), (I : EReal) ≤ r.Qm (T - (s + 1)) (s + 1) x) :
    ε / 2 * ‖r.β (k + 1) s‖ ≤ S - I := by
  have hε : 0 < ε := hH2.1
  obtain ⟨hθb, hθt⟩ := theta_fin D ε hS hH2 R ys r hr s hs k hk
  set xt := r.hist (k + 1) s (sampNode ys (k + 1) s)
  have hxt := hist_mem D R ys r hr k s (by omega) (sampNode ys (k + 1) s)
  have h34 := RiskAverseSDDP.Convergence.lemma_3_4 D ε hS hH2 R ys r hr s hs (k + 1) (by omega)
  set β := r.β (k + 1) s
  set c : ℝ := ε / (2 * ‖β‖)
  have hc0 : 0 ≤ c := div_nonneg hε.le (by positivity)
  have hcb : c * ‖β‖ ^ 2 = ε / 2 * ‖β‖ := by
    rcases eq_or_ne ‖β‖ 0 with h0 | h0
    · rw [h0]; ring
    · simp only [c]; field_simp
  have hcb' : c * ‖β‖ ≤ ε / 2 := by
    rcases eq_or_ne ‖β‖ 0 with h0 | h0
    · rw [h0]; linarith
    · simp only [c]; rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg β]
  set ystar := xt + c • β
  have hmem : ystar ∈ Metric.cthickening (ε / 2) (D.prodSet (s + 1)) := by
    refine Metric.mem_cthickening_of_dist_le ystar xt (ε / 2) _ hxt ?_
    rw [dist_eq_norm, show ystar - xt = c • β by simp [ystar], norm_smul, Real.norm_of_nonneg hc0]
    exact hcb'
  -- upper bound
  obtain ⟨-, -, -, -, -, hupd⟩ := hr.2.2.2 k s hs
  have hcut : r.θ (k + 1) s + ((inner ℝ β (ystar - xt) : ℝ) : EReal) ≤ (S : EReal) := by
    refine le_trans ?_ ((valid D hS R ys r hr (T - (s + 1)) (s + 1) (by omega) (by omega)
      (k + 1) ystar).trans (hsup _ hmem))
    rw [hupd]; exact le_max_right _ _
  have hinner : inner ℝ β (ystar - xt) = c * ‖β‖ ^ 2 := by
    rw [show ystar - xt = c • β by simp [ystar], real_inner_smul_right, real_inner_self_eq_norm_sq]
  -- lower bound
  have hlow : (I : EReal) ≤ r.θ (k + 1) s := by
    rw [← h34]
    exact (hinf _ hxt).trans (mono_Qm D ε hS hH2 R ys r hr s hs _ _ (by omega) _)
  lift r.θ (k + 1) s to ℝ using ⟨hθt, hθb⟩ with t
  rw [hinner, ← EReal.coe_add] at hcut
  have h1 : t + c * ‖β‖ ^ 2 ≤ S := by exact_mod_cast hcut
  have h2 : I ≤ t := by exact_mod_cast hlow
  linarith

lemma claimB1 (s : ℕ) (hs : s + 2 ≤ T) (Lr : ℝ) (hL0 : 0 ≤ Lr)
    (hβ : ∀ k, T ≤ k + 1 + (s + 1) → ‖r.β (k + 1) s‖ ≤ Lr) :
    ∀ k, T ≤ k + (s + 1) → ∀ y z,
      |(r.Qm k (s + 1) y).toReal - (r.Qm k (s + 1) z).toReal| ≤ Lr * ‖y - z‖ := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ihk =>
    intro hk
    obtain ⟨-, -, -, -, -, hupd⟩ := hr.2.2.2 k s hs
    rw [hupd]
    obtain ⟨hθb, hθt⟩ := theta_fin D ε hS hH2 R ys r hr s hs k hk
    obtain ⟨hcf, hcl⟩ := cut_lip _ hθb hθt (r.β (k + 1) s) (r.hist (k + 1) s (sampNode ys (k + 1) s))
    have hcl' : ∀ y z, |(r.θ (k + 1) s + ((inner ℝ (r.β (k + 1) s)
        (y - r.hist (k + 1) s (sampNode ys (k + 1) s)) : ℝ) : EReal)).toReal -
        (r.θ (k + 1) s + ((inner ℝ (r.β (k + 1) s)
        (z - r.hist (k + 1) s (sampNode ys (k + 1) s)) : ℝ) : EReal)).toReal| ≤ Lr * ‖y - z‖ :=
      fun y z => (hcl y z).trans (mul_le_mul_of_nonneg_right (hβ k hk) (norm_nonneg _))
    by_cases hk' : T ≤ k + (s + 1)
    · have hf' := (claimB0 D ε hS hH2 R ys r hr (T - (s + 1)) (s + 1) (by omega) (by omega) k
        hk').1
      have := (lip_max _ _ hf' hcf Lr Lr (ihk hk') hcl').2
      simpa only [max_self] using this
    · have hb := claimA D ε hS hH2 R ys r hr k (s + 1) (by omega) (by omega)
      simp only [hb, bot_le, max_eq_right]
      exact hcl'

end main
end RASDDPLem35

open RASDDPLem35 in
theorem solution {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ)
    (hS : D.Standing) (hH2 : D.H2 ε) (R : Rules n M) (ys : ℕ → ℕ → Fin M) (r : RunData n M)
    (hr : D.IsRun R ys r) :
    let L : EReal := ((2 / ε : ℝ) : EReal) *
      ⨆ h', ⨆ (_ : 1 ≤ h' ∧ h' + 1 ≤ T),
        ((⨆ x ∈ Metric.cthickening (ε / 2) (D.prodSet h'), D.Q h' x) -
          ⨅ x ∈ D.prodSet h', r.Qm (T - h') h' x)
    ∀ h, 1 ≤ h → h + 1 ≤ T → ∀ k, T ≤ k + h →
      L ≠ ⊥ ∧ L ≠ ⊤ ∧
      ∀ x y : Hist n h, r.Qm k h x ≠ ⊥ ∧ r.Qm k h x ≠ ⊤ ∧
        |(r.Qm k h x).toReal - (r.Qm k h y).toReal| ≤ L.toReal * ‖x - y‖ := by
  intro L h h1 hh k hk
  have hε : 0 < ε := hH2.1
  set supE : ℕ → EReal := fun h' => ⨆ x ∈ Metric.cthickening (ε / 2) (D.prodSet h'), D.Q h' x
  set infE : ℕ → EReal := fun h' => ⨅ x ∈ D.prodSet h', r.Qm (T - h') h' x
  -- facts for every valid stage
  have hfacts : ∀ h', 1 ≤ h' → h' + 1 ≤ T →
      ∃ S I : ℝ, supE h' = S ∧ infE h' = I ∧ I ≤ S := by
    intro h' h1' hh'
    have hc : ∀ i, i < h' → IsCompact (D.Xc (i + 1)) := fun i hi => (hH2.2 i (by omega)).1.2.2
    have hP := prodSet_compact D h' hc
    set x0 : Hist n h' := WithLp.toLp 2 (fun i : Fin h' => (hH2.2 i.val (by omega)).1.1.some)
    have hx0 : x0 ∈ D.prodSet h' := fun i => (hH2.2 i.val (by omega)).1.1.some_mem
    obtain ⟨-, hfin, hcont⟩ := proposition_3_1 D ε hS hH2 h' h1' (by omega) (ε / 2) (by linarith)
      (by linarith)
    have hK := hP.cthickening (r := ε / 2)
    have hx0K : x0 ∈ Metric.cthickening (ε / 2) (D.prodSet h') :=
      Metric.self_subset_cthickening _ hx0
    obtain ⟨xm, hxmK, hxm⟩ := hK.exists_isMaxOn ⟨x0, hx0K⟩ hcont
    obtain ⟨hB0f, C, hB0l⟩ := claimB0 D ε hS hH2 R ys r hr (T - h') h' (by omega) h1' (T - h')
      (by omega)
    obtain ⟨xn, hxnP, hxn⟩ := hP.exists_isMinOn ⟨x0, hx0⟩ (cont_of_lip _ C hB0l).continuousOn
    have hsupv : supE h' = D.Q h' xm := by
      apply le_antisymm
      · refine iSup₂_le fun x hx => ?_
        have h1 := hxm hx
        simp only [Set.mem_setOf_eq] at h1
        rw [← EReal.coe_toReal (hfin x hx).2 (hfin x hx).1,
          ← EReal.coe_toReal (hfin xm hxmK).2 (hfin xm hxmK).1]
        exact_mod_cast h1
      · exact le_iSup₂ (f := fun x _ => D.Q h' x) xm hxmK
    have hinfv : infE h' = r.Qm (T - h') h' xn := by
      apply le_antisymm
      · exact iInf₂_le (f := fun x _ => r.Qm (T - h') h' x) xn hxnP
      · refine le_iInf₂ fun x hx => ?_
        have h1 := hxn hx
        simp only [Set.mem_setOf_eq] at h1
        rw [← EReal.coe_toReal (hB0f x).2 (hB0f x).1, ← EReal.coe_toReal (hB0f xn).2 (hB0f xn).1]
        exact_mod_cast h1
    refine ⟨(D.Q h' xm).toReal, (r.Qm (T - h') h' xn).toReal, ?_, ?_, ?_⟩
    · rw [hsupv, EReal.coe_toReal (hfin xm hxmK).2 (hfin xm hxmK).1]
    · rw [hinfv, EReal.coe_toReal (hB0f xn).2 (hB0f xn).1]
    · have hle : r.Qm (T - h') h' xn ≤ D.Q h' xm := by
        refine (valid D hS R ys r hr (T - h') h' (by omega) h1' _ xn).trans ?_
        rw [← hsupv]
        exact le_iSup₂ (f := fun x _ => D.Q h' x) xn (Metric.self_subset_cthickening _ hxnP)
      exact EReal.toReal_le_toReal hle (hB0f xn).1 (hfin xm hxmK).2
  -- the supremum defining L is finite
  set SS : EReal := ⨆ h', ⨆ (_ : 1 ≤ h' ∧ h' + 1 ≤ T), (supE h' - infE h') with hSS
  have hL : L = ((2 / ε : ℝ) : EReal) * SS := rfl
  obtain ⟨S0, I0, hS0, hI0, hSI0⟩ := hfacts h h1 hh
  have hSSlow : ((S0 - I0 : ℝ) : EReal) ≤ SS := by
    refine le_trans (le_of_eq ?_) (le_iSup₂_of_le (f := fun h' (_ : 1 ≤ h' ∧ h' + 1 ≤ T) =>
      supE h' - infE h') h ⟨h1, hh⟩ le_rfl)
    rw [hS0, hI0, EReal.coe_sub]
  set B : ℝ := ∑ h' ∈ Finset.range T, max 0 (supE h' - infE h').toReal
  have hSSup : SS ≤ (B : EReal) := by
    refine iSup₂_le fun h' hc => ?_
    obtain ⟨S, I, hSv, hIv, _⟩ := hfacts h' hc.1 hc.2
    rw [hSv, hIv, ← EReal.coe_sub]
    refine EReal.coe_le_coe_iff.2 ?_
    have h1 : S - I ≤ max 0 (supE h' - infE h').toReal := by
      rw [hSv, hIv, ← EReal.coe_sub, EReal.toReal_coe]; exact le_max_right _ _
    refine h1.trans (Finset.single_le_sum (f := fun h' => max 0 (supE h' - infE h').toReal)
      (fun _ _ => le_max_left _ _) (Finset.mem_range.2 (by omega)))
  have hSSb : SS ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hSSlow
  have hSSt : SS ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hSSup
  lift SS to ℝ using ⟨hSSt, hSSb⟩ with SSr hSSr
  have hSSr' : S0 - I0 ≤ SSr := by exact_mod_cast hSSlow
  have hLr : L = ((2 / ε * SSr : ℝ) : EReal) := by rw [hL, EReal.coe_mul]
  have hLt : L.toReal = 2 / ε * SSr := by rw [hLr, EReal.toReal_coe]
  refine ⟨by rw [hLr]; exact EReal.coe_ne_bot _, by rw [hLr]; exact EReal.coe_ne_top _, ?_⟩
  obtain ⟨s, rfl⟩ : ∃ s, h = s + 1 := ⟨h - 1, by omega⟩
  have hs : s + 2 ≤ T := by omega
  have hβ : ∀ k, T ≤ k + 1 + (s + 1) → ‖r.β (k + 1) s‖ ≤ L.toReal := by
    intro k' hk'
    have hb := beta_bound D ε hS hH2 R ys r hr s hs k' hk' S0 I0
      (fun x hx => by rw [← hS0]; exact le_iSup₂ (f := fun x _ => D.Q (s + 1) x) x hx)
      (fun x hx => by rw [← hI0]; exact iInf₂_le (f := fun x _ => r.Qm (T - (s + 1)) (s + 1) x) x hx)
    rw [hLt]
    have h2 : ‖r.β (k' + 1) s‖ = 2 / ε * (ε / 2 * ‖r.β (k' + 1) s‖) := by field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_left (hb.trans hSSr') (by positivity)
  have hL0 : 0 ≤ L.toReal := by rw [hLt]; exact mul_nonneg (by positivity) (by linarith)
  have hlip := claimB1 D ε hS hH2 R ys r hr s hs L.toReal hL0 hβ k hk
  have hfin := (claimB0 D ε hS hH2 R ys r hr (T - (s + 1)) (s + 1) (by omega) (by omega) k hk).1
  exact fun x y => ⟨(hfin x).1, (hfin x).2, hlip x y⟩
