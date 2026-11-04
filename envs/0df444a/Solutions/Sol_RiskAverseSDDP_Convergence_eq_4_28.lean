-- Prove2me | solution 1 for RiskAverseSDDP.Convergence.eq_4_28
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:22:48.336311+00:00
-- url     : https://prove2.me/submissions/f3c8a721-3376-4fb3-9220-ec04de37e8d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Convergence_Run
import Theorems.Thm_RiskAverseSDDP_Convergence_proposition_3_1
import Theorems.Thm_RiskAverseSDDP_Convergence_lemma_3_5
import Theorems.Thm_RiskAverseSDDP_Convergence_eq_4_26
import Theorems.Thm_GirardeauLeclerePhilpott_lemma_A_1
open Filter Topology
open RiskAverseSDDP.Convergence

namespace RASDDPEq428

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

lemma snoc_mem_prodSet {T n M q p s : ℕ} (D : Model T n M q p) {x : Hist n s}
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
    exact snoc_mem_prodSet D (fun i => Fin.elim0 i) h.1
  | succ s ih =>
    intro hs ν
    have h := (hr.2.2.1 k (s + 1) ν hs).2.1
    exact snoc_mem_prodSet D (ih (by omega) (Fin.init ν)) h.1

lemma ereal_A1 {E : Type*} [PseudoMetricSpace E] (X : Set E) (hX : IsCompact X)
    (f : E → EReal) (F : ℕ → E → EReal) (L : ℝ) (k0 : ℕ)
    (hf : ∀ x ∈ X, f x ≠ ⊥ ∧ f x ≠ ⊤) (hF : ∀ k, k0 ≤ k → ∀ x ∈ X, F k x ≠ ⊥ ∧ F k x ≠ ⊤)
    (hL : ∀ k, k0 ≤ k → ∀ x ∈ X, ∀ y ∈ X, |(F k x).toReal - (F k y).toReal| ≤ L * dist x y)
    (hmono : ∀ k, ∀ x ∈ X, F k x ≤ F (k + 1) x) (hle : ∀ k, ∀ x ∈ X, F k x ≤ f x)
    (x : ℕ → E) (hx : ∀ k, k0 ≤ k → x k ∈ X)
    (h : Tendsto (fun k => f (x k) - F k (x k)) atTop (𝓝 0)) :
    Tendsto (fun k => f (x (k + 1)) - F k (x (k + 1))) atTop (𝓝 0) := by
  have hx' : ∀ k, x (k + k0) ∈ X := fun k => hx _ (by omega)
  have hFk : ∀ k, ∀ y ∈ X, F (k + k0) y ≠ ⊥ ∧ F (k + k0) y ≠ ⊤ := fun k => hF _ (by omega)
  have hreal : ∀ k, f (x (k + k0)) - F (k + k0) (x (k + k0)) =
      (((f (x (k + k0))).toReal - (F (k + k0) (x (k + k0))).toReal : ℝ) : EReal) := by
    intro k
    rw [EReal.coe_sub, EReal.coe_toReal (hf _ (hx' k)).2 (hf _ (hx' k)).1,
      EReal.coe_toReal (hFk k _ (hx' k)).2 (hFk k _ (hx' k)).1]
  have h0 : Tendsto (fun k => (f (x (k + k0))).toReal - (F (k + k0) (x (k + k0))).toReal)
      atTop (𝓝 0) := by
    have h1 := (EReal.tendsto_toReal (a := 0) (by simp) (by simp)).comp
      (h.comp (tendsto_add_atTop_nat k0))
    refine (h1.congr fun k => ?_)
    simp only [Function.comp, hreal, EReal.toReal_coe]
  have hA := GirardeauLeclerePhilpott.lemma_A_1 X hX (fun y => (f y).toReal)
    (fun k y => (F (k + k0) y).toReal) L
    (fun k y hy z hz => hL _ (by omega) y hy z hz)
    (fun k y hy => by
      have := hmono (k + k0) y hy
      rw [show k + 1 + k0 = k + k0 + 1 by omega]
      exact EReal.toReal_le_toReal this (hFk k y hy).1 (hF _ (by omega) y hy).2)
    (fun k y hy => EReal.toReal_le_toReal (hle _ y hy) (hFk k y hy).1 (hf y hy).2)
    (fun k => x (k + k0)) hx' h0
  rw [← tendsto_add_atTop_iff_nat k0]
  have hc := (continuous_coe_real_ereal.tendsto 0).comp hA
  simp only [EReal.coe_zero] at hc
  refine hc.congr fun k => ?_
  have e1 : k + 1 + k0 = k + k0 + 1 := by omega
  simp only [Function.comp, e1]
  have hxk : x (k + k0 + 1) ∈ X := hx _ (by omega)
  rw [EReal.coe_sub, EReal.coe_toReal (hf _ hxk).2 (hf _ hxk).1,
    EReal.coe_toReal (hFk k _ hxk).2 (hFk k _ hxk).1]

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

lemma tendsto_sum_zero {M : ℕ} (G : Fin M → ℕ → EReal)
    (h : ∀ j, Tendsto (G j) atTop (𝓝 0)) :
    Tendsto (fun k => ∑ j, G j k) atTop (𝓝 0) := by
  induction (Finset.univ : Finset (Fin M)) using Finset.induction_on with
  | empty => simp
  | insert b t hb ih =>
    simp only [Finset.sum_insert hb]
    have hc := (EReal.continuousAt_add_coe_coe 0 0).tendsto.comp ((h b).prodMk_nhds ih)
    simp only [EReal.coe_zero, add_zero] at hc
    exact hc

end RASDDPEq428

open RASDDPEq428 in
theorem solution {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ)
    (hS : D.Standing) (hH2 : D.H2 ε) (R : Rules n M) (ys : ℕ → ℕ → Fin M) (r : RunData n M)
    (hr : D.IsRun R ys r) (s : ℕ) (hs : s + 2 ≤ T) (ν : Fin s → Fin M)
    (h427 : ∀ j : Fin M, Tendsto (fun k =>
      D.Q (s + 2) (r.hist k (s + 1) (Fin.snoc (α := fun _ => Fin M) ν j)) -
        r.Qm k (s + 2) (r.hist k (s + 1) (Fin.snoc (α := fun _ => Fin M) ν j))) atTop (𝓝 0)) :
    Tendsto (fun k => D.Q (s + 1) (r.hist k s ν) - r.Qm k (s + 1) (r.hist k s ν))
      (atTop ⊓ 𝓟 (iterSet ys s ν)) (𝓝 0) := by
  have hε : 0 < ε := hH2.1
  set G : Fin M → ℕ → EReal := fun j k =>
    D.Q (s + 2) (r.hist (k + 1) (s + 1) (Fin.snoc (α := fun _ => Fin M) ν j)) -
      r.Qm k (s + 2) (r.hist (k + 1) (s + 1) (Fin.snoc (α := fun _ => Fin M) ν j)) with hGdef
  have hval2 := valid D hS R ys r hr (T - (s + 2)) (s + 2) (by omega) (by omega)
  have hfin2 := (proposition_3_1 D ε hS hH2 (s + 2) (by omega) hs (ε / 2) (by linarith)
      (by linarith)).2.1
  have hmemP : ∀ k (ν' : Fin (s + 1) → Fin M), r.hist (k + 1) (s + 1) ν' ∈ D.prodSet (s + 2) :=
    fun k ν' => hist_mem D R ys r hr k (s + 1) (by omega) ν'
  have hGnn : ∀ j k, 0 ≤ G j k := by
    intro j k
    have hq := hfin2 _ (Metric.self_subset_cthickening _
      (hmemP k (Fin.snoc (α := fun _ => Fin M) ν j)))
    exact (EReal.sub_nonneg (Or.inl hq.2) (Or.inl hq.1)).2 (hval2 k _)
  -- (4.27) transferred to the previous approximation by Lemma A.1
  have hG : ∀ j, Tendsto (G j) atTop (𝓝 0) := by
    intro j
    rcases Nat.lt_or_ge (s + 2) T with hlt | hge
    · have hc : ∀ i, i < s + 2 → IsCompact (D.Xc (i + 1)) := fun i hi =>
        (hH2.2 i (by omega)).1.2.2
      have h35 := lemma_3_5 D ε hS hH2 R ys r hr
      extract_lets L at h35
      refine ereal_A1 (D.prodSet (s + 2)) (prodSet_compact D _ hc) (D.Q (s + 2))
        (fun k => r.Qm k (s + 2)) L.toReal (T - (s + 2))
        (fun z hz => hfin2 z (Metric.self_subset_cthickening _ hz))
        (fun k hk z _ => ⟨(h35 (s + 2) (by omega) (by omega) k (by omega)).2.2 z z |>.1,
          (h35 (s + 2) (by omega) (by omega) k (by omega)).2.2 z z |>.2.1⟩)
        (fun k hk z _ w _ => by
          rw [dist_eq_norm]; exact ((h35 (s + 2) (by omega) (by omega) k (by omega)).2.2 z w).2.2)
        (fun k z _ => by
          obtain ⟨-, -, -, -, -, hupd⟩ := hr.2.2.2 k (s + 1) (by omega)
          rw [hupd]; exact le_max_left _ _)
        (fun k z _ => hval2 k z)
        (fun k => r.hist k (s + 1) (Fin.snoc (α := fun _ => Fin M) ν j)) (fun k hk => ?_) (h427 j)
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact hmemP k' _
    · have hT : s + 2 = T := by omega
      have hz : ∀ k, G j k = 0 := by
        intro k
        simp only [hGdef]
        subst hT
        rw [Q_last, hr.2.1 k]
        simp
      rw [show G j = fun _ => 0 from funext hz]
      exact tendsto_const_nhds
  -- bound of the risk measure by the sum of the gaps
  have hrho : ∀ k, D.rho (s + 2) (fun j => G j k) ≤ ∑ j, G j k := by
    intro k
    unfold Model.rho
    refine iSup₂_le fun π hπ => ?_
    have hS' := hS (s + 2) (by omega) hs
    have hd := hS'.2.2.1 hπ
    have hw : ∀ j, 0 ≤ π j * D.Φ (s + 2) j := fun j => mul_nonneg (hd.1 j) (hS'.1 j).le
    have hw1 : ∀ j, π j * D.Φ (s + 2) j ≤ 1 := by
      intro j
      rw [← hd.2]
      exact Finset.single_le_sum (f := fun i => π i * D.Φ (s + 2) i) (fun i _ => hw i)
        (Finset.mem_univ j)
    refine Finset.sum_le_sum fun j _ => ?_
    calc ((π j * D.Φ (s + 2) j : ℝ) : EReal) * G j k ≤ 1 * G j k :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hw1 j) (hGnn j k)
      _ = G j k := one_mul _
  have hB : Tendsto (fun k => ∑ j, G j (k - 1)) atTop (𝓝 0) :=
    (tendsto_sum_zero G hG).comp (tendsto_sub_atTop_nat 1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds.mono_left inf_le_left)
    (hB.mono_left inf_le_left) ?_ ?_
  · filter_upwards [mem_inf_of_right (Filter.mem_principal_self (iterSet ys s ν))] with k hk
    obtain ⟨hk1, hks⟩ := hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact (eq_4_26 D ε hS hH2 R ys r hr s hs ν k' hks).1
  · filter_upwards [mem_inf_of_right (Filter.mem_principal_self (iterSet ys s ν))] with k hk
    obtain ⟨hk1, hks⟩ := hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    refine (eq_4_26 D ε hS hH2 R ys r hr s hs ν k' hks).2.trans ?_
    simpa using hrho k'
