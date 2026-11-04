-- Prove2me | solution 1 for RiskAverseSDDP.Convergence.eq_4_32
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:20:41.797929+00:00
-- url     : https://prove2.me/submissions/95ded810-7cfc-4cfb-8050-97073804e493
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Convergence_Run
import Theorems.Thm_RiskAverseSDDP_Convergence_proposition_3_1
import Theorems.Thm_RiskAverseSDDP_Convergence_lemma_3_5
import Theorems.Thm_GirardeauLeclerePhilpott_lemma_A_1
open Filter Topology
open RiskAverseSDDP.Convergence

namespace RASDDPEq432

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

end RASDDPEq432

open RASDDPEq432 in
theorem solution {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ) (hT : 1 ≤ T)
    (hS : D.Standing) (hH2 : D.H2 ε) (R : Rules n M) (ys : ℕ → ℕ → Fin M) (r : RunData n M)
    (hr : D.IsRun R ys r)
    (hH2t : Tendsto (fun k => D.Q 1 (r.hist k 0 Fin.elim0) - r.Qm k 1 (r.hist k 0 Fin.elim0))
      atTop (𝓝 0)) :
    Tendsto (fun k => D.Q 1 (r.hist (k + 1) 0 Fin.elim0) - r.Qm k 1 (r.hist (k + 1) 0 Fin.elim0))
      atTop (𝓝 0) := by
  rcases Nat.lt_or_ge 1 T with hT2 | hT1
  swap
  · -- T = 1: both functions vanish
    have h1 : T = 1 := by omega
    subst h1
    have hQT := hr.2.1
    simp only [Q_last, hQT, sub_zero]
    exact tendsto_const_nhds
  have hε : 0 < ε := hH2.1
  obtain ⟨hX, -, -, -, -, -⟩ := hH2.2 0 hT
  set e := Hist.empty n
  set X : Set (Hist n 1) := (fun y => e.snoc y) '' D.Xc 1 with hXdef
  have hXc : IsCompact X := hX.2.2.image (snoc_continuous e)
  have hXP : ∀ z ∈ X, z ∈ D.prodSet 1 := by
    rintro _ ⟨y, hy, rfl⟩; exact snoc_mem_prodSet D y hy
  obtain ⟨-, hfin, -⟩ := proposition_3_1 D ε hS hH2 1 le_rfl hT (ε / 2) (by linarith)
    (by linarith)
  have h35 := lemma_3_5 D ε hS hH2 R ys r hr
  extract_lets L at h35
  have hval := valid D hS R ys r hr (T - 1) 1 (by omega) le_rfl
  refine ereal_A1 X hXc (D.Q 1) (fun k => r.Qm k 1) L.toReal (T - 1)
    (fun z hz => hfin z (Metric.self_subset_cthickening _ (hXP z hz)))
    (fun k hk z _ => ⟨(h35 1 le_rfl hT2 k (by omega)).2.2 z z |>.1,
      (h35 1 le_rfl hT2 k (by omega)).2.2 z z |>.2.1⟩)
    (fun k hk z _ w _ => by
      rw [dist_eq_norm]; exact ((h35 1 le_rfl hT2 k (by omega)).2.2 z w).2.2)
    (fun k z _ => by
      obtain ⟨-, -, -, -, -, hupd⟩ := hr.2.2.2 k 0 (by omega)
      rw [hupd]; exact le_max_left _ _)
    (fun k z _ => hval k z)
    (fun k => r.hist k 0 Fin.elim0) (fun k hk => ?_) hH2t
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact ⟨_, (hr.2.2.1 k' 0 Fin.elim0 hT).2.1.1, rfl⟩
