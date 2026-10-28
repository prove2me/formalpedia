-- Prove2me | solution 1 for SemilinearHJ.Verification.observation_4_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T06:09:06.753934+00:00
-- url     : https://prove2.me/submissions/f57fa522-2668-4d4c-b724-c716ac5ea7d4

import Mathlib
import Definitions.Def_SemilinearHJ_Verification_Setting

open scoped ENNReal MeasureTheory
open SemilinearHJ.Verification

namespace M31

lemma inner_eq {n : ℕ} (u v : E n) : inner ℝ u v = ∑ i, u i * v i := by
  simp [PiLp.inner_apply, mul_comm]

lemma l1_nonneg {n : ℕ} (v : E n) : 0 ≤ l1 v := Finset.sum_nonneg fun i _ => abs_nonneg _

lemma abs_le_l1 {n : ℕ} (v : E n) (i : Fin n) : |v i| ≤ l1 v :=
  Finset.single_le_sum (f := fun i => |v i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)

lemma l1_smul {n : ℕ} (c : ℝ) (v : E n) : l1 (c • v) = |c| * l1 v := by
  simp [l1, abs_mul, Finset.mul_sum]

lemma continuous_l1 {n : ℕ} : Continuous (fun v : E n => l1 v) := by
  unfold l1; fun_prop

lemma isCompact_of_poly {n : ℕ} {X : Set (E n)} (hX : IsPolytope X) : IsCompact X := by
  obtain ⟨S, -, rfl⟩ := hX
  exact S.finite_toSet.isCompact_convexHull ℝ

lemma convex_of_poly {n : ℕ} {X : Set (E n)} (hX : IsPolytope X) : Convex ℝ X := by
  obtain ⟨S, -, rfl⟩ := hX
  exact convex_convexHull ℝ _

lemma bdd_psi {n : ℕ} {X : Set (E n)} (hX : IsPolytope X) (Ψ : E n → E n)
    (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) : BddAbove ((fun x => l1 (Ψ x)) '' X) := by
  obtain ⟨K, hK⟩ := hΨL
  exact ((isCompact_of_poly hX).image_of_continuousOn
    (continuous_l1.comp_continuousOn hK.continuousOn)).bddAbove

lemma l1_le_psiNorm {n : ℕ} {X : Set (E n)} (hX : IsPolytope X) (Ψ : E n → E n)
    (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) {x : E n} (hx : x ∈ X) :
    l1 (Ψ x) ≤ psiNorm X Ψ :=
  le_csSup (bdd_psi hX Ψ hΨL) ⟨x, hx, rfl⟩

lemma psiNorm_nonneg {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) : 0 ≤ psiNorm X Ψ := by
  apply Real.sSup_nonneg
  rintro _ ⟨x, -, rfl⟩
  exact l1_nonneg _

/-- the cost integrand bound -/
lemma cost_le {n : ℕ} {X : Set (E n)} (hX : IsPolytope X) (Ψ : E n → E n)
    (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    {x : E n} (hx : x ∈ X) (v : E n) :
    ∑ i, Ψ x i * max (v i) 0 ≤ psiNorm X Ψ * l1 v := by
  calc ∑ i, Ψ x i * max (v i) 0 ≤ ∑ i, |Ψ x i| * l1 v := by
        apply Finset.sum_le_sum; intro i _
        rw [abs_of_nonneg (hΨ0 x hx i)]
        apply mul_le_mul_of_nonneg_left _ (hΨ0 x hx i)
        exact max_le ((le_abs_self _).trans (abs_le_l1 v i)) (l1_nonneg v)
    _ = l1 (Ψ x) * l1 v := by rw [l1, ← Finset.sum_mul]; rfl
    _ ≤ psiNorm X Ψ * l1 v := mul_le_mul_of_nonneg_right (l1_le_psiNorm hX Ψ hΨL hx) (l1_nonneg v)

lemma zero_mem_ballR {n : ℕ} (X : Set (E n)) {r : ℝ} (hr : 0 ≤ r) : (0 : E n) ∈ ballR X r :=
  ⟨Submodule.zero_mem _, by simp [l1, hr]⟩

lemma ham_bdd {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) {x : E n}
    (hΨ0 : ∀ i, 0 ≤ Ψ x i) (u : E n) :
    BddAbove ((fun v => inner ℝ u v - ∑ i, Ψ x i * max (v i) 0) '' ballR X r) := by
  refine ⟨l1 u * r, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  have h1 : 0 ≤ ∑ i, Ψ x i * max (v i) 0 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hΨ0 i) (le_max_right _ _)
  have h2 : inner ℝ u v ≤ l1 u * r := by
    rw [inner_eq, l1, Finset.sum_mul]
    apply Finset.sum_le_sum; intro i _
    calc u i * v i ≤ |u i| * |v i| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ |u i| * r := mul_le_mul_of_nonneg_left ((abs_le_l1 v i).trans hv.2) (abs_nonneg _)
  linarith

lemma le_ham {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) {x : E n}
    (hΨ0 : ∀ i, 0 ≤ Ψ x i) (u v : E n) (hv : v ∈ ballR X r) :
    inner ℝ u v - ∑ i, Ψ x i * max (v i) 0 ≤ ham X Ψ r x u :=
  le_csSup (ham_bdd X Ψ r hΨ0 u) ⟨v, hv, rfl⟩

lemma ham_nonneg {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) {r : ℝ} (hr : 0 ≤ r) {x : E n}
    (hΨ0 : ∀ i, 0 ≤ Ψ x i) (u : E n) : 0 ≤ ham X Ψ r x u := by
  have := le_ham X Ψ r hΨ0 u 0 (zero_mem_ballR X hr)
  simpa using this

open MeasureTheory Set

lemma pathCost_zero {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (φ : ℝ → E n) :
    pathCost X Ψ r 0 φ = 0 := by
  unfold pathCost
  rw [Icc_self]
  exact setLIntegral_measure_zero _ _ (by simp)

lemma isPath_const {n : ℕ} {X : Set (E n)} {x : E n} (hx : x ∈ X) :
    IsPath X 0 (fun _ => x) :=
  ⟨le_rfl, ⟨0, (LipschitzWith.const x).lipschitzOnWith⟩, fun _ _ => hx⟩

lemma minCost_self {n : ℕ} {X : Set (E n)} (Ψ : E n → E n) (r : ℝ) {x : E n} (hx : x ∈ X) :
    minCost X Ψ r x x = 0 := by
  rw [← nonpos_iff_eq_zero]
  unfold minCost
  refine (iInf_le _ 0).trans ((iInf_le _ (fun _ => x)).trans ((iInf_le _ ⟨isPath_const hx, rfl, rfl⟩).trans ?_))
  rw [pathCost_zero]

lemma srcVal_eq_zero {n : ℕ} {X : Set (E n)} (Ψ : E n → E n) (r : ℝ) {X0 : Set (E n)}
    (hX0X : X0 ⊆ X) {x : E n} (hx : x ∈ X0) :
    srcVal X Ψ r X0 x = 0 := by
  rw [← nonpos_iff_eq_zero]
  unfold srcVal
  refine (iInf_le _ 0).trans ((iInf_le _ (fun _ => x)).trans
    ((iInf_le _ ⟨isPath_const (hX0X hx), hx, rfl⟩).trans ?_))
  rw [pathCost_zero]

/-- concatenation of paths -/
noncomputable def cat {n : ℕ} (T1 : ℝ) (φ1 φ2 : ℝ → E n) : ℝ → E n :=
  fun t => if t ≤ T1 then φ1 t else φ2 (t - T1)

lemma cat_zero {n : ℕ} {T1 : ℝ} (hT1 : 0 ≤ T1) (φ1 φ2 : ℝ → E n) : cat T1 φ1 φ2 0 = φ1 0 := by
  simp [cat, hT1]

lemma cat_end {n : ℕ} {T1 T2 : ℝ} (hT2 : 0 ≤ T2) (φ1 φ2 : ℝ → E n) (h : φ1 T1 = φ2 0) :
    cat T1 φ1 φ2 (T1 + T2) = φ2 T2 := by
  rcases hT2.eq_or_lt with h0 | h0
  · subst h0; simp [cat, h]
  · simp [cat, h0]

lemma isPath_cat {n : ℕ} {X : Set (E n)} {T1 T2 : ℝ} {φ1 φ2 : ℝ → E n}
    (h1 : IsPath X T1 φ1) (h2 : IsPath X T2 φ2) (h : φ1 T1 = φ2 0) :
    IsPath X (T1 + T2) (cat T1 φ1 φ2) := by
  obtain ⟨hT1, ⟨K1, hK1⟩, hm1⟩ := h1
  obtain ⟨hT2, ⟨K2, hK2⟩, hm2⟩ := h2
  refine ⟨add_nonneg hT1 hT2, ⟨max K1 K2, ?_⟩, ?_⟩
  · have key : ∀ s t, 0 ≤ s → s ≤ T1 → T1 < t → t ≤ T1 + T2 →
        dist (cat T1 φ1 φ2 s) (cat T1 φ1 φ2 t) ≤ (max K1 K2 : NNReal) * dist s t := by
      intro s t hs hsT htT ht
      have e1 : cat T1 φ1 φ2 s = φ1 s := by simp [cat, hsT]
      have e2 : cat T1 φ1 φ2 t = φ2 (t - T1) := by simp [cat, not_le.mpr htT]
      rw [e1, e2]
      have d1 := hK1.dist_le_mul s ⟨hs, hsT⟩ T1 ⟨hT1, le_rfl⟩
      have d2 := hK2.dist_le_mul 0 ⟨le_rfl, hT2⟩ (t - T1) ⟨by linarith, by linarith⟩
      rw [← h] at d2
      have hk1 : (K1 : ℝ) ≤ (max K1 K2 : NNReal) := by exact_mod_cast le_max_left K1 K2
      have hk2 : (K2 : ℝ) ≤ (max K1 K2 : NNReal) := by exact_mod_cast le_max_right K1 K2
      rw [Real.dist_eq, abs_of_nonpos (by linarith)] at d1
      rw [Real.dist_eq, abs_of_nonpos (by linarith)] at d2
      rw [Real.dist_eq, abs_of_nonpos (by linarith)]
      calc dist (φ1 s) (φ2 (t - T1)) ≤ dist (φ1 s) (φ1 T1) + dist (φ1 T1) (φ2 (t - T1)) :=
            dist_triangle _ _ _
        _ ≤ K1 * -(s - T1) + K2 * -(0 - (t - T1)) := add_le_add d1 d2
        _ ≤ (max K1 K2 : NNReal) * -(s - T1) + (max K1 K2 : NNReal) * -(0 - (t - T1)) := by
            gcongr <;> linarith
        _ = _ := by ring
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    have hk1 : (K1 : ℝ) ≤ (max K1 K2 : NNReal) := by exact_mod_cast le_max_left K1 K2
    have hk2 : (K2 : ℝ) ≤ (max K1 K2 : NNReal) := by exact_mod_cast le_max_right K1 K2
    by_cases hsT : s ≤ T1 <;> by_cases htT : t ≤ T1
    · have e1 : cat T1 φ1 φ2 s = φ1 s := by simp [cat, hsT]
      have e2 : cat T1 φ1 φ2 t = φ1 t := by simp [cat, htT]
      rw [e1, e2]
      exact (hK1.dist_le_mul s ⟨hs.1, hsT⟩ t ⟨ht.1, htT⟩).trans
        (mul_le_mul_of_nonneg_right hk1 dist_nonneg)
    · exact key s t hs.1 hsT (not_le.mp htT) ht.2
    · rw [dist_comm, dist_comm s]; exact key t s ht.1 htT (not_le.mp hsT) hs.2
    · have e1 : cat T1 φ1 φ2 s = φ2 (s - T1) := by simp [cat, hsT]
      have e2 : cat T1 φ1 φ2 t = φ2 (t - T1) := by simp [cat, htT]
      rw [e1, e2]
      have := hK2.dist_le_mul (s - T1) ⟨by linarith [not_le.mp hsT], by linarith [hs.2]⟩
        (t - T1) ⟨by linarith [not_le.mp htT], by linarith [ht.2]⟩
      rw [dist_sub_right] at this
      exact this.trans (mul_le_mul_of_nonneg_right hk2 dist_nonneg)
  · intro t ht
    by_cases htT : t ≤ T1
    · simp only [cat, htT, if_true]; exact hm1 ⟨ht.1, htT⟩
    · simp only [cat, htT, if_false]
      exact hm2 ⟨by linarith [not_le.mp htT], by linarith [ht.2]⟩

lemma pathCost_Ioo {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r T : ℝ) (φ : ℝ → E n) :
    pathCost X Ψ r T φ = ∫⁻ t in Ioo 0 T, runCost X Ψ r (φ t) (deriv φ t) := by
  unfold pathCost
  rw [setLIntegral_congr (Ioo_ae_eq_Icc (μ := volume)).symm]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

lemma pathCost_cat_le {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) {T1 T2 : ℝ}
    (hT1 : 0 ≤ T1) (φ1 φ2 : ℝ → E n) :
    pathCost X Ψ r (T1 + T2) (cat T1 φ1 φ2) ≤ pathCost X Ψ r T1 φ1 + pathCost X Ψ r T2 φ2 := by
  set F : ℝ → ℝ≥0∞ := fun t => runCost X Ψ r (cat T1 φ1 φ2 t) (deriv (cat T1 φ1 φ2) t)
  have hsub : Ioo 0 (T1 + T2) ⊆ Ioo 0 T1 ∪ Icc T1 (T1 + T2) := by
    intro t ht
    by_cases h : t < T1
    · exact Or.inl ⟨ht.1, h⟩
    · exact Or.inr ⟨not_lt.mp h, ht.2.le⟩
  rw [pathCost_Ioo, pathCost_Ioo, pathCost_Ioo]
  calc ∫⁻ t in Ioo 0 (T1 + T2), F t ≤ ∫⁻ t in Ioo 0 T1 ∪ Icc T1 (T1 + T2), F t :=
        lintegral_mono_set hsub
    _ ≤ (∫⁻ t in Ioo 0 T1, F t) + ∫⁻ t in Icc T1 (T1 + T2), F t := lintegral_union_le _ _ _
    _ = _ := by
      congr 1
      · apply setLIntegral_congr_fun measurableSet_Ioo
        intro t ht
        have hev : cat T1 φ1 φ2 =ᶠ[nhds t] φ1 := by
          filter_upwards [Iio_mem_nhds ht.2] with s hs
          simp [cat, (show s ≤ T1 from le_of_lt hs)]
        simp only [F, hev.deriv_eq, hev.eq_of_nhds]
      · rw [setLIntegral_congr (Ioo_ae_eq_Icc (μ := volume)).symm]
        have : ∀ t ∈ Ioo T1 (T1 + T2), F t =
            (Ioo 0 T2).indicator (fun s => runCost X Ψ r (φ2 s) (deriv φ2 s)) (t - T1) := by
          intro t ht
          have hev : cat T1 φ1 φ2 =ᶠ[nhds t] (fun s => φ2 (s - T1)) := by
            filter_upwards [Ioi_mem_nhds ht.1] with s hs
            simp [cat, not_le.mpr (show T1 < s from hs)]
          rw [indicator_of_mem (show t - T1 ∈ Ioo 0 T2 from ⟨by linarith [ht.1], by linarith [ht.2]⟩)]
          simp only [F, hev.deriv_eq, hev.eq_of_nhds, deriv_comp_sub_const]
        rw [setLIntegral_congr_fun measurableSet_Ioo this]
        rw [← lintegral_indicator measurableSet_Ioo]
        have : (Ioo T1 (T1 + T2)).indicator (fun t => (Ioo 0 T2).indicator
            (fun s => runCost X Ψ r (φ2 s) (deriv φ2 s)) (t - T1)) =
            fun t => (Ioo 0 T2).indicator (fun s => runCost X Ψ r (φ2 s) (deriv φ2 s)) (t - T1) := by
          funext t
          by_cases ht : t ∈ Ioo T1 (T1 + T2)
          · rw [indicator_of_mem ht]
          · rw [indicator_of_notMem ht, indicator_of_notMem]
            intro h; apply ht; exact ⟨by linarith [h.1], by linarith [h.2]⟩
        rw [this, lintegral_sub_right_eq_self
          ((Ioo 0 T2).indicator (fun s => runCost X Ψ r (φ2 s) (deriv φ2 s))) T1,
          lintegral_indicator measurableSet_Ioo]

lemma srcVal_le_add {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (X0 : Set (E n)) (x y : E n) :
    srcVal X Ψ r X0 x ≤ srcVal X Ψ r X0 y + minCost X Ψ r y x := by
  unfold srcVal minCost
  simp only [ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf fun T2 => le_iInf fun φ2 => le_iInf fun h2 => le_iInf fun T1 =>
    le_iInf fun φ1 => le_iInf fun h1 => ?_
  refine (iInf_le _ (T1 + T2)).trans ((iInf_le _ (cat T1 φ1 φ2)).trans ((iInf_le _
    ⟨isPath_cat h1.1 h2.1 (h1.2.2.trans h2.2.1.symm), ?_, ?_⟩).trans
    (pathCost_cat_le X Ψ r h1.1.1 φ1 φ2)))
  · rw [cat_zero h1.1.1]; exact h1.2.1
  · rw [cat_end h2.1.1 _ _ (h1.2.2.trans h2.2.1.symm)]; exact h2.2.2

end M31

open M31

theorem solution {n : ℕ} (X : Set (E n)) (hX : IsPolytope X)
    (Ψ : E n → E n) (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    (r : ℝ) (hr : 0 < r)
    (X0 : Set (E n)) (hX0c : IsCompact X0) (hX0X : X0 ⊆ X) :
    ∀ x ∈ X, ∀ ρ : ℝ, 0 < ρ →
      (∃ y ∈ X, l1 (y - x) ≤ ρ ∧ srcVal X Ψ r X0 x = srcVal X Ψ r X0 y + minCost X Ψ r y x) ∧
      ∀ y ∈ X, l1 (y - x) ≤ ρ → srcVal X Ψ r X0 x ≤ srcVal X Ψ r X0 y + minCost X Ψ r y x := by
  intro x hx ρ hρ
  refine ⟨⟨x, hx, by simp [l1, hρ.le], by rw [minCost_self Ψ r hx, add_zero]⟩, ?_⟩
  intro y _ _
  exact srcVal_le_add X Ψ r X0 x y

