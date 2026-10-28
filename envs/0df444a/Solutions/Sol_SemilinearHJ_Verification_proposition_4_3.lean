-- Prove2me | solution 1 for SemilinearHJ.Verification.proposition_4_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T06:14:53.746511+00:00
-- url     : https://prove2.me/submissions/a3f59bc7-f4f2-49f3-836f-ef5f271e85ba

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


lemma l1_eq_zero {n : ℕ} {v : E n} (h : l1 v = 0) : v = 0 := by
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg (v i))).mp h
  ext i; simpa using this i (Finset.mem_univ i)

lemma l1_le_norm {n : ℕ} (v : E n) : l1 v ≤ n * ‖v‖ := by
  calc l1 v ≤ ∑ _i : Fin n, ‖v‖ := Finset.sum_le_sum fun i _ => by
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v i
    _ = n * ‖v‖ := by simp

/-- straight-line path estimate -/
lemma minCost_line {n : ℕ} {X : Set (E n)} (hX : IsPolytope X) (Ψ : E n → E n) (r : ℝ)
    {x y : E n} (hx : x ∈ X) (hy : y ∈ X) {T : ℝ} (hT : 0 < T) (hw : l1 (T⁻¹ • (x - y)) ≤ r)
    (B : ℝ) (hB : ∀ t ∈ Ioo 0 T, y + t • (T⁻¹ • (x - y)) ∈ X →
      ∑ i, Ψ (y + t • (T⁻¹ • (x - y))) i * max ((T⁻¹ • (x - y)) i) 0 ≤ B) :
    minCost X Ψ r y x ≤ ENNReal.ofReal B * ENNReal.ofReal T := by
  set w : E n := T⁻¹ • (x - y) with hwdef
  set φ : ℝ → E n := fun t => y + t • w with hφ
  have hmem : ∀ t ∈ Icc 0 T, φ t ∈ X := by
    intro t ht
    have : φ t = y + (t / T) • (x - y) := by
      simp only [hφ, hwdef, smul_smul, div_eq_mul_inv]
    rw [this]
    exact (convex_of_poly hX).add_smul_sub_mem hy hx
      ⟨div_nonneg ht.1 hT.le, (div_le_one hT).mpr ht.2⟩
  have hpath : IsPath X T φ := by
    refine ⟨hT.le, ⟨‖w‖₊, ?_⟩, hmem⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro s _ t _
    simp only [hφ, dist_eq_norm, coe_nnnorm]
    rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs, mul_comm]
  have hφT : φ T = x := by
    simp only [hφ, hwdef, smul_smul, mul_inv_cancel₀ hT.ne', one_smul, add_sub_cancel]
  have hder : ∀ t, deriv φ t = w := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s • w) w t := by
      simpa using (hasDerivAt_id t).smul_const w
    exact (h1.const_add y).deriv
  unfold minCost
  refine (iInf_le _ T).trans ((iInf_le _ φ).trans ((iInf_le _ ⟨hpath, by simp [hφ], hφT⟩).trans ?_))
  rw [pathCost_Ioo]
  calc ∫⁻ t in Ioo 0 T, runCost X Ψ r (φ t) (deriv φ t)
      ≤ ∫⁻ _t in Ioo 0 T, ENNReal.ofReal B := by
        apply setLIntegral_mono measurable_const
        intro t ht
        rw [hder]
        have htc : w ∈ tanCone X (φ t) := by
          refine ⟨x, hx, (T - t)⁻¹, inv_nonneg.mpr (by linarith [ht.2]), ?_⟩
          have hTw : T • w = x - y := by
            rw [hwdef, smul_smul, mul_inv_cancel₀ hT.ne', one_smul]
          have : x - φ t = (T - t) • w := by
            rw [sub_smul, hTw]; simp only [hφ]; abel
          rw [this, smul_smul, inv_mul_cancel₀ (by linarith [ht.2]), one_smul]
        have hb : w ∈ ballR X r :=
          ⟨Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ hx hy), hw⟩
        unfold runCost
        rw [if_pos ⟨htc, hb⟩]
        exact ENNReal.ofReal_le_ofReal (hB t ht (hmem t ⟨ht.1.le, ht.2.le⟩))
    _ = ENNReal.ofReal B * ENNReal.ofReal T := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_zero]

lemma minCost_le_lip {n : ℕ} {X : Set (E n)} (hX : IsPolytope X) (Ψ : E n → E n)
    (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    {r : ℝ} (hr : 0 < r) {x y : E n} (hx : x ∈ X) (hy : y ∈ X) :
    minCost X Ψ r y x ≤ ENNReal.ofReal (psiNorm X Ψ * l1 (x - y)) := by
  rcases (l1_nonneg (x - y)).eq_or_lt with h0 | hpos
  · have : x = y := sub_eq_zero.mp (l1_eq_zero h0.symm)
    subst this
    rw [minCost_self Ψ r hx]; exact bot_le
  · have hT : 0 < l1 (x - y) / r := div_pos hpos hr
    have hl : l1 ((l1 (x - y) / r)⁻¹ • (x - y)) = r := by
      rw [l1_smul, abs_of_pos (inv_pos.mpr hT)]; field_simp
    refine (minCost_line hX Ψ r hx hy hT hl.le (psiNorm X Ψ * r) ?_).trans ?_
    · intro t _ htX
      have := cost_le hX Ψ hΨL hΨ0 htX ((l1 (x - y) / r)⁻¹ • (x - y))
      rwa [hl] at this
    · rw [← ENNReal.ofReal_mul (mul_nonneg (psiNorm_nonneg X Ψ) hr.le)]
      apply le_of_eq; congr 1; field_simp

lemma srcVal_ne_top {n : ℕ} {X : Set (E n)} (hX : IsPolytope X) (Ψ : E n → E n)
    (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    {r : ℝ} (hr : 0 < r) {X0 : Set (E n)} (hX0X : X0 ⊆ X) (hX0 : X0.Nonempty)
    {x : E n} (hx : x ∈ X) : srcVal X Ψ r X0 x ≠ ⊤ := by
  obtain ⟨x0, hx0⟩ := hX0
  apply ne_top_of_le_ne_top _ (srcVal_le_add X Ψ r X0 x x0)
  rw [srcVal_eq_zero Ψ r hX0X hx0, zero_add]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (minCost_le_lip hX Ψ hΨL hΨ0 hr hx (hX0X hx0))

lemma toReal_le_add {a b : ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c) (hb : b ≠ ⊤)
    (h : a ≤ b + ENNReal.ofReal c) : a.toReal ≤ b.toReal + c := by
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hb, ENNReal.ofReal_ne_top⟩) h
  rwa [ENNReal.toReal_add hb ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hc] at this

lemma srcVal_real_le {n : ℕ} {X : Set (E n)} (hX : IsPolytope X) (Ψ : E n → E n)
    (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    {r : ℝ} (hr : 0 < r) {X0 : Set (E n)} (hX0X : X0 ⊆ X) (hX0 : X0.Nonempty)
    {x y : E n} (hx : x ∈ X) (hy : y ∈ X) :
    (srcVal X Ψ r X0 x).toReal ≤ (srcVal X Ψ r X0 y).toReal + psiNorm X Ψ * l1 (x - y) :=
  toReal_le_add (mul_nonneg (psiNorm_nonneg X Ψ) (l1_nonneg _))
    (srcVal_ne_top hX Ψ hΨL hΨ0 hr hX0X hX0 hy)
    ((srcVal_le_add X Ψ r X0 x y).trans (add_le_add le_rfl (minCost_le_lip hX Ψ hΨL hΨ0 hr hx hy)))

lemma srcVal_lip {n : ℕ} {X : Set (E n)} (hX : IsPolytope X) (Ψ : E n → E n)
    (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    {r : ℝ} (hr : 0 < r) {X0 : Set (E n)} (hX0X : X0 ⊆ X) (hX0 : X0.Nonempty) :
    LipschitzOnWith (Real.toNNReal (psiNorm X Ψ * n)) (fun x => (srcVal X Ψ r X0 x).toReal) X := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have h1 := srcVal_real_le hX Ψ hΨL hΨ0 hr hX0X hX0 hx hy
  have h2 := srcVal_real_le hX Ψ hΨL hΨ0 hr hX0X hX0 hy hx
  have hP := psiNorm_nonneg X Ψ
  have e1 : psiNorm X Ψ * l1 (x - y) ≤ psiNorm X Ψ * n * dist x y := by
    rw [mul_assoc, dist_eq_norm]; exact mul_le_mul_of_nonneg_left (l1_le_norm _) hP
  have e2 : psiNorm X Ψ * l1 (y - x) ≤ psiNorm X Ψ * n * dist x y := by
    rw [mul_assoc, dist_comm, dist_eq_norm]; exact mul_le_mul_of_nonneg_left (l1_le_norm _) hP
  rw [Real.coe_toNNReal _ (mul_nonneg hP (Nat.cast_nonneg n)), Real.dist_eq, abs_le]
  constructor <;> linarith

lemma interior_line {n : ℕ} {X : Set (E n)} {x0 v : E n} (hx0 : x0 ∈ intrinsicInterior ℝ X)
    (hv : v ∈ vectorSpan ℝ X) : ∃ δ > 0, ∀ h : ℝ, |h| < δ → x0 - h • v ∈ X := by
  obtain ⟨y, hyint, hyx⟩ := mem_intrinsicInterior.mp hx0
  have hmem : ∀ h : ℝ, x0 - h • v ∈ affineSpan ℝ X := by
    intro h
    have : x0 - h • v = (-h) • v +ᵥ x0 := by simp [vadd_eq_add, sub_eq_neg_add, neg_smul]
    rw [this]
    apply AffineSubspace.vadd_mem_of_mem_direction
    · rw [direction_affineSpan]; exact Submodule.smul_mem _ _ hv
    · rw [← hyx]; exact y.2
  let c : ℝ → affineSpan ℝ X := fun h => ⟨x0 - h • v, hmem h⟩
  have hc : Continuous c := by
    apply Continuous.subtype_mk; fun_prop
  have hc0 : c 0 = y := by
    apply Subtype.ext; simp [c, hyx]
  have : c ⁻¹' interior (Subtype.val ⁻¹' X) ∈ nhds (0 : ℝ) := by
    apply hc.continuousAt.preimage_mem_nhds
    rw [hc0]; exact isOpen_interior.mem_nhds hyint
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp this
  refine ⟨δ, hδ, fun h hh => ?_⟩
  have := interior_subset (hball (show h ∈ Metric.ball 0 δ by simpa using hh))
  exact this

end M31

open M31
open MeasureTheory Set

theorem solution {n : ℕ} (X : Set (E n)) (hX : IsPolytope X)
    (Ψ : E n → E n) (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    (r : ℝ) (hr : 0 < r)
    (X0 : Set (E n)) (hX0c : IsCompact X0) (hX0X : X0 ⊆ X) (hX0 : X0.Nonempty) :
    (∀ x ∈ X, srcVal X Ψ r X0 x ≠ ⊤) ∧
      IsViscSub X Ψ r X0 (fun x => (srcVal X Ψ r X0 x).toReal) := by
  refine ⟨fun x hx => srcVal_ne_top hX Ψ hΨL hΨ0 hr hX0X hX0 hx,
    (srcVal_lip hX Ψ hΨL hΨ0 hr hX0X hX0).continuousOn,
    fun x hx => by simp [srcVal_eq_zero Ψ r hX0X hx], ?_⟩
  intro ϕ hϕ x0 hx0 hmax
  have hx0X : x0 ∈ X := intrinsicInterior_subset hx0.1
  set V : E n → ℝ := fun x => (srcVal X Ψ r X0 x).toReal with hV
  apply csSup_le ((Set.nonempty_of_mem (zero_mem_ballR X hr.le)).image _)
  rintro _ ⟨v, hv, rfl⟩
  simp only
  rw [gradient, InnerProductSpace.toDual_symm_apply]
  set S := ∑ i, Ψ x0 i * max (v i) 0 with hS
  set D := fderiv ℝ ϕ x0 v with hD
  suffices ∀ ε > 0, D ≤ S + ε by
    by_contra hcon
    have := this ((D - S) / 2) (by linarith)
    linarith
  intro ε hε
  obtain ⟨δ1, hδ1, hline⟩ := interior_line hx0.1 hv.1
  -- continuity of the cost density
  have hFc : ContinuousWithinAt (fun p => ∑ i, Ψ p i * max (v i) 0) X x0 := by
    obtain ⟨K, hK⟩ := hΨL
    have : ContinuousOn (fun p => ∑ i, Ψ p i * max (v i) 0) X := by
      apply continuousOn_finsetSum; intro i _
      exact (((PiLp.continuous_apply 2 _ i).comp_continuousOn hK.continuousOn)).mul
        continuousOn_const
    exact this x0 hx0X
  obtain ⟨δ2, hδ2, hF⟩ := Metric.continuousWithinAt_iff.mp hFc ε hε
  obtain ⟨δ3, hδ3, hloc⟩ := Metric.mem_nhdsWithin_iff.mp hmax
  -- the one-dimensional function
  set g : ℝ → ℝ := fun h => ϕ (x0 - h • v) with hg
  have hgd : HasDerivAt g (fderiv ℝ ϕ x0 (-v)) 0 := by
    have hl : HasDerivAt (fun h : ℝ => x0 - h • v) (-v) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_sub x0
    have hf : HasFDerivAt ϕ (fderiv ℝ ϕ x0) x0 :=
      ((hϕ.differentiable (by simp)) x0).hasFDerivAt
    exact hf.comp_hasDerivAt_of_eq (0:ℝ) hl (by simp)
  have hslope := (hasDerivAt_iff_tendsto_slope.mp hgd).mono_left
    (nhdsWithin_mono (0:ℝ) (fun h (hh : h ∈ Ioi (0:ℝ)) => ne_of_gt hh))
  have hδ : 0 < min δ1 (min (δ2 / (‖v‖ + 1)) (δ3 / (‖v‖ + 1))) := by
    have : 0 < ‖v‖ + 1 := by positivity
    exact lt_min hδ1 (lt_min (div_pos hδ2 this) (div_pos hδ3 this))
  have hev : ∀ᶠ h in nhdsWithin (0:ℝ) (Ioi 0), -(S + ε) ≤ slope g 0 h := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with h hh
    have hnv : 0 < ‖v‖ + 1 := by positivity
    have hh1 : h < δ1 := lt_of_lt_of_le hh.2 (min_le_left _ _)
    have hh2 : h * ‖v‖ < δ2 := by
      have : h < δ2 / (‖v‖ + 1) := lt_of_lt_of_le hh.2 ((min_le_right _ _).trans (min_le_left _ _))
      rw [lt_div_iff₀ hnv] at this; nlinarith [norm_nonneg v, hh.1]
    have hh3 : h * ‖v‖ < δ3 := by
      have : h < δ3 / (‖v‖ + 1) := lt_of_lt_of_le hh.2 ((min_le_right _ _).trans (min_le_right _ _))
      rw [lt_div_iff₀ hnv] at this; nlinarith [norm_nonneg v, hh.1]
    set y := x0 - h • v with hy
    have hyX : y ∈ X := hline h (by rw [abs_of_pos hh.1]; exact hh1)
    have hw : h⁻¹ • (x0 - y) = v := by
      rw [hy, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hh.1.ne', one_smul]
    have hcost : minCost X Ψ r y x0 ≤ ENNReal.ofReal (S + ε) * ENNReal.ofReal h := by
      apply minCost_line hX Ψ r hx0X hyX hh.1 (by rw [hw]; exact hv.2)
      intro t ht htX
      rw [hw] at htX ⊢
      have hdist : dist (y + t • v) x0 < δ2 := by
        rw [hy, dist_eq_norm, show x0 - h • v + t • v - x0 = (t - h) • v by
          rw [sub_smul]; abel, norm_smul, Real.norm_eq_abs, abs_of_neg (by linarith [ht.2])]
        nlinarith [norm_nonneg v, ht.1, ht.2]
      have := hF htX hdist
      rw [Real.dist_eq] at this
      linarith [(abs_lt.mp this).2]
    have hSε : 0 ≤ S + ε := by
      have : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (hΨ0 x0 hx0X i) (le_max_right _ _)
      linarith
    rw [← ENNReal.ofReal_mul hSε] at hcost
    have hVle : V x0 ≤ V y + (S + ε) * h :=
      toReal_le_add (mul_nonneg hSε hh.1.le) (srcVal_ne_top hX Ψ hΨL hΨ0 hr hX0X hX0 hyX)
        ((srcVal_le_add X Ψ r X0 x0 y).trans (add_le_add le_rfl hcost))
    have hlocy : V y - ϕ y ≤ V x0 - ϕ x0 := by
      have hyb : y ∈ Metric.ball x0 δ3 := by
        rw [Metric.mem_ball, hy, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
          Real.norm_eq_abs, abs_of_pos hh.1]
        exact hh3
      exact hloc ⟨hyb, hyX⟩
    have hg0 : g 0 = ϕ x0 := by simp [hg]
    rw [slope_def_field, hg0, sub_zero, le_div_iff₀ hh.1]
    simp only [hg]
    change -(S + ε) * h ≤ ϕ y - ϕ x0
    linarith
  have := ge_of_tendsto hslope hev
  rw [map_neg] at this
  linarith

