-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.dens_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:29.2444+00:00
-- url     : https://prove2.me/submissions/b18b14a0-d4f7-40cd-813f-725be0d9d217

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_CardAddB
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_cardAddB
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_nexpB
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_contIpB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution (hA : AlgA) (hI : IntG) (hD : DerivF) (hM : MollId) (hG : Gauss) (hCG : ClsGain)
    (hInt : Integr) : Dens := by
  intro m n ε c t hc ht P N hN
  obtain ⟨hTr, hHq, hHinv, hDet, hQc⟩ := hA m n ε
  have ht0 : t ≠ 0 := by
    rcases ht with rfl | rfl
    · exact hc.ne'
    · exact neg_ne_zero.mpr hc.ne'
  have hIt : (Complex.I * (t : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht0)
  have hsec : ∀ (Q : PX m n) (y : E n), secN ε c t Q (herm y) = FP ε c t Q y := by
    intro Q y
    simp only [secN, FP, hTr]
  obtain ⟨P', hP'⟩ : ∃ P' : PX m n, P' = (MvPolynomial.C ((Complex.I * (t : ℂ)) ^ n) * detQ ε) ^ N * P := ⟨_, rfl⟩
  have hev : ∀ x : Fin m → Fin n → ℂ, evX P' x = ((Complex.I * (t : ℂ)) ^ n * (gramX ε x).det) ^ N * evX P x := by
    intro x
    rw [← hDet x, hP']
    simp only [evX, map_mul, map_pow, MvPolynomial.eval_C]
  have hDP' : Delta^[N] (FP ε c t P) = FP ε c t P' := by
    rw [hP']
    exact (hD m n ε c t hc P N).2
  have hFP'c : Continuous (FP ε c t P') := (hD m n ε c t hc P' N).1
  obtain ⟨R, hR⟩ := hG m n ε c t hc ht P
  have hpq := cardAddB ε
  generalize hp : (Finset.univ.filter fun i => ε i = true).card = p at hR hpq
  generalize hq : (Finset.univ.filter fun i => ε i = false).card = q at hR hpq
  have hs : ((t / c : ℝ) : ℂ) = 1 ∨ ((t / c : ℝ) : ℂ) = -1 := by
    rcases ht with rfl | rfl
    · left
      rw [div_self hc.ne']
      simp
    · right
      rw [neg_div, div_self hc.ne']
      simp
  obtain ⟨J, a, G, hGc, ⟨C, hC⟩, hGeq⟩ := hCG n _ hs p q N R
  have hFPcls : FP ε c t P = cls ((t / c : ℝ) : ℂ) 0 p q R := by
    funext y
    rw [← hsec]
    exact hR y
  have hFP'eq : ∀ y, FP ε c t P' y = ∑ j : Fin J, Polynomial.eval 0 (a j) * G j y := by
    intro y
    rw [← hDP', hFPcls, hGeq]
    simp
  have hbd : ∀ y, ‖FP ε c t P' y‖ ≤ (∑ j : Fin J, ‖Polynomial.eval 0 (a j)‖) * (C * dP y ^ (-((p + q + N : ℕ) : ℝ) / 2)) := by
    intro y
    rw [hFP'eq y, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC j y) (norm_nonneg _)
  have hσ : (n : ℝ) ^ 2 / 2 < ((p + q + N : ℕ) : ℝ) / 2 := by
    have h1 : ((n : ℝ)) ^ 2 < ((m + N : ℕ) : ℝ) := by exact_mod_cast hN
    rw [hpq]
    linarith
  have hFP'int : Integrable (FP ε c t P') volume := by
    refine Integrable.mono' (((hInt n).2 _ hσ).const_mul ((∑ j : Fin J, ‖Polynomial.eval 0 (a j)‖) * C)) hFP'c.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    calc ‖FP ε c t P' y‖ ≤ (∑ j : Fin J, ‖Polynomial.eval 0 (a j)‖) * (C * dP y ^ (-((p + q + N : ℕ) : ℝ) / 2)) := hbd y
      _ = (∑ j : Fin J, ‖Polynomial.eval 0 (a j)‖) * C * dP y ^ (-(((p + q + N : ℕ) : ℝ) / 2)) := by
        rw [neg_div]
        ring
  have hipc : ∀ β y : E n, ip β y = ip y β := by
    intro β y
    simp only [ip]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hcy : ∀ β : E n, Continuous fun y : E n => ip β y := fun β => (contIpB β).congr (fun y => hipc y β)
  have hhc : Continuous fun β : E n => herm β := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [herm]
    fun_prop
  have hdc : Continuous fun β : E n => (herm β).det := hhc.matrix_det
  have hDc : Continuous fun β : E n => ((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N := (continuous_const.mul hdc).pow N
  have hF : Continuous fun β : E n => ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ))) := by
    refine continuous_of_dominated (bound := fun y => ‖FP ε c t P' y‖) (fun β => ?_) (fun β => Filter.Eventually.of_forall fun y => ?_) hFP'int.norm (Filter.Eventually.of_forall fun y => ?_)
    · exact hFP'c.aestronglyMeasurable.mul (Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp (hcy β))).neg)).aestronglyMeasurable
    · rw [norm_mul, nexpB, mul_one]
    · exact continuous_const.mul (Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp (contIpB y))).neg))
  obtain ⟨g, hg⟩ : ∃ g : E n → ℂ, g = fun β => (((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N)⁻¹ * ((((|t| / (2 * Real.pi)) ^ n ^ 2 : ℝ) : ℂ) * ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ)))) := ⟨_, rfl⟩
  have hgU : ContinuousOn g {y : E n | (herm y).det ≠ 0} := by
    rw [hg]
    refine ContinuousOn.mul ?_ (continuous_const.mul hF).continuousOn
    exact hDc.continuousOn.inv₀ (fun β hβ => pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hIt) hβ))
  have hgm : Measurable g := by
    rw [hg]
    exact hDc.measurable.inv.mul (continuous_const.mul hF).measurable
  have hcan : ∀ u v w D : ℂ, D ≠ 0 → u * (v * w) = u * D⁻¹ * (D * v * w) := by
    intro u v w D hD
    rw [show u * D⁻¹ * (D * v * w) = u * (D⁻¹ * D) * (v * w) by ring, inv_mul_cancel₀ hD, mul_one]
  have hA' : ∀ φ : E n → ℂ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ {y : E n | (herm y).det ≠ 0} →
      ∫ x, φ (qX ε x) * (evX P x * gs c x) = ∫ β, φ β * g β := by
    intro φ hφc hφs hφU
    have hψc : Continuous (fun β : E n => φ β * (((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N)⁻¹) := by
      apply continuous_of_tsupport
      intro β hβ
      have hβU : (herm β).det ≠ 0 := hφU (tsupport_mul_subset_left hβ)
      exact hφc.continuousAt.mul (hDc.continuousAt.inv₀ (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hIt) hβU)))
    have hψs : HasCompactSupport (fun β : E n => φ β * (((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N)⁻¹) := hφs.mul_right
    have key2 : (∫ x, (φ (qX ε x) * (((Complex.I * (t : ℂ)) ^ n * (herm (qX ε x)).det) ^ N)⁻¹) * (evX P' x * gs c x)) = ∫ β, (φ β * (((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N)⁻¹) * ((((|t| / (2 * Real.pi)) ^ n ^ 2 : ℝ) : ℂ) * ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ)))) :=
      hM n (Fin m → Fin n → ℂ) volume (fun x => evX P' x * gs c x) (qX ε) (hI m n c hc P') hQc.measurable t ht0 hFP'int _ hψc hψs
    calc (∫ x, φ (qX ε x) * (evX P x * gs c x)) = ∫ x, (φ (qX ε x) * (((Complex.I * (t : ℂ)) ^ n * (herm (qX ε x)).det) ^ N)⁻¹) * (evX P' x * gs c x) := by
          congr 1
          funext x
          rw [hev x]
          by_cases h0 : φ (qX ε x) = 0
          · simp [h0]
          · have hne : (herm (qX ε x)).det ≠ 0 := hφU (subset_tsupport _ (Function.mem_support.mpr h0))
            rw [hHq x] at hne
            rw [hHq x]
            exact hcan _ _ _ _ (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hIt) hne))
      _ = _ := key2
      _ = ∫ β, φ β * g β := by
          congr 1
          funext β
          rw [hg]
          ring
  refine ⟨g, hgU, ?_, ?_⟩
  · intro S hS hSU
    have hpre : gramX ε ⁻¹' (herm '' S) = qX ε ⁻¹' S := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hyq : y = qX ε x := by
          calc y = hinv (herm y) := (hHinv y).symm
            _ = hinv (herm (qX ε x)) := by rw [hyx, hHq]
            _ = qX ε x := hHinv _
        rw [← hyq]
        exact hy
      · intro hx
        exact ⟨qX ε x, hx, hHq x⟩
    rw [hpre]
    have hUo : IsOpen {y : E n | (herm y).det ≠ 0} := isOpen_ne_fun hdc continuous_const
    obtain ⟨δ, hδ, hδU⟩ := hS.exists_cthickening_subset_open hUo hSU
    have hK : IsCompact (Metric.cthickening δ S) := hS.cthickening
    have hδk : ∀ k : ℕ, 0 < δ / ((k : ℝ) + 1) := fun k => div_pos hδ (Nat.cast_add_one_pos k)
    have hδt : Tendsto (fun k : ℕ => δ / ((k : ℝ) + 1)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ)
    have hle : ∀ k : ℕ, δ / ((k : ℝ) + 1) ≤ δ := fun k => div_le_self hδ.le (le_add_of_nonneg_left (Nat.cast_nonneg k))
    obtain ⟨φk, hφk⟩ : ∃ φk : ℕ → E n → ℂ, φk = fun k β => (((thickenedIndicator (hδk k) S β : NNReal) : ℝ) : ℂ) := ⟨_, rfl⟩
    have hφkc : ∀ k, Continuous (φk k) := by
      intro k
      rw [hφk]
      exact Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (thickenedIndicator (hδk k) S).continuous)
    have hφk0 : ∀ k β, β ∉ Metric.cthickening δ S → φk k β = 0 := by
      intro k β hβ
      rw [hφk]
      simp only
      rw [thickenedIndicator_zero (hδk k) S (fun h => hβ (Metric.cthickening_mono (hle k) S (Metric.thickening_subset_cthickening _ _ h)))]
      simp
    have hφk1 : ∀ k β, ‖φk k β‖ ≤ 1 := by
      intro k β
      rw [hφk]
      simp only
      rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
      exact_mod_cast thickenedIndicator_le_one (hδk k) S β
    have hφks : ∀ k, HasCompactSupport (φk k) := fun k => HasCompactSupport.intro hK (hφk0 k)
    have hφkU : ∀ k, tsupport (φk k) ⊆ {y : E n | (herm y).det ≠ 0} := fun k =>
      (closure_minimal (Function.support_subset_iff'.2 (hφk0 k)) hK.isClosed).trans hδU
    have hlim : ∀ β : E n, Tendsto (fun k : ℕ => φk k β) atTop (𝓝 (S.indicator (fun _ => (1 : ℂ)) β)) := by
      intro β
      have h1 := tendsto_pi_nhds.1 (thickenedIndicator_tendsto_indicator_closure hδk hδt S) β
      rw [hS.isClosed.closure_eq] at h1
      have h2 := ((Complex.continuous_ofReal.comp NNReal.continuous_coe).tendsto _).comp h1
      rw [hφk]
      by_cases hβ : β ∈ S
      · simpa [hβ, Function.comp_def] using h2
      · simpa [hβ, Function.comp_def] using h2
    have hLt : Tendsto (fun k => ∫ x, φk k (qX ε x) * (evX P x * gs c x)) atTop (𝓝 (∫ x, S.indicator (fun _ => (1 : ℂ)) (qX ε x) * (evX P x * gs c x))) := by
      refine tendsto_integral_of_dominated_convergence (fun x => ‖evX P x * gs c x‖) (fun k => ?_) (hI m n c hc P).norm (fun k => Filter.Eventually.of_forall fun x => ?_) (Filter.Eventually.of_forall fun x => ?_)
      · exact ((hφkc k).comp hQc).aestronglyMeasurable.mul (hI m n c hc P).aestronglyMeasurable
      · rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hφk1 k _)
      · exact (hlim (qX ε x)).mul_const _
    have hgK : IntegrableOn g (Metric.cthickening δ S) volume := (hgU.mono hδU).integrableOn_compact hK
    have hRt : Tendsto (fun k => ∫ β, φk k β * g β) atTop (𝓝 (∫ β, S.indicator (fun _ => (1 : ℂ)) β * g β)) := by
      refine tendsto_integral_of_dominated_convergence ((Metric.cthickening δ S).indicator fun β => ‖g β‖) (fun k => ?_) (IntegrableOn.integrable_indicator hgK.norm hK.measurableSet) (fun k => Filter.Eventually.of_forall fun β => ?_) (Filter.Eventually.of_forall fun β => (hlim β).mul_const _)
      · exact (hφkc k).aestronglyMeasurable.mul hgm.aestronglyMeasurable
      · by_cases hβ : β ∈ Metric.cthickening δ S
        · rw [Set.indicator_of_mem hβ, norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (hφk1 k _)
        · simp [hβ, hφk0 k β hβ]
    have heq := tendsto_nhds_unique hLt (Filter.Tendsto.congr (fun k => (hA' (φk k) (hφkc k) (hφks k) (hφkU k)).symm) hRt)
    rw [← integral_indicator (hQc.measurable hS.isClosed.measurableSet), ← integral_indicator hS.isClosed.measurableSet]
    have e1 : ∀ x, (qX ε ⁻¹' S).indicator (fun x => evX P x * gs c x) x = S.indicator (fun _ => (1 : ℂ)) (qX ε x) * (evX P x * gs c x) := by
      intro x
      by_cases h : qX ε x ∈ S <;> simp [h]
    have e2 : ∀ β, S.indicator g β = S.indicator (fun _ => (1 : ℂ)) β * g β := by
      intro β
      by_cases h : β ∈ S <;> simp [h]
    simp only [e1, e2]
    exact heq
  · intro β _
    have hint : (∫ y : E n, Delta^[N] (fun y : E n => secN ε c t P (herm y)) y * chr t β y) = ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ))) := by
      have hfun : (fun y : E n => secN ε c t P (herm y)) = FP ε c t P := funext (hsec P)
      rw [hfun, hDP']
      rfl
    rw [hint, hg]
    have h1 : ((-1 : ℂ) ^ n / (-(Complex.I * (t : ℂ))) ^ n) = ((Complex.I * (t : ℂ)) ^ n)⁻¹ := by
      rw [neg_pow (Complex.I * (t : ℂ)), div_mul_eq_div_div, div_self (pow_ne_zero _ (by norm_num)), one_div]
    rw [h1]
    have hab : (((2 * Real.pi / |t|) ^ n ^ 2 : ℝ) : ℂ) * (((|t| / (2 * Real.pi)) ^ n ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← mul_pow, div_mul_div_comm, mul_comm (2 * Real.pi) |t|, div_self (mul_ne_zero (abs_ne_zero.mpr ht0) (by positivity)), one_pow, Complex.ofReal_one]
    linear_combination (((herm β).det ^ N)⁻¹ * (((Complex.I * (t : ℂ)) ^ n)⁻¹) ^ N * ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ)))) * hab
end PositivityTheory.Rg.Sw.WR.D
