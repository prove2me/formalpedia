-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Holtb.aesm_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:42.687064+00:00
-- url     : https://prove2.me/submissions/4a189bbe-e993-489c-b675-838af9b5f2a7

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_HolomorphicTheta_IntHol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric Set
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Holtb
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
namespace PositivityTheory.SiegelWeilFormula.Holtb
theorem _root_.solution (f : X → E → ℂ) (W₀ : E) (r : ℝ) (hr : 0 < r)
    (hd : ∀ x, DifferentiableAt ℂ (f x) W₀)
    (hm : ∀ W ∈ ball W₀ r, AEStronglyMeasurable (f · W) ν) :
    AEStronglyMeasurable (fun x => fderiv ℂ (f x) W₀) ν := by
  classical
  let b := Module.finBasis ℂ E
  let L : Fin (Module.finrank ℂ E) → E →L[ℂ] ℂ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  have hrep : ∀ x, fderiv ℂ (f x) W₀ = ∑ i, fderiv ℂ (f x) W₀ (b i) • L i := by
    intro x
    ext v
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul, L, LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have hfun : (fun x => fderiv ℂ (f x) W₀) = fun x => ∑ i, fderiv ℂ (f x) W₀ (b i) • L i := funext hrep
  rw [hfun]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  refine AEStronglyMeasurable.smul_const ?_ (L i)
  set v := b i
  set ε : ℝ := r / (2 * (‖v‖ + 1)) with hε_def
  have hε : 0 < ε := by positivity
  set t : ℕ → ℂ := fun k => ((ε * (1 / ((k : ℝ) + 1)) : ℝ) : ℂ) with ht_def
  have ht0 : Tendsto t atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => ?_⟩
    · have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ε)
      rw [mul_zero] at h
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h
      simpa [ht_def, Function.comp_def] using h2
    · simp only [ht_def, Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
      positivity
  have htn : ∀ k, ‖t k‖ ≤ ε := by
    intro k
    simp only [ht_def, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    have : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith
  have htmem : ∀ k, W₀ + t k • v ∈ ball W₀ r := by
    intro k
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    have h1 : ε * (‖v‖ + 1) = r / 2 := by rw [hε_def]; field_simp
    have h2 : ‖t k‖ * ‖v‖ ≤ ε * (‖v‖ + 1) := by
      calc ‖t k‖ * ‖v‖ ≤ ε * ‖v‖ := by gcongr; exact htn k
        _ ≤ ε * (‖v‖ + 1) := by nlinarith
    linarith
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun k x => (t k)⁻¹ • (f x (W₀ + t k • v) - f x W₀)) (fun k => ?_) (ae_of_all _ fun x => ?_)
  · exact (((hm _ (htmem k)).sub (hm _ (mem_ball_self hr))).const_smul ((t k)⁻¹)).congr (ae_of_all _ fun x => rfl)
  · have hl : HasDerivAt (fun s : ℂ => W₀ + s • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add W₀
    have h1 : HasDerivAt (fun s : ℂ => f x (W₀ + s • v)) (fderiv ℂ (f x) W₀ v) 0 :=
      (hd x).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hl (by simp)
    have h2 := h1.tendsto_slope_zero.comp ht0
    simpa [Function.comp_def] using h2
end PositivityTheory.SiegelWeilFormula.Holtb
