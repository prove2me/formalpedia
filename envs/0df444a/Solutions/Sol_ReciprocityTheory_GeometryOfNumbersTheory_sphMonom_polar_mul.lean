-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_polar_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:02:09.081516+00:00
-- url     : https://prove2.me/submissions/875cb69f-60c8-4bbc-8106-4cf1572bfc12

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Metric Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (μ : Measure E) [μ.IsAddHaarMeasure] (G : E → ℂ) (φ : ℝ → ℝ) :
    ∫ x, G (‖x‖⁻¹ • x) * (φ ‖x‖ : ℂ) ∂μ =
      (∫ u : sphere (0 : E) 1, G u ∂μ.toSphere) *
        ((∫ r : Ioi (0 : ℝ), φ r ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) : ℝ) : ℂ) := by
  have hpres := (Measure.measurePreserving_homeomorphUnitSphereProd μ).integral_comp
    (Homeomorph.measurableEmbedding _)
    (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => G (p.1 : E) * ((φ p.2 : ℝ) : ℂ))
  calc ∫ x, G (‖x‖⁻¹ • x) * (φ ‖x‖ : ℂ) ∂μ
      = ∫ x in ({0}ᶜ : Set E), G (‖x‖⁻¹ • x) * (φ ‖x‖ : ℂ) ∂μ := by
        rw [restrict_compl_singleton]
    _ = ∫ x : ({0}ᶜ : Set E), G (‖(x : E)‖⁻¹ • (x : E)) * (φ ‖(x : E)‖ : ℂ)
          ∂(Measure.comap Subtype.val μ) :=
        (integral_subtype_comap (measurableSet_singleton 0).compl _).symm
    _ = ∫ p : sphere (0 : E) 1 × Ioi (0 : ℝ), G (p.1 : E) * ((φ p.2 : ℝ) : ℂ)
          ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
        refine Eq.trans (integral_congr_ae (ae_of_all _ fun x => ?_)) hpres
        simp [homeomorphUnitSphereProd]
    _ = _ := by
        rw [integral_prod_mul (fun u : sphere (0 : E) 1 => G (u : E))
          (fun r : Ioi (0 : ℝ) => ((φ r : ℝ) : ℂ)), integral_complex_ofReal]
end ReciprocityTheory.GeometryOfNumbersTheory
