-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_integral_sphProb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:59.029796+00:00
-- url     : https://prove2.me/submissions/cfe58db8-69e7-4c35-ba55-20a9a516d1cd

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_continuous_sqN
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_measurable_normalize

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
variable {N : ℕ}
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (g : (Fin N → ℂ) → ℂ) (hg : Continuous g) :
    ∫ z, g z ∂(sphProb N) =
      ((Real.pi ^ N)⁻¹ : ℂ) * ∫ z, g ((Real.sqrt (sqN z))⁻¹ • z) * (Real.exp (-sqN z) : ℂ) := by
  have hm := sphMonom_measurable_normalize (N := N)
  have hmeas : Measurable fun z : Fin N → ℂ => ENNReal.ofReal ((Real.pi ^ N)⁻¹ * Real.exp (-sqN z)) :=
    Measurable.ennreal_ofReal (measurable_const.mul
      (Real.measurable_exp.comp (sphMonom_continuous_sqN.measurable.neg)))
  rw [sphProb, integral_map hm.aemeasurable hg.aestronglyMeasurable, gaussC,
    integral_withDensity_eq_integral_toReal_smul hmeas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    ← integral_const_mul]
  congr 1
  funext z
  have hsm : (((Real.sqrt (sqN z))⁻¹ : ℝ) : ℂ) • z = (Real.sqrt (sqN z))⁻¹ • z := by
    funext i
    simp [Complex.real_smul]
  rw [ENNReal.toReal_ofReal (by positivity), hsm, Complex.real_smul]
  push_cast
  ring
end ReciprocityTheory.GeometryOfNumbersTheory
