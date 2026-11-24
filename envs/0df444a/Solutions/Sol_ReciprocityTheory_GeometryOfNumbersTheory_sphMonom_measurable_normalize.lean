-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_measurable_normalize
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:35.46038+00:00
-- url     : https://prove2.me/submissions/8be90de3-ed1f-4f8b-b15a-c7cdb42ca3bd

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_continuous_sqN

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
theorem _root_.solution :
    Measurable (fun z : Fin N → ℂ => (((Real.sqrt (sqN z))⁻¹ : ℝ) : ℂ) • z) :=
  (Complex.measurable_ofReal.comp (sphMonom_continuous_sqN.measurable.sqrt.inv)).smul measurable_id
end ReciprocityTheory.GeometryOfNumbersTheory
