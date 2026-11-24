-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.fderiv_sq_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:31.4748+00:00
-- url     : https://prove2.me/submissions/f39ce226-23e4-4836-bb5b-edd47742d2d2

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix Filter Topology
open scoped ComplexOrder
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} (g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (hg : DifferentiableAt ℝ g z) :
    fderiv ℝ (fun y => g y ^ 2 / 2) z = g z • fderiv ℝ g z := by
  have he : (fun y => g y ^ 2 / 2) = fun y => (1 / 2 : ℝ) * (g y * g y) := by funext y; ring
  rw [he, HasFDerivAt.fderiv (f := fun y => (1 / 2 : ℝ) * (g y * g y))
    ((hg.hasFDerivAt.mul hg.hasFDerivAt).const_mul (1 / 2 : ℝ))]
  ext u
  simp
  ring
end ReciprocityTheory.AnForm.A
