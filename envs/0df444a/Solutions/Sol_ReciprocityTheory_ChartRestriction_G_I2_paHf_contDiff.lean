-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.paHf_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:12:08.805424+00:00
-- url     : https://prove2.me/submissions/5a85e135-e34d-460e-9e24-60379d12980d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropABSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaThContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (a : EuclideanSpace ℂ ι) :
    ContDiff ℂ (⊤ : ℕ∞) (fun v : EuclideanSpace ℂ ι => Hf v a) := by
  show ContDiff ℂ (⊤ : ℕ∞) (fun v : EuclideanSpace ℂ ι => ∑ i, v i * (starRingEnd ℂ) (a i))
  exact ContDiff.sum fun i _ =>
    (EuclideanSpace.proj i : EuclideanSpace ℂ ι →L[ℂ] ℂ).contDiff.mul contDiff_const
end ReciprocityTheory.ChartRestriction.G.I2
