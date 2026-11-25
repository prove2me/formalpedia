-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.pa_cd_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:12:19.882165+00:00
-- url     : https://prove2.me/submissions/0e1fec9a-89d2-4fe6-9b39-d261939e4136

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropABSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaThContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paMono_contDiff

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
theorem _root_.solution (s : Finset (ι →₀ ℕ)) (f : (ι →₀ ℕ) → ℂ) :
    ContDiff ℂ (⊤ : ℕ∞) (∑ β ∈ s, f β • paMono (ι := ι) β) := by
  have h := ContDiff.sum (𝕜 := ℂ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (s := s)
    (f := fun β v => f β * paMono (ι := ι) β v) fun β _ => contDiff_const.mul (paMono_contDiff β)
  convert h using 1
  ext v
  simp [Finset.sum_apply]
end ReciprocityTheory.ChartRestriction.G.I2
