-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.paIsPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:55:03.805823+00:00
-- url     : https://prove2.me/submissions/53f6b9cd-84a4-444c-b78d-17e8f21ce493

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropABSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaThContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_comp_smul_paT_mem_paPoly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paPoly_exists


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
theorem _root_.solution {c : ℕ} (t : ℝ) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    IsPolyLE c (fun z => F (t • paT z)) := by
  obtain ⟨p, hp, hpe⟩ := paPoly_exists (comp_smul_paT_mem_paPoly t hF)
  exact ⟨p, hp, fun z => congrFun hpe z⟩
end ReciprocityTheory.ChartRestriction.G.I2
