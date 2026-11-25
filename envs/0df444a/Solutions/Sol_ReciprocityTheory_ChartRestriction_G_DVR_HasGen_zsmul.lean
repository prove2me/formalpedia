-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.HasGen.zsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:54:00.833737+00:00
-- url     : https://prove2.me/submissions/81e1087f-180c-4458-bb68-1984a8934963

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_nsmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} (L : LB X)
variable {L}
namespace ReciprocityTheory.ChartRestriction.G.DVR
namespace HasGen
theorem _root_.solution {F : (Y ⟶ X) →₀ ℤ} (hF : HasGen L F) : ∀ n : ℤ, HasGen L (n • F)
  | (n : ℕ) => by rw [natCast_zsmul]; exact hF.nsmul n
  | Int.negSucc n => by rw [negSucc_zsmul]; exact (hF.nsmul (n + 1)).neg
end HasGen
end ReciprocityTheory.ChartRestriction.G.DVR
