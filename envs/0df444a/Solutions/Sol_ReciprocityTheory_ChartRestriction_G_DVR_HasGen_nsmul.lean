-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.HasGen.nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:46:54.7637+00:00
-- url     : https://prove2.me/submissions/2c75864a-0d37-49a5-9696-5ad14089dfb7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_add

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
theorem _root_.solution {F : (Y ⟶ X) →₀ ℤ} (hF : HasGen L F) : ∀ n : ℕ, HasGen L (n • F)
  | 0 => by rw [zero_smul]; exact HasGen.zero
  | n + 1 => by rw [add_smul, one_smul]; exact (solution hF n).add hF
end HasGen
end ReciprocityTheory.ChartRestriction.G.DVR
