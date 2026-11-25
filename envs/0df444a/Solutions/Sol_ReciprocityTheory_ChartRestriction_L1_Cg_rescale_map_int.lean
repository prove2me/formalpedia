-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.Cg.rescale_map_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:01:20.915646+00:00
-- url     : https://prove2.me/submissions/d9a89652-9b2e-49d2-b5b7-e84c3435359f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_map_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rescale_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
namespace Cg
theorem _root_.solution {p : ℕ} (hp : 0 < p) (b : ℕ) (F : PowerSeries ℤ) :
    Cg p (PowerSeries.rescale (zetaC p ^ b) (F.map (Int.castRingHom ℂ))) (F.map (Int.castRingHom ℂ)) := ⟨CoeffIn.map_int _ F, rescale_congr hp b F⟩
end Cg
end ReciprocityTheory.ChartRestriction.L1
