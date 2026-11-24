-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.spH_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:35.115976+00:00
-- url     : https://prove2.me/submissions/8a7d6c39-3a53-4549-9e35-557f7d6b2da9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SpGenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spGens_subset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution (g : ℕ) : spH g ≤ symplecticGroup (Fin g) ℤ := Submonoid.closure_le.mpr (spGens_subset g)
end ReciprocityTheory.ChartRestriction.G.Key.Chi
