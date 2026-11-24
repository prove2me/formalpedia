-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.freeQuot_exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:49.935414+00:00
-- url     : https://prove2.me/submissions/79ae14d8-063c-4d05-9c75-760a1b774eb5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotSt
import Definitions.Def_Lemmata_MiscLemmasJ_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FreeQuotPf
import Theorems.Thm_Bl_SecondBlockLemmaK_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Module
variable {R F X : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup X] [Module F X] [Module R X] [IsScalarTower R F X]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution (S : Submodule R X) {x : X}
    (hx : x ∈ Submodule.span F (S : Set X)) : ∃ d : R, d ≠ 0 ∧ d • x ∈ S := by
  exact Bl.SecondBlockLemmaK.goal1 S hx
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
