-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.length_eq_sub_add_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:27:32.291863+00:00
-- url     : https://prove2.me/submissions/00240f0c-2c53-4226-a3e7-b302c2fb7f15

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {A : Type*} [Ring A] {M : Type*} [AddCommGroup M] [Module A M]
    (P : Submodule A M) : length A M = length A P + length A (M ⧸ P) :=
  Module.length_eq_add_of_exact P.subtype P.mkQ (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ P)
end ReciprocityTheory.ChartRestriction.G.AI
