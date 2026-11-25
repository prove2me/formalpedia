-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.length_eq_of_surj_of_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:24.084806+00:00
-- url     : https://prove2.me/submissions/79a69e3e-8df9-46db-b728-7edc516d9577

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqOfSurjOfKerEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
universe u
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {A C M N : Type*} [CommRing A] [AddCommGroup C] [Module A C]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (f : C →ₗ[A] M) (g : C →ₗ[A] N)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : LinearMap.ker f = LinearMap.ker g) : Module.length A M = Module.length A N := ((f.quotKerEquivOfSurjective hf).symm.trans ((Submodule.quotEquivOfEq _ _ h).trans
      (g.quotKerEquivOfSurjective hg))).length_eq
end ReciprocityTheory.ChartRestriction.G.AI
