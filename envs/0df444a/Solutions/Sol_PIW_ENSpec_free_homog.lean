-- Prove2me | solution 1 for PIW.ENSpec.free_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:21:23.309364+00:00
-- url     : https://prove2.me/submissions/e1ac5612-9e1f-40f4-90a5-547b41de939c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StSpecOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_WregOfSubsingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open PIW PIW.ENSpec
open MvPolynomial RingTheory.Sequence
open scoped Pointwise
variable {R : Type u} [CommRing R] {D : ℕ}
local notation "𝔛" => Ideal.span (Set.range (MvPolynomial.X : Fin D → MvPolynomial (Fin D) R))
namespace PIW.ENSpec
theorem _root_.solution (a : ℕ) : Module.Free R (homogeneousSubmodule (Fin D) R a) :=
  Module.Free.of_equiv
    ((LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported (Fin D) R a)).trans
      (((AddMonoidAlgebra.coeffLinearEquiv R).ofSubmodule' _).trans
        (Finsupp.supportedEquivFinsupp _))).symm
end PIW.ENSpec
