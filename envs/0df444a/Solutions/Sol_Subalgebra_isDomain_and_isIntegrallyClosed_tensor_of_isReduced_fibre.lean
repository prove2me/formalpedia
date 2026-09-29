-- Prove2me | solution 1 for Subalgebra.isDomain_and_isIntegrallyClosed_tensor_of_isReduced_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/835d7fc4-a2ce-547b-aff1-0aed205cf488

import Mathlib
import Theorems.Thm_Algebra_TensorProduct_isDomain_and_isIntegrallyClosed_of_isReduced_fibre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subalgebra_isDomain_and_isIntegrallyClosed_tensor_of_isReduced_fibre

open scoped TensorProduct

universe u

theorem solution
    {R F R' K' k' : Type u} [CommRing R] [Field F] [Algebra R F] (A : Subalgebra R F)
    [Module.Flat R A]
    [CommRing R'] [Algebra R R'] (ϖ : R') (hϖ : ϖ ∈ nonZeroDivisors R')
    [CommRing K'] [Algebra R' K'] [IsLocalization.Away ϖ K'] [Algebra R K'] [IsScalarTower R R' K']
    [IsDomain (K' ⊗[R] A)] [IsIntegrallyClosed (K' ⊗[R] A)]
    [CommRing k'] [Algebra R' k'] [Algebra R k'] [IsScalarTower R R' k']
    (hk : Function.Surjective (algebraMap R' k')) (hker : RingHom.ker (algebraMap R' k') = Ideal.span {ϖ})
    (hred : IsReduced (k' ⊗[R] A)) :
    IsDomain (R' ⊗[R] A) ∧ IsIntegrallyClosed (R' ⊗[R] A) :=
  Algebra.TensorProduct.isDomain_and_isIntegrallyClosed_of_isReduced_fibre (K' := K') ϖ hϖ hk hker hred

end S_Subalgebra_isDomain_and_isIntegrallyClosed_tensor_of_isReduced_fibre
end P2MW
export P2MW.S_Subalgebra_isDomain_and_isIntegrallyClosed_tensor_of_isReduced_fibre (solution)
