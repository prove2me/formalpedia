-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.piTop_T3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:48:09.529066+00:00
-- url     : https://prove2.me/submissions/ca5390a1-06ac-43a0-a21f-24fbebc66837

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_laurentPoly_T3

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : @T3Space R piTop :=
  @instT3SpaceForall (Unit →₀ ℕ) (fun _ => LaurentPolynomial ℤ)
    (fun _ => (⊥ : UniformSpace (LaurentPolynomial ℤ)).toTopologicalSpace) (fun _ => laurentPoly_T3)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
