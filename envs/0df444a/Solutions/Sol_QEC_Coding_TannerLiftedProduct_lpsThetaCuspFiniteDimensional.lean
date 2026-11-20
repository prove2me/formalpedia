-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaCuspFiniteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:35:43.193173+00:00
-- url     : https://prove2.me/submissions/ede9b44c-1fe2-45ff-b334-c4b0b35b2feb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFiniteDimension

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) (a : LPSResiduePrime p) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 ((4*a.q)^2) :
      Subgroup (GL (Fin 2) ℝ)) 2) := by
  have hn : NeZero ((4*a.q)^2) := ⟨pow_ne_zero _ (mul_ne_zero (by norm_num) a.prime.ne_zero)⟩
  exact lpsGamma0CuspFiniteDimensional ((4*a.q)^2) 2
end QEC.Coding.TannerLiftedProduct
