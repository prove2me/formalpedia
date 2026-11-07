-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroChart_intFlat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:02:36.192485+00:00
-- url     : https://prove2.me/submissions/504f629b-55fe-48a5-a353-54475db0d65b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0 < N) :
    (Int.castRingHom (lpsOriginalIntegerNormalZeroChart N hN)).Flat := by
  let : Algebra ℤ (lpsOriginalIntegerNormalZeroChart N hN) :=
    Ring.toIntAlgebra (lpsOriginalIntegerNormalZeroChart N hN)
  rw [← algebraMap_int_eq, RingHom.flat_algebraMap_iff]
  infer_instance
end QEC.Coding.TannerLiftedProduct
