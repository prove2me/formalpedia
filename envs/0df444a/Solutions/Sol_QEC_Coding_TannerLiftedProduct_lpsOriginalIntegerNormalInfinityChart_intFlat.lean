-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalInfinityChart_intFlat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:02:43.872245+00:00
-- url     : https://prove2.me/submissions/e862fa8f-696a-4ebd-b4e0-90aa29f62085

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
    (Int.castRingHom (lpsOriginalIntegerNormalInfinityChart N hN)).Flat := by
  let : Algebra ℤ (lpsOriginalIntegerNormalInfinityChart N hN) :=
    Ring.toIntAlgebra (lpsOriginalIntegerNormalInfinityChart N hN)
  rw [← algebraMap_int_eq, RingHom.flat_algebraMap_iff]
  infer_instance
end QEC.Coding.TannerLiftedProduct
