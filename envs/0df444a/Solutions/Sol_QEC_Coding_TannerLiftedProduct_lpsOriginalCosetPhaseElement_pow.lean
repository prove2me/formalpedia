-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCosetPhaseElement_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:15:55.989329+00:00
-- url     : https://prove2.me/submissions/e8d103ae-29c8-4342-b016-da730b01d348

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.KummerExtension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue

set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0 < N) (x : LPSOriginalCuspIndex N) :
    (lpsOriginalCosetPhaseElement N hN x)^N = 1 := by
  apply Subtype.ext
  exact lpsOriginalCosetCuspData_phase_pow N hN x
end QEC.Coding.TannerLiftedProduct
