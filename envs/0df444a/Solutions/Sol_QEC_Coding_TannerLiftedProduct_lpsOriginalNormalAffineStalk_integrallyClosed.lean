-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalAffineStalk_integrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:55:37.286175+00:00
-- url     : https://prove2.me/submissions/d90e827b-d431-42a3-b696-ed7657430850

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.FunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (R : CommRingCat) [IsDomain R] [IsIntegrallyClosed R] (y : Spec R) :
    IsIntegrallyClosed ((Spec R).presheaf.stalk y) := by
  let : y.asIdeal.IsPrime := y.isPrime
  let : IsIntegrallyClosed (Localization.AtPrime y.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime y.asIdeal)
      y.asIdeal.primeCompl y.asIdeal.primeCompl_le_nonZeroDivisors
  exact IsIntegrallyClosed.of_equiv (Spec.stalkIso R y).symm.commRingCatIsoToRingEquiv
end QEC.Coding.TannerLiftedProduct
