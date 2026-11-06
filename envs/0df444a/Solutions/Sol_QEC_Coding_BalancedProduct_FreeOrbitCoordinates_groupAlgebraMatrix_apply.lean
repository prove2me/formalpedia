-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.FreeOrbitCoordinates.groupAlgebraMatrix_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:46:10.120412+00:00
-- url     : https://prove2.me/submissions/11808a8d-3c97-40a9-af94-cb5fc0d0f9ee

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.FreeOrbitCoordinates
universe u v
variable (G : Type u) (X : Type v) [Group G] [MulAction G X]
variable {F : Type*} [Semiring F]
variable {R : Type*} {C : Type*}
variable [MulAction G R] [MulAction G C]
variable [IsCancelSMul G R] [IsCancelSMul G C]
variable [Fintype G]
namespace QEC.Coding.BalancedProduct.FreeOrbitCoordinates
theorem _root_.solution
    (P : Matrix R C F) (ro : OrbitIndex G R) (co : OrbitIndex G C) (h : G) :
    (groupAlgebraMatrix G P ro co).coeff h =
      P (h • orbitRep G R ro) (orbitRep G C co) := rfl
end QEC.Coding.BalancedProduct.FreeOrbitCoordinates
