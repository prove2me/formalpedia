-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.FreeOrbitCoordinates.sum_rightRegularMatrix_groupAlgebraMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:52:54.999899+00:00
-- url     : https://prove2.me/submissions/bd434e99-28c6-41bb-8dfe-e8a0a995ab8b

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates
import Theorems.Thm_QEC_Coding_BalancedProduct_FreeOrbitCoordinates_rightRegularMatrix_groupAlgebraMatrix

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
    [Fintype C] [Fintype (OrbitIndex G C)]
    (P : Matrix R C F)
    (hP : ∀ (g : G) (r : R) (c : C), P (g • r) (g • c) = P r c)
    (z : C → F)
    (ro : OrbitIndex G R) (go : G) :
    (∑ co : OrbitIndex G C, ∑ gi : G,
      QEC.Coding.LiftedProduct.rightRegularMatrix
          (groupAlgebraMatrix G P ro co) go gi *
        z ((freeOrbitEquiv G C).symm (co, gi))) =
      ∑ c : C,
        P ((freeOrbitEquiv G R).symm (ro, go)) c * z c := by
  calc
    _ = ∑ p : OrbitIndex G C × G,
        QEC.Coding.LiftedProduct.rightRegularMatrix
            (groupAlgebraMatrix G P ro p.1) go p.2 *
          z ((freeOrbitEquiv G C).symm p) :=
      (Fintype.sum_prod_type _).symm
    _ = _ := by
      apply Fintype.sum_equiv (freeOrbitEquiv G C).symm
      intro p
      rcases p with ⟨co, gi⟩
      rw [rightRegularMatrix_groupAlgebraMatrix G P hP]
end QEC.Coding.BalancedProduct.FreeOrbitCoordinates
