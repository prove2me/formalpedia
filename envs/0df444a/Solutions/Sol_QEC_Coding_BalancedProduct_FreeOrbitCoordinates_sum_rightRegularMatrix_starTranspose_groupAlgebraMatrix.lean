-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.FreeOrbitCoordinates.sum_rightRegularMatrix_starTranspose_groupAlgebraMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:52:59.910407+00:00
-- url     : https://prove2.me/submissions/053d9c43-69cd-4785-8aa7-50d3e487cbd8

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates
import Theorems.Thm_QEC_Coding_BalancedProduct_FreeOrbitCoordinates_rightRegularMatrix_groupAlgebraMatrix
import Theorems.Thm_QEC_Coding_LiftedProduct_rightRegularMatrix_starTranspose_entry


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
    [Fintype R] [Fintype (OrbitIndex G R)]
    (P : Matrix R C F)
    (hP : ∀ (g : G) (r : R) (c : C), P (g • r) (g • c) = P r c)
    (y : R → F)
    (co : OrbitIndex G C) (go : G) :
    (∑ ro : OrbitIndex G R, ∑ gi : G,
      QEC.Coding.LiftedProduct.rightRegularMatrix
          (QEC.Coding.LiftedProduct.starTranspose
            (groupAlgebraMatrix G P) co ro) go gi *
        y ((freeOrbitEquiv G R).symm (ro, gi))) =
      ∑ r : R,
        P r ((freeOrbitEquiv G C).symm (co, go)) * y r := by
  calc
    _ = ∑ p : OrbitIndex G R × G,
        QEC.Coding.LiftedProduct.rightRegularMatrix
            (QEC.Coding.LiftedProduct.starTranspose
              (groupAlgebraMatrix G P) co p.1) go p.2 *
          y ((freeOrbitEquiv G R).symm p) :=
      (Fintype.sum_prod_type _).symm
    _ = _ := by
      apply Fintype.sum_equiv (freeOrbitEquiv G R).symm
      intro p
      rcases p with ⟨ro, gi⟩
      rw [show QEC.Coding.LiftedProduct.rightRegularMatrix
          (QEC.Coding.LiftedProduct.starTranspose
            (groupAlgebraMatrix G P) co ro) go gi =
          QEC.Coding.LiftedProduct.rightRegularMatrix
            (groupAlgebraMatrix G P ro co) gi go by
        exact congrFun (congrFun
          (QEC.Coding.LiftedProduct.rightRegularMatrix_starTranspose_entry
            (groupAlgebraMatrix G P) ro co) go) gi]
      rw [rightRegularMatrix_groupAlgebraMatrix G P hP]
end QEC.Coding.BalancedProduct.FreeOrbitCoordinates
