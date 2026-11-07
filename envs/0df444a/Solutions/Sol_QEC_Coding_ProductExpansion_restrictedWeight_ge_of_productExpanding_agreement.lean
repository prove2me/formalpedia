-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.restrictedWeight_ge_of_productExpanding_agreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:03:42.090231+00:00
-- url     : https://prove2.me/submissions/7201b6d9-ef57-4257-b729-b98866c1fe7d

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_restrictedWeight_mono


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [DecidableEq W] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (h' : Matrix R' W F)
    (f t : Matrix W W F) (A B J₃ : Finset W)
    (s m : Nat) (beta : ℝ)
    (hExpand : ProductExpanding h h' s (2 * m) beta)
    (hKernel : ProductKernel h h' t) (hNonzero : t ≠ 0)
    (hMinimal : IsDeltaMinimal h h'
      (beta * Fintype.card W) t)
    (hA : Fintype.card W - 2 * m ≤ A.card)
    (hJ₃ : Fintype.card W - 2 * m ≤ J₃.card)
    (hJ₃B : J₃ ⊆ B)
    (hAgree : ∀ i ∈ J₃, ∀ j ∈ A, f i j = t i j) :
    s ≤ restrictedWeight f B A := by
  have hProduct : s ≤ restrictedWeight t J₃ A :=
    hExpand t hKernel hNonzero hMinimal J₃ A hJ₃ hA
  have hEq : restrictedWeight f J₃ A = restrictedWeight t J₃ A := by
    unfold restrictedWeight
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hAgree i hi j hj]
  calc
    s ≤ restrictedWeight t J₃ A := hProduct
    _ = restrictedWeight f J₃ A := hEq.symm
    _ ≤ restrictedWeight f B A :=
      restrictedWeight_mono f hJ₃B (Finset.Subset.refl A)
end QEC.Coding.ProductExpansion
