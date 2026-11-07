-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.restrictedWeight_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:35:52.994287+00:00
-- url     : https://prove2.me/submissions/9756746d-326c-4199-8589-1d966b59449f

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype F] [Fintype W] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (x : Matrix W W F) {A A' B B' : Finset W}
    (hA : A' ⊆ A) (hB : B' ⊆ B) :
    restrictedWeight x A' B' ≤ restrictedWeight x A B := by
  unfold restrictedWeight
  calc
    (∑ i ∈ A', ∑ j ∈ B', if x i j = 0 then 0 else 1) ≤
        ∑ i ∈ A', ∑ j ∈ B, if x i j = 0 then 0 else 1 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum_of_subset_of_nonneg hB
      intro j hjB hjB'
      omega
    _ ≤ ∑ i ∈ A, ∑ j ∈ B, if x i j = 0 then 0 else 1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hA
      intro i hiA hiA'
      omega
end QEC.Coding.ProductExpansion
