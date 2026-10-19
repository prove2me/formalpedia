-- Prove2me | solution 1 for PermanentRollout.affine_finrank_le_degree_product_of_regular_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/cee1ca4d-5da4-4ac7-8c2a-0e4694a65ad0

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_affine_total_degree_filtered_piece_eventual_finrank
import Theorems.Thm_PermanentRollout_affine_cumulative_iterate_eventual_constant_lower
import Theorems.Thm_PermanentRollout_affine_le_of_shifted_choose_bounds
import Theorems.Thm_PermanentRollout_affine_total_degree_cumulative_iterate_regular

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [Fintype ι]
    (I : ℕ → Ideal (MvPolynomial ι ℂ))
    (g : ℕ → MvPolynomial ι ℂ)
    (hzero : I 0 = ⊥)
    (hnext : ∀ i, i < Fintype.card ι →
      I (i + 1) = I i ⊔ Ideal.span ({g i} : Set (MvPolynomial ι ℂ)))
    (hregular : ∀ i, i < Fintype.card ι →
      IsSMulRegular (MvPolynomial ι ℂ ⧸ I i) (g i))
    [Module.Finite ℂ (MvPolynomial ι ℂ ⧸ I (Fintype.card ι))] :
    Module.finrank ℂ (MvPolynomial ι ℂ ⧸ I (Fintype.card ι)) ≤
      ∏ i ∈ Finset.range (Fintype.card ι), (g i).totalDegree := by
  let n := Fintype.card ι
  let L := Module.finrank ℂ (MvPolynomial ι ℂ ⧸ I n)
  let P := ∏ i ∈ Finset.range n, (g i).totalDegree
  obtain ⟨N, hN⟩ :=
    affine_total_degree_filtered_piece_eventual_finrank (I n)
  have heventual : ∀ m : ℕ, N ≤ m →
      affineTotalDegreeHilbert (I n) m = L := by
    intro m hm
    exact hN m hm
  change L ≤ P
  apply affine_le_of_shifted_choose_bounds L P n N
  intro m
  calc
    L * (m + n).choose n ≤
        (affineCumulative^[n])
          (affineTotalDegreeHilbert (I n)) (N + m) :=
      affine_cumulative_iterate_eventual_constant_lower
        (affineTotalDegreeHilbert (I n)) L N heventual n m
    _ ≤ P * (N + m + n).choose n := by
      exact affine_total_degree_cumulative_iterate_regular
        I g n hzero hnext hregular (N + m)
    _ = P * (m + N + n).choose n := by
      simp [Nat.add_comm]
end PermanentRollout
