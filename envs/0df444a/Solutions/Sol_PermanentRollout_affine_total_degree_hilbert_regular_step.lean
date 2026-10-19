-- Prove2me | solution 1 for PermanentRollout.affine_total_degree_hilbert_regular_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/0aafc2db-c822-4802-80c8-38837dee21f5

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_affine_total_degree_filtered_factor_finrank_le
import Theorems.Thm_PermanentRollout_affine_total_degree_filtered_regular_finrank_inequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [Finite ι]
    (I : Ideal (MvPolynomial ι ℂ)) (g : MvPolynomial ι ℂ)
    (hregular : IsSMulRegular (MvPolynomial ι ℂ ⧸ I) g)
    (m : ℕ) :
    affineTotalDegreeHilbert
        (I ⊔ Ideal.span ({g} : Set (MvPolynomial ι ℂ))) m +
      (if g.totalDegree ≤ m then
        affineTotalDegreeHilbert I (m - g.totalDegree) else 0) ≤
          affineTotalDegreeHilbert I m := by
  by_cases hm : g.totalDegree ≤ m
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
    have hsub : g.totalDegree + n - g.totalDegree = n := by omega
    have hle : g.totalDegree ≤ g.totalDegree + n := by omega
    change
      Module.finrank ℂ
          (affineTotalDegreeFilteredPiece
            (I ⊔ Ideal.span ({g} : Set (MvPolynomial ι ℂ)))
              (g.totalDegree + n)) +
        (if g.totalDegree ≤ g.totalDegree + n then
          Module.finrank ℂ
            (affineTotalDegreeFilteredPiece I
              (g.totalDegree + n - g.totalDegree)) else 0) ≤
          Module.finrank ℂ
            (affineTotalDegreeFilteredPiece I (g.totalDegree + n))
    rw [if_pos hle, hsub]
    exact affine_total_degree_filtered_regular_finrank_inequality
      I g hregular n
  · simp only [if_neg hm, add_zero]
    exact affine_total_degree_filtered_factor_finrank_le
      (show I ≤ I ⊔ Ideal.span ({g} : Set (MvPolynomial ι ℂ)) from
        le_sup_left) m
end PermanentRollout
