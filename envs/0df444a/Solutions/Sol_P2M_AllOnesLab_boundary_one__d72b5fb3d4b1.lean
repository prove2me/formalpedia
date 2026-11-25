-- Prove2me | solution 1 for P2M_AllOnesLab_boundary_one__d72b5fb3d4b1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:54:47.907137+00:00
-- url     : https://prove2.me/submissions/063e3749-99a0-4f22-a316-176d1f7ab188

import Definitions.Def_AllOnesLab_Defs
import Definitions.Def_AllOnesLab_Basic
section
open Polynomial
namespace AllOnesLab
private lemma two_eq_zero_poly : (2 : (ZMod 2)[X]) = 0 := by
  simpa using CharP.cast_eq_zero ((ZMod 2)[X]) 2
end AllOnesLab
end

set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution : Irreducible (allOnes 1) ∧ ¬ Irreducible (allOnesP 1) := by
  refine ⟨?_, ?_⟩
  · have h1 : allOnes 1 = X + C (1 : ZMod 2) := by
      rw [allOnes, Finset.sum_range_succ, Finset.sum_range_one, Polynomial.C_1, pow_zero, pow_one,
        add_comm]
    rw [h1]
    exact (monic_X_add_C (1 : ZMod 2)).irreducible_of_degree_eq_one (degree_X_add_C 1)
  · intro h
    have h1 : allOnesP 1 = 1 + P := by
      simp [allOnesP, Finset.sum_range_succ]
    have hfac : allOnesP 1 = X * (X + 1) := by
      rw [h1]
      simp only [P]
      linear_combination two_eq_zero_poly
    have hX : (X : (ZMod 2)[X]).natDegree = 1 := natDegree_X
    have hX1 : (X + 1 : (ZMod 2)[X]).natDegree = 1 := by compute_degree!
    rcases h.isUnit_or_isUnit hfac with hu | hu
    · exact not_isUnit_of_natDegree_pos _ (by omega) hu
    · exact not_isUnit_of_natDegree_pos _ (by omega) hu
end AllOnesLab
