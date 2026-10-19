-- Prove2me | solution 1 for PermanentRollout.exists_inputSlice_projective_disjoint_of_criticalLocus_codimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/744d09a2-85f3-4a46-a1ce-074b526c5647

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_exists_inputSlice_projective_disjoint_of_criticalLocusDimension

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {m k c d : ℕ} (P : MvPolynomial (Fin m) ℂ)
    (hd : 2 ≤ d) (hP : P.IsHomogeneous d)
    (hk : k ≤ c) (hm : k < m)
    (hcodimension : criticalLocusDimension P ≤
      ((m - c : ℕ) : WithBot ℕ∞)) :
    ∃ W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ),
      Function.Injective W ∧
      Disjoint
        ((LinearMap.range W).projectivization : Set (ℙ ℂ (Fin m → ℂ)))
        (projectiveCriticalLocus P) := by
  have hsubtraction : m - c ≤ m - k := by omega
  have hcast :
      ((m - c : ℕ) : WithBot ℕ∞) ≤
        ((m - k : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast hsubtraction
  exact exists_inputSlice_projective_disjoint_of_criticalLocusDimension
    P hd hP hm.le (hcodimension.trans hcast)
end PermanentRollout
