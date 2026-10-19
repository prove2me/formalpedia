-- Prove2me | solution 1 for PermanentRollout.exists_inputSlice_projective_disjoint_of_criticalLocusDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/e3de85e8-7d9e-48fe-ac1f-9e435880d66a

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_permanent_rollout_exists_independent_linear_ideal_dimension_zero
import Theorems.Thm_PermanentRollout_zeroLocus_gradientIdeal_eq_criticalLocus
import Theorems.Thm_PermanentRollout_gradientVector_eq_zero_iff
import Theorems.Thm_PermanentRollout_projective_input_disjoint_iff
import Theorems.Thm_PermanentRollout_criticalGradientIdeal_isHomogeneous
import Theorems.Thm_PermanentRollout_exists_injective_inputMap_into_linearCoordinateKernel
import Theorems.Thm_PermanentRollout_eq_zero_of_mem_zeroLocus_of_linearCoordinateKernel_of_radical
import Theorems.Thm_PermanentRollout_criticalLinearSliceIdeal_radical_eq_idealOfVars_of_dimension_le_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {m k d : ℕ} (P : MvPolynomial (Fin m) ℂ)
    (hd : 2 ≤ d) (hP : P.IsHomogeneous d)
    (hk : k ≤ m)
    (hcodimension : criticalLocusDimension P ≤
      ((m - k : ℕ) : WithBot ℕ∞)) :
    ∃ W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ),
      Function.Injective W ∧
      Disjoint
        ((LinearMap.range W).projectivization : Set (ℙ ℂ (Fin m → ℂ)))
        (projectiveCriticalLocus P) := by
  let I : Ideal (MvPolynomial (Fin m) ℂ) :=
    homogeneousMapIdeal (fun i : Fin m => MvPolynomial.pderiv i P)
  have hIhomogeneous :
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) ℂ) :=
    criticalGradientIdeal_isHomogeneous P hP
  have hIdimension :
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ I) ≤
        ((m - k : ℕ) : WithBot ℕ∞) := hcodimension
  obtain ⟨q, c, hq, _, hzero_dimension⟩ :=
    permanent_rollout_exists_independent_linear_ideal_dimension_zero
      I hIhomogeneous (m - k) hIdimension
  have hkq : k + q ≤ m := by omega
  obtain ⟨W, hW, hkernel⟩ :=
    exists_injective_inputMap_into_linearCoordinateKernel c hkq
  have hradical :=
    criticalLinearSliceIdeal_radical_eq_idealOfVars_of_dimension_le_zero
      P hd hP c hzero_dimension
  refine ⟨W, hW, (projective_input_disjoint_iff P W hW).mpr ?_⟩
  intro u hu hgradient
  have hcritical : W u ∈ criticalLocus P :=
    (gradientVector_eq_zero_iff P (W u)).mp hgradient
  have hvanishing : W u ∈ MvPolynomial.zeroLocus ℂ I := by
    change W u ∈ MvPolynomial.zeroLocus ℂ
      (homogeneousMapIdeal
        (fun i : Fin m => MvPolynomial.pderiv i P))
    rw [zeroLocus_gradientIdeal_eq_criticalLocus]
    exact hcritical
  have hradical' :
      (I ⊔ Ideal.span (Set.range fun j =>
        permanentRolloutLinearCoordinateCombination m (c j))).radical =
        MvPolynomial.idealOfVars (Fin m) ℂ := hradical
  have hWu : W u = 0 :=
    eq_zero_of_mem_zeroLocus_of_linearCoordinateKernel_of_radical
      I c hradical' hvanishing (hkernel u)
  exact hu (hW (by simpa using hWu))
end PermanentRollout
