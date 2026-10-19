-- Prove2me | solution 1 for PermanentRollout.projective_input_disjoint_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/e0648cc3-e722-4e3a-93ba-905022dc4b89

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_gradientVector_eq_zero_iff
import Theorems.Thm_PermanentRollout_gradientVector_after_embedding_ne_zero_of_projective_disjoint

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution {m k : ℕ}
    (P : MvPolynomial (Fin m) ℂ)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (hW : Function.Injective W) :
    Disjoint
      ((LinearMap.range W).projectivization : Set (ℙ ℂ (Fin m → ℂ)))
      (projectiveCriticalLocus P) ↔
      ∀ (u : Fin k → ℂ), u ≠ 0 → gradientVector P (W u) ≠ 0 := by
  constructor
  · exact gradientVector_after_embedding_ne_zero_of_projective_disjoint
      P W hW
  · intro hnonzero
    apply Set.disjoint_left.mpr
    intro point hpoint_range hpoint_critical
    obtain ⟨v, hv, hpoint, hcritical⟩ := hpoint_critical
    rw [← hpoint] at hpoint_range
    have hv_range : v ∈ LinearMap.range W :=
      (Submodule.mk_mem_projectivization_iff _ hv).mp hpoint_range
    obtain ⟨u, hu⟩ := hv_range
    have hu_ne : u ≠ 0 := by
      intro hu_zero
      apply hv
      rw [← hu, hu_zero]
      exact W.map_zero
    apply hnonzero u hu_ne
    rw [hu]
    exact (gradientVector_eq_zero_iff P v).mpr hcritical
end PermanentRollout
