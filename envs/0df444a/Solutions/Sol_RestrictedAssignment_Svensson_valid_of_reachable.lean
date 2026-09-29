-- Prove2me | solution 1 for RestrictedAssignment.Svensson.valid_of_reachable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:14:16.766241+00:00
-- url     : https://prove2.me/submissions/913a11c7-b1f9-4c22-8353-b0419dc3fef8

import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP
import Definitions.Def_RestrictedAssignment_Svensson_extendSchedule

namespace RestrictedAssignment.Svensson

theorem aux_vor_step_valid {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (jnew : J) (s s' : AlgState J M)
    (hst : Step Γ p jnew s s') (hs : Valid Γ p s.σ) : Valid Γ p s'.σ := by
  obtain ⟨_, j, i, _, _, k, hk, _, rfl⟩ := hst
  by_cases hv : IsValidMove Γ p s j i
  · rw [if_pos hv]
    exact hv.2
  · rw [if_neg hv]
    split_ifs <;> exact hs

end RestrictedAssignment.Svensson

open RestrictedAssignment.Svensson

theorem solution {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (σ0 : J → Option M) (jnew : J)
    (hσ0 : Valid Γ p σ0) (hjnew : σ0 jnew = none) (s : AlgState J M)
    (hs : Reachable Γ p σ0 jnew s) :
    Valid Γ p s.σ := by
  induction hs with
  | refl => exact hσ0
  | tail _ hst ih => exact aux_vor_step_valid Γ p jnew _ _ hst ih
