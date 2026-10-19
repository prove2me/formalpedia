-- Prove2me | solution 1 for SoficGroups.KunResidualExpanderDecomposition.exists_minimum_sparse_residual_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/e60658a0-322b-4df9-a89c-83cf47644d0a

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualExpanderDecomposition
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunResidualExpanderDecomposition
theorem _root_.solution {V ι : Type*}
    [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (R : Finset V) (γ : ℝ)
    (hsparse : ∃ T : Finset V, T ⊆ R ∧
      (SoficGroups.boundary σ T : ℝ) < γ * (T.card : ℝ)) :
    ∃ T : Finset V, T ⊆ R ∧
      (SoficGroups.boundary σ T : ℝ) < γ * (T.card : ℝ) ∧
      ∀ E : Finset V, E ⊆ R →
        (SoficGroups.boundary σ E : ℝ) < γ * (E.card : ℝ) →
        T.card ≤ E.card := by
  classical
  let candidates : Finset (Finset V) :=
    R.powerset.filter fun T =>
      (SoficGroups.boundary σ T : ℝ) < γ * (T.card : ℝ)
  have hcandidates : candidates.Nonempty := by
    obtain ⟨T, hTR, hT⟩ := hsparse
    refine ⟨T, ?_⟩
    simp [candidates, hTR, hT]
  obtain ⟨T, hT, hminimum⟩ :=
    Finset.exists_min_image candidates Finset.card hcandidates
  have hT' := (Finset.mem_filter.mp hT)
  refine ⟨T, Finset.mem_powerset.mp hT'.1, hT'.2, ?_⟩
  intro E hER hE
  apply hminimum E
  simp [candidates, hER, hE]
end SoficGroups.KunResidualExpanderDecomposition
