-- Prove2me | solution 1 for SoficGroups.exists_pruned_expander
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/700512fd-c9f2-489b-b46f-69784b96da47

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_bad_cut_card_bound
import Theorems.Thm_SoficGroups_prune_permutation_multigraph
import Theorems.Thm_SoficGroups_exists_maximal_bad_cut

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (γ ell a : ℝ)
    (hgap : ell < γ)
    (hadd : ∀ A : Finset V,
      γ * min (A.card : ℝ) ((Fintype.card V : ℝ) - (A.card : ℝ)) -
          a * (Fintype.card V : ℝ) ≤ (boundary σ A : ℝ))
    (hsmall :
      2 * a * (2 * (γ - ell) + (Fintype.card ι : ℝ)) ≤ (γ - ell) ^ 2) :
    ∃ B : Finset V,
      2 * B.card ≤ Fintype.card V ∧
      (B.card : ℝ) ≤ a * (Fintype.card V : ℝ) / (γ - ell) ∧
      ∀ E : Finset V, Disjoint B E →
        2 * E.card ≤ Fintype.card V - B.card →
        ell * (E.card : ℝ) ≤ (inducedBoundary σ B E : ℝ) := by
  classical
  obtain ⟨B, hhalf, hB, hmax⟩ := exists_maximal_bad_cut σ ell
  refine ⟨B, hhalf, ?_, ?_⟩
  · have hhalfReal :
        (B.card : ℝ) ≤ (Fintype.card V : ℝ) - (B.card : ℝ) := by
      have hcast : 2 * (B.card : ℝ) ≤ (Fintype.card V : ℝ) := by
        exact_mod_cast hhalf
      linarith
    have hlow := hadd B
    rw [min_eq_left hhalfReal] at hlow
    exact bad_cut_card_bound hgap hlow hB
  · intro E hdisj hEhalf
    exact prune_permutation_multigraph σ γ ell a B hgap hadd hhalf hB
      hmax hsmall E hdisj hEhalf
end SoficGroups
