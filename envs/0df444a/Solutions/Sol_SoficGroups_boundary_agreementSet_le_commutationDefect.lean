-- Prove2me | solution 1 for SoficGroups.boundary_agreementSet_le_commutationDefect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/49163064-90ec-4ff9-9920-df883128a757

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (c c' : Equiv.Perm V) :
    boundary σ (agreementSet c c') ≤
      permutationCommutationDefect σ c +
        permutationCommutationDefect σ c' := by
  classical
  unfold boundary permutationCommutationDefect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  let B : Finset V :=
    Finset.univ.filter fun x => c (σ i x) ≠ σ i (c x)
  let B' : Finset V :=
    Finset.univ.filter fun x => c' (σ i x) ≠ σ i (c' x)
  have hsub :
      (agreementSet c c').filter (fun x => σ i x ∉ agreementSet c c') ⊆
        B ∪ B' := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    have hagree : c x = c' x :=
      (Finset.mem_filter.mp hx'.1).2
    have hdisagree : c (σ i x) ≠ c' (σ i x) := by
      intro heq
      exact hx'.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩)
    by_cases hc : c (σ i x) = σ i (c x)
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hc'
      apply hdisagree
      calc
        c (σ i x) = σ i (c x) := hc
        _ = σ i (c' x) := congrArg (σ i) hagree
        _ = c' (σ i x) := hc'.symm
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le B B')
end SoficGroups
