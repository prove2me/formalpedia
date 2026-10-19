-- Prove2me | solution 1 for SoficGroups.hamming_dichotomy_of_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/c518aa0b-fdc3-47e0-b95f-ed64a530e241

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_agreementSet_card_add_hammingDist
import Theorems.Thm_SoficGroups_boundary_agreementSet_le_commutationDefect

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (h : ℝ)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
          ((Fintype.card V : ℝ) - A.card) ≤
        (boundary σ A : ℝ))
    (c c' : Equiv.Perm V) :
    h * (hammingDist (fun x => c x) (fun x => c' x) : ℝ) ≤
        (permutationCommutationDefect σ c +
          permutationCommutationDefect σ c' : ℕ) ∨
      h * ((Fintype.card V : ℝ) -
          hammingDist (fun x => c x) (fun x => c' x)) ≤
        (permutationCommutationDefect σ c +
          permutationCommutationDefect σ c' : ℕ) := by
  have hcard := agreementSet_card_add_hammingDist c c'
  have hcard' :
      ((agreementSet c c').card : ℝ) +
        (hammingDist (fun x => c x) (fun x => c' x) : ℝ) =
          Fintype.card V := by
    exact_mod_cast hcard
  have hboundary := boundary_agreementSet_le_commutationDefect σ c c'
  have hboundary' :
      (boundary σ (agreementSet c c') : ℝ) ≤
        (permutationCommutationDefect σ c +
          permutationCommutationDefect σ c' : ℕ) := by
    exact_mod_cast hboundary
  have hcut := (hexp (agreementSet c c')).trans hboundary'
  by_cases hhalf :
      ((agreementSet c c').card : ℝ) ≤
        (Fintype.card V : ℝ) - (agreementSet c c').card
  · right
    rw [min_eq_left hhalf] at hcut
    have hident :
        (Fintype.card V : ℝ) -
          hammingDist (fun x => c x) (fun x => c' x) =
            (agreementSet c c').card := by
      linarith [hcard']
    simpa [hident] using hcut
  · left
    rw [min_eq_right (le_of_not_ge hhalf)] at hcut
    have hident :
        (Fintype.card V : ℝ) - (agreementSet c c').card =
          hammingDist (fun x => c x) (fun x => c' x) := by
      linarith [hcard']
    simpa [hident] using hcut
end SoficGroups
