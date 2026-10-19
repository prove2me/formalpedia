-- Prove2me | solution 1 for SoficGroups.KunThomInvariantOrthogonal.unitaryFinsetMarkov_iterate_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/fde4ca0a-8dfa-4903-85fd-5453258f0292

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_kazhdanMarkovContractionFactor_nonneg
import Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_unitaryFinsetMarkov_norm_le
import Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_unitaryFinsetMarkov_orthogonal_invariants

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomInvariantOrthogonal
open Filter Topology
open scoped ComplexConjugate Pointwise
universe u v
variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace SoficGroups.KunThomInvariantOrthogonal
theorem _root_.solution
    [CompleteSpace H] (P : SoficGroups.KazhdanPair.{u, v} G)
    (π : SoficGroups.UnitaryRepresentation G H)
    (S : Finset G) (hone : 1 ∈ S)
    (hsub : P.generators ⊆ S) (x : H)
    (horth : ∀ y : H,
      (∀ g : G, π g y = y) → @inner ℂ H _ y x = 0)
    (n : ℕ) :
    ‖((unitaryFinsetMarkov π S)^[n]) x‖ ≤
      kazhdanMarkovContractionFactor P S ^ n * ‖x‖ := by
  have horthn (k : ℕ) :
      ∀ y : H, (∀ g : G, π g y = y) →
        @inner ℂ H _ y (((unitaryFinsetMarkov π S)^[k]) x) = 0 := by
    induction k with
    | zero => simpa using horth
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact unitaryFinsetMarkov_orthogonal_invariants
        π S (((unitaryFinsetMarkov π S)^[k]) x) ih
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc
      ‖unitaryFinsetMarkov π S
          (((unitaryFinsetMarkov π S)^[n]) x)‖ ≤
        kazhdanMarkovContractionFactor P S *
          ‖((unitaryFinsetMarkov π S)^[n]) x‖ :=
        unitaryFinsetMarkov_norm_le P π S hone hsub _ (horthn n)
      _ ≤ kazhdanMarkovContractionFactor P S *
          (kazhdanMarkovContractionFactor P S ^ n * ‖x‖) :=
        mul_le_mul_of_nonneg_left ih
          (kazhdanMarkovContractionFactor_nonneg P S)
      _ = kazhdanMarkovContractionFactor P S ^ n.succ * ‖x‖ := by
        rw [pow_succ]
        ring
end SoficGroups.KunThomInvariantOrthogonal
