-- Prove2me | solution 1 for SoficGroups.MatchedComponentExitBudget.sourceCompletionBad_surviving_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/95dabbc2-f58d-4e5c-9063-61881117e70b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_retained_bad_density_tendsto_zero
import Theorems.Thm_SoficGroups_MatchedComponentExitBudget_sourceCompletionBad_subset_survivors
import Theorems.Thm_SoficGroups_MatchedComponentExitBudget_sourceCompletionBad_original_density_tendsto_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedComponentExitBudget
open Filter Topology
open scoped BigOperators
namespace SoficGroups.MatchedComponentExitBudget
theorem _root_.solution
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    {ι J : Type*} [Fintype ι] [Group J]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (F : Finset J)
    (B : (n : ℕ) → Finset (V n))
    (hZ : ∀ n, (Finset.univ \ B n : Finset (V n)).Nonempty)
    (hdeleted : Tendsto
      (fun n => ((B n).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0))
    (hword : Tendsto
      (fun n =>
        ((sourceWordTestBad (σ n) (p n) F).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((SoficGroups.MatchedComponentCompletion.sourceCompletionBad
          (σ n) (p n) F (Finset.univ \ B n)).card : ℝ) /
            (Finset.univ \ B n : Finset (V n)).card)
      atTop (nhds 0) := by
  let U : (n : ℕ) → Finset (V n) := fun _ => Finset.univ
  let Z : (n : ℕ) → Finset (V n) := fun n => Finset.univ \ B n
  let E : (n : ℕ) → Finset (V n) := fun n =>
    SoficGroups.MatchedComponentCompletion.sourceCompletionBad
      (σ n) (p n) F (Z n)
  have hU (n : ℕ) : (U n).Nonempty := by
    obtain ⟨x, _⟩ := hZ n
    exact ⟨x, Finset.mem_univ _⟩
  have hcover : Tendsto
      (fun n => ((Z n).card : ℝ) / (U n).card)
      atTop (nhds 1) := by
    have hbase : Tendsto
        (fun n => (1 : ℝ) -
          ((B n).card : ℝ) / Fintype.card (V n))
        atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hdeleted
    convert hbase using 1
    funext n
    have hcard : Fintype.card (V n) ≠ 0 := by
      exact Finset.card_ne_zero.mpr (hU n)
    dsimp [U, Z]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ (B n)),
      Finset.card_univ, Nat.cast_sub (Finset.card_le_univ (B n))]
    field_simp
  have hglobal : Tendsto
      (fun n => (((U n ∩ E n).card : ℝ) / (U n).card))
      atTop (nhds 0) := by
    simpa [U, Z, E] using
      sourceCompletionBad_original_density_tendsto_zero
        V σ p F B hdeleted hword
  have hretained := SoficGroups.retained_bad_density_tendsto_zero
    U Z E hU hZ
    (fun n => Finset.subset_univ (Z n)) hcover hglobal
  convert hretained using 1
  funext n
  dsimp [Z, E]
  rw [Finset.inter_eq_right.mpr
    (sourceCompletionBad_subset_survivors
      (σ n) (p n) F (Finset.univ \ B n))]
end SoficGroups.MatchedComponentExitBudget
