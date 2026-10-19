-- Prove2me | solution 1 for SoficGroups.CompletedSourceFinalGeneratorTransfer.surviving_card_ratio_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/2abbce7d-bda4-4746-8d9c-cd8c1ff5046d

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedSourceFinalGeneratorTransfer
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.CompletedSourceChosenWordRestrictionTransfer
namespace SoficGroups.CompletedSourceFinalGeneratorTransfer
theorem _root_.solution
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (D : (n : ℕ) → Finset (V n))
    (hZ : ∀ n, (Finset.univ \ D n : Finset (V n)).Nonempty)
    (hdeleted : Tendsto
      (fun n => ((D n).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (((Finset.univ \ D n : Finset (V n)).card : ℝ) /
          Fintype.card (V n)))
      atTop (nhds 1) := by
  have hbase : Tendsto
      (fun n => (1 : ℝ) -
        ((D n).card : ℝ) / Fintype.card (V n))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hdeleted
  convert hbase using 1
  funext n
  have hU : (Finset.univ : Finset (V n)).Nonempty := by
    obtain ⟨x, _⟩ := hZ n
    exact ⟨x, Finset.mem_univ x⟩
  have hcard : Fintype.card (V n) ≠ 0 := by
    exact Finset.card_ne_zero.mpr hU
  rw [Finset.card_sdiff_of_subset
      (Finset.subset_univ (D n)),
    Finset.card_univ,
    Nat.cast_sub (Finset.card_le_univ (D n))]
  field_simp
end SoficGroups.CompletedSourceFinalGeneratorTransfer
