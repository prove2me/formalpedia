-- Prove2me | solution 1 for ThreeBoundWitness.sensitivity_reindex
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:39:44.747818+00:00
-- url     : https://prove2.me/submissions/2e11959a-5140-4108-8ca0-e17fc5795611

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace OAI.Paper320
end OAI.Paper320
section
/-
Common block and positive-sensitivity witnesses for a broad two-child
guarded construction. These are lower-bound witnesses; no upper sensitivity
transfer theorem is asserted here.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundWitness
open OAI.Paper320

variable {L I V : Type}

























































/- Reindexing lemmas follow the accepted Apache-2.0 source by @yousofy:
   Sol_Paley11987Verified_CompactFiniteProfile11987_actual_seeds_of_label_and_certificate,
   together with Definitions.Def_Paley11987Support_053. -/






theorem sensitivityAt_reindex {J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (f : (I → Bool) → Bool) (x : J → Bool) :
    sensitivityAt (reindex e f) x = sensitivityAt f (fun i => x (e i)) := by
  classical
  have hs : (Finset.univ.filter fun j =>
      reindex e f (OAI.Paper320.flip x {j}) ≠ reindex e f x).map e.symm.toEmbedding =
      Finset.univ.filter (fun i =>
        f (OAI.Paper320.flip (fun a => x (e a)) {i}) ≠ f (fun a => x (e a))) := by
    ext i
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change f (fun a => OAI.Paper320.flip x {e i} (e a)) ≠ f (fun a => x (e a)) ↔ _
    rw [flip_reindex_singleton]
  simpa only [sensitivityAt, Finset.card_map] using congrArg Finset.card hs



end ThreeBoundWitness








end

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ThreeBoundWitness
end ThreeBoundWitness
open ThreeBoundWitness
open OAI.Paper320
variable {L I V : Type}

theorem solution {J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (f : (I → Bool) → Bool) :
    sensitivity (reindex e f) = sensitivity f := by
  classical
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro x _
    rw [sensitivityAt_reindex]
    exact Finset.le_sup (Finset.mem_univ _)
  · apply Finset.sup_le
    intro x _
    have h : sensitivityAt (reindex e f) (fun j => x (e.symm j)) ≤
        sensitivity (reindex e f) := Finset.le_sup (Finset.mem_univ _)
    rw [sensitivityAt_reindex] at h
    simpa only [Equiv.symm_apply_apply] using h
end
