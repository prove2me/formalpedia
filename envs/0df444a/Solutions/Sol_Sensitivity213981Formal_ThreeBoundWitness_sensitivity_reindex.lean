-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundWitness.sensitivity_reindex
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:38:59.040411+00:00
-- url     : https://prove2.me/submissions/26fa4ad5-4281-4c09-9ea6-aeaba11bfd6e

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith


namespace Sensitivity213981Formal
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
    _root_.OAI.Paper320.sensitivityAt (reindex e f) x = _root_.OAI.Paper320.sensitivityAt f (fun i => x (e i)) := by
  classical
  have hs : (Finset.univ.filter fun j =>
      reindex e f (_root_.OAI.Paper320.flip x {j}) ≠ reindex e f x).map e.symm.toEmbedding =
      Finset.univ.filter (fun i =>
        f (_root_.OAI.Paper320.flip (fun a => x (e a)) {i}) ≠ f (fun a => x (e a))) := by
    ext i
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change f (fun a => _root_.OAI.Paper320.flip x {e i} (e a)) ≠ f (fun a => x (e a)) ↔ _
    rw [flip_reindex_singleton]
  simpa only [_root_.OAI.Paper320.sensitivityAt, Finset.card_map] using congrArg Finset.card hs

theorem sensitivity_reindex {J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (f : (I → Bool) → Bool) :
    _root_.OAI.Paper320.sensitivity (reindex e f) = _root_.OAI.Paper320.sensitivity f := by
  classical
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro x _
    rw [sensitivityAt_reindex]
    exact Finset.le_sup (Finset.mem_univ _)
  · apply Finset.sup_le
    intro x _
    have h : _root_.OAI.Paper320.sensitivityAt (reindex e f) (fun j => x (e.symm j)) ≤ 
        _root_.OAI.Paper320.sensitivity (reindex e f) := Finset.le_sup (Finset.mem_univ _)
    rw [sensitivityAt_reindex] at h
    simpa only [Equiv.symm_apply_apply] using h

end ThreeBoundWitness








end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {I J : Type} [inst : Fintype.{0} I] [inst_1 : Fintype.{0} J] (e : Equiv.{1, 1} I J) (f : (I → Bool) → Bool),
  @Eq.{1} Nat (@OAI.Paper320.sensitivity J inst_1 (@Sensitivity213981Formal.ThreeBoundWitness.reindex I J e f))
    (@OAI.Paper320.sensitivity I inst f) := @Sensitivity213981Formal.ThreeBoundWitness.sensitivity_reindex
