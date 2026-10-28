-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundWitness.blockSensitivity_lower_of_indexed_blocks
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:35:54.13103+00:00
-- url     : https://prove2.me/submissions/33a23ad2-890a-4482-bcce-b261b49c51e7

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



















































/-- Pairwise disjoint, nonempty sensitive blocks bound the campaign measure. -/
theorem blockSensitivity_lower_of_indexed_blocks [Fintype I] {A : Type} [Fintype A]
    (f : (I → Bool) → Bool) (x : I → Bool) (B : A → Finset I)
    (hne : ∀ a, (B a).Nonempty)
    (hdis : ∀ a b, a ≠ b → Disjoint (B a) (B b))
    (hflip : ∀ a, f (_root_.OAI.Paper320.flip x (B a)) ≠ f x) :
    Fintype.card A ≤  _root_.OAI.Paper320.blockSensitivity f := by
  classical
  have hinj : Function.Injective B := by
    intro a b hab
    by_contra hneab
    obtain ⟨i, hi⟩ := hne a
    have hib : i ∈ B b := by simpa only [hab] using hi
    exact Finset.disjoint_left.mp (hdis a b hneab) hi hib
  let blocks : Finset (Finset I) := Finset.univ.image B
  have hcond : (∀ C ∈ blocks, ∀ D ∈ blocks, C ≠ D → Disjoint C D) ∧
      (∀ C ∈ blocks, C.Nonempty ∧ f (_root_.OAI.Paper320.flip x C) ≠ f x) := by
    constructor
    · intro C hC D hD hCD
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hC
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hD
      exact hdis a b (fun hab => hCD (congrArg B hab))
    · intro C hC
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hC
      exact ⟨hne a, hflip a⟩
  have hc : blocks.card = Fintype.card A := by
    simp only [blocks, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have hat : blocks.card ≤  _root_.OAI.Paper320.blockSensitivityAt f x := by
    have hh := Finset.le_sup (f := fun Cs : Finset (Finset I) =>
      if (∀ C ∈ Cs, ∀ D ∈ Cs, C ≠ D → Disjoint C D) ∧
          (∀ C ∈ Cs, C.Nonempty ∧ f (_root_.OAI.Paper320.flip x C) ≠ f x)
      then Cs.card else 0) (Finset.mem_univ blocks)
    calc
      blocks.card = (if (∀ C ∈ blocks, ∀ D ∈ blocks, C ≠ D → Disjoint C D) ∧
          (∀ C ∈ blocks, C.Nonempty ∧ f (_root_.OAI.Paper320.flip x C) ≠ f x)
        then blocks.card else 0) := (if_pos hcond).symm
      _ ≤  _root_.OAI.Paper320.blockSensitivityAt f x := hh
  rw [hc] at hat
  exact hat.trans (Finset.le_sup (Finset.mem_univ x))





/- Reindexing lemmas follow the accepted Apache-2.0 source by @yousofy:
   Sol_Paley11987Verified_CompactFiniteProfile11987_actual_seeds_of_label_and_certificate,
   together with Definitions.Def_Paley11987Support_053. -/










end ThreeBoundWitness








end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {I : Type} [inst : Fintype.{0} I] {A : Type} [inst_1 : Fintype.{0} A] (f : (I → Bool) → Bool) (x : I → Bool)
  (B : A → Finset.{0} I) (hne : ∀ (a : A), @Finset.Nonempty.{0} I (B a))
  (hdis :
    ∀ (a b : A),
      @Ne.{1} A a b →
        @Disjoint.{0} (Finset.{0} I) (@Finset.instPartialOrder.{0} I) (@Finset.instOrderBot.{0} I) (B a) (B b))
  (hflip : ∀ (a : A), @Ne.{1} Bool (f (@OAI.Paper320.flip I x (B a))) (f x)),
  @LE.le.{0} Nat instLENat (@Fintype.card.{0} A inst_1) (@OAI.Paper320.blockSensitivity I inst f) := @Sensitivity213981Formal.ThreeBoundWitness.blockSensitivity_lower_of_indexed_blocks
