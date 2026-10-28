-- Prove2me | solution 1 for ThreeBoundWitness.blockSensitivity_lower_of_indexed_blocks
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:38:00.54606+00:00
-- url     : https://prove2.me/submissions/ef81f24b-9759-4faf-9896-d45531f2fc99

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace OAI.Paper320
end OAI.Paper320
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ThreeBoundWitness
end ThreeBoundWitness
open ThreeBoundWitness
open OAI.Paper320
variable {L I V : Type}

/-- Pairwise disjoint, nonempty sensitive blocks bound the campaign measure. -/
theorem solution [Fintype I] {A : Type} [Fintype A]
    (f : (I → Bool) → Bool) (x : I → Bool) (B : A → Finset I)
    (hne : ∀ a, (B a).Nonempty)
    (hdis : ∀ a b, a ≠ b → Disjoint (B a) (B b))
    (hflip : ∀ a, f (flip x (B a)) ≠ f x) :
    Fintype.card A ≤ blockSensitivity f := by
  classical
  have hinj : Function.Injective B := by
    intro a b hab
    by_contra hneab
    obtain ⟨i, hi⟩ := hne a
    have hib : i ∈ B b := by simpa only [hab] using hi
    exact Finset.disjoint_left.mp (hdis a b hneab) hi hib
  let blocks : Finset (Finset I) := Finset.univ.image B
  have hcond : (∀ C ∈ blocks, ∀ D ∈ blocks, C ≠ D → Disjoint C D) ∧
      (∀ C ∈ blocks, C.Nonempty ∧ f (flip x C) ≠ f x) := by
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
  have hat : blocks.card ≤ blockSensitivityAt f x := by
    have hh := Finset.le_sup (f := fun Cs : Finset (Finset I) =>
      if (∀ C ∈ Cs, ∀ D ∈ Cs, C ≠ D → Disjoint C D) ∧
          (∀ C ∈ Cs, C.Nonempty ∧ f (flip x C) ≠ f x)
      then Cs.card else 0) (Finset.mem_univ blocks)
    calc
      blocks.card = (if (∀ C ∈ blocks, ∀ D ∈ blocks, C ≠ D → Disjoint C D) ∧
          (∀ C ∈ blocks, C.Nonempty ∧ f (flip x C) ≠ f x)
        then blocks.card else 0) := (if_pos hcond).symm
      _ ≤ blockSensitivityAt f x := hh
  rw [hc] at hat
  exact hat.trans (Finset.le_sup (Finset.mem_univ x))
end
