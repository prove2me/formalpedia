-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.hammingWeight_columnRestriction_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:55:40.104843+00:00
-- url     : https://prove2.me/submissions/07e47280-d32b-4ad4-87b9-1fcda35f1188

import Definitions.Def_QEC_Coding_QuantumTanner_TensorDuality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
namespace QEC.Coding.QuantumTanner
theorem _root_.solution [DecidableEq F]
    (b : B) (x : Word F (A × B)) :
    HammingWeight (columnRestriction b x) ≤ HammingWeight x := by
  have hs : (hammingSupport (columnRestriction b x)).image (fun a => (a, b)) ⊆
      hammingSupport x := by
    intro ab hab
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hab
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
  have hinj : Function.Injective (fun a : A => (a, b)) := fun _ _ h => congrArg Prod.fst h
  have hcard := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hinj] at hcard
  exact hcard
end QEC.Coding.QuantumTanner
