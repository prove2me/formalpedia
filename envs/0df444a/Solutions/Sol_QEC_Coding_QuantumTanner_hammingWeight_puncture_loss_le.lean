-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.hammingWeight_puncture_loss_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:46:51.457185+00:00
-- url     : https://prove2.me/submissions/0256baa5-6eb5-417f-9e63-61cee0ad01ec

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
namespace QEC.Coding.QuantumTanner
theorem _root_.solution [DecidableEq F]
    (removed : Finset A) (x : Word F A) :
    HammingWeight x ≤ HammingWeight (punctureMap removed x) + removed.card := by
  have hImage : (hammingSupport (punctureMap removed x)).image Subtype.val =
      hammingSupport x \ removed := by
    ext a
    constructor
    · intro ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩, i.2⟩
    · intro ha
      obtain ⟨ha, hNot⟩ := Finset.mem_sdiff.mp ha
      exact Finset.mem_image.mpr ⟨⟨a, hNot⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩, rfl⟩
  have hCard := congrArg Finset.card hImage
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hCard
  have hPartition := Finset.card_sdiff_add_card_inter (hammingSupport x) removed
  have hInter := Finset.card_le_card (Finset.inter_subset_right :
    hammingSupport x ∩ removed ⊆ removed)
  change (hammingSupport x).card ≤ (hammingSupport (punctureMap removed x)).card + _
  omega
end QEC.Coding.QuantumTanner
