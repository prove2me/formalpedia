-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.hammingWeight_punctureMap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:50:45.142722+00:00
-- url     : https://prove2.me/submissions/f82b5f64-e2b9-4fb7-a321-aa0f26b902db

import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
variable {A B : Type v} [Fintype A] [Fintype B]
namespace QEC.Coding.QuantumTanner
theorem _root_.solution {ι : Type v} [Fintype ι]
    (removed : Finset ι) (x : Word (ZMod 2) ι) :
    HammingWeight (punctureMap removed x) ≤ HammingWeight x := by
  have hSubset : (hammingSupport (punctureMap removed x)).image Subtype.val ⊆
      hammingSupport x := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  have hCard := Finset.card_le_card hSubset
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hCard
  exact hCard
end QEC.Coding.QuantumTanner
