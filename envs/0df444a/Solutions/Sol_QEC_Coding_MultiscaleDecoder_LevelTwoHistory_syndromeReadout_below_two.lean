-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.LevelTwoHistory.syndromeReadout_below_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:55:23.710227+00:00
-- url     : https://prove2.me/submissions/8d345679-b3de-48b3-97d4-abc1c071fd0c

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.MultiscaleDecoder QEC.Coding.MultiscaleDecoder.LevelTwoHistory
universe u v
variable {n : Nat}
variable {C0 C1 C2 : LevelIndex (n + 2) → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
namespace QEC.Coding.MultiscaleDecoder.LevelTwoHistory
theorem _root_.solution (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (H : CorrectionHistory (suffixData D)) (i : LevelIndex (n + 2)) (hi : i.val < 2) :
    syndromeReadout D H i = 0 := by
  classical
  unfold syndromeReadout
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  have htwo : 2 ≤ p.1.val := by
    unfold physicalInputSnapshots at hp
    obtain ⟨e, _, he⟩ := List.mem_map.mp hp
    have hv := congrArg (fun q : Σ j : LevelIndex (n + 2), D.family.Syndrome j =>
      q.1.val) he
    change e.inputSyndrome.1.val + 2 = p.1.val at hv
    omega
  have hne : p.1 ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    omega
  exact dif_neg hne
end QEC.Coding.MultiscaleDecoder.LevelTwoHistory
