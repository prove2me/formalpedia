-- Prove2me | solution 1 for TunnellMap.midpoint_parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:53:44.49749+00:00
-- url     : https://prove2.me/submissions/0af7e595-4980-4128-87a8-d18dadb5dd28

import Definitions.Def_TunnellMap_QuarterTurns
import Definitions.Def_TunnellMap_Midpoint
import Theorems.Thm_TunnellMap_qForm_bLift
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_lifted_first_coordinates_same_parity
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_odd_y_of_aRep
import Theorems.Thm_TunnellMap_odd_y_of_bOdd
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply


attribute [local simp] TunnellMap.qForm_bLift
attribute [local simp] TunnellMap.qForm_aLift

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hn : Odd n) (s : BOddRep n) (t : ARep n) :
    ∃ hPlus hMinus : Triple,
      IsHalfSum hPlus (bLift s) (aLift t) ∧ Odd hPlus.z ∧
      IsHalfDiff hMinus (bLift s) (aLift t) ∧ Odd hMinus.z := by
  obtain ⟨sy, hsy⟩ := odd_y_of_bOdd hn s
  obtain ⟨ty, hty⟩ := odd_y_of_aRep hn t
  obtain ⟨sz, hsz⟩ := s.2.2
  rcases lifted_first_coordinates_same_parity hn s t with hEven | hOdd
  · obtain ⟨⟨sx, hsx⟩, ⟨tx, htx⟩⟩ := hEven
    refine ⟨⟨sx + tx, sy + ty + 1, s.1.z + 2 * t.1.z⟩,
      ⟨sx - tx, sy - ty, s.1.z - 2 * t.1.z⟩, ?_, ?_, ?_, ?_⟩
    · constructor
      · dsimp [IsHalfSum, bLift, aLift]
        omega
      · constructor <;> dsimp [bLift, aLift] <;> omega
    · refine ⟨sz + t.1.z, ?_⟩
      dsimp
      omega
    · constructor
      · dsimp [IsHalfDiff, bLift, aLift]
        omega
      · constructor <;> dsimp [bLift, aLift] <;> omega
    · refine ⟨sz - t.1.z, ?_⟩
      dsimp
      omega
  · obtain ⟨⟨sx, hsx⟩, ⟨tx, htx⟩⟩ := hOdd
    refine ⟨⟨sx + tx + 1, sy + ty + 1, s.1.z + 2 * t.1.z⟩,
      ⟨sx - tx, sy - ty, s.1.z - 2 * t.1.z⟩, ?_, ?_, ?_, ?_⟩
    · constructor
      · dsimp [IsHalfSum, bLift, aLift]
        omega
      · constructor <;> dsimp [bLift, aLift] <;> omega
    · refine ⟨sz + t.1.z, ?_⟩
      dsimp
      omega
    · constructor
      · dsimp [IsHalfDiff, bLift, aLift]
        omega
      · constructor <;> dsimp [bLift, aLift] <;> omega
    · refine ⟨sz - t.1.z, ?_⟩
      dsimp
      omega
end TunnellMap
