-- Prove2me | solution 1 for RHX100000.Edge.hAH
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T01:50:13.518497+00:00
-- url     : https://prove2.me/submissions/fbaba8eb-7930-4961-b286-04e6e9472ba8

import Theorems.Thm_H11K_edge_sound_of_split
import Theorems.Thm_RHX100000_Edge_piece_00
import Theorems.Thm_RHX100000_Edge_piece_01
import Theorems.Thm_RHX100000_Edge_piece_02
import Theorems.Thm_RHX100000_Edge_piece_03
import Theorems.Thm_RHX100000_Edge_piece_04
import Theorems.Thm_RHX100000_Edge_piece_05
import Theorems.Thm_RHX100000_Edge_piece_06
import Theorems.Thm_RHX100000_Edge_piece_07
import Theorems.Thm_RHX100000_Edge_piece_08
import Theorems.Thm_RHX100000_Edge_piece_09
import Theorems.Thm_RHX100000_Edge_piece_10
import Theorems.Thm_RHX100000_Edge_piece_11
import Theorems.Thm_RHX100000_Edge_piece_12
import Theorems.Thm_RHX100000_Edge_piece_13
import Theorems.Thm_RHX100000_Edge_piece_14
import Theorems.Thm_RHX100000_Edge_piece_15
import Theorems.Thm_RHX100000_Edge_piece_16
import Theorems.Thm_RHX100000_Edge_piece_17
import Theorems.Thm_RHX100000_Edge_piece_18
import Theorems.Thm_RHX100000_Edge_piece_19
import Theorems.Thm_RHX100000_Edge_piece_20
import Theorems.Thm_RHX100000_Edge_piece_21
import Theorems.Thm_RHX100000_Edge_piece_22
import Theorems.Thm_RHX100000_Edge_piece_23
import Theorems.Thm_RHX100000_Edge_piece_24
import Theorems.Thm_RHX100000_Edge_piece_25
import Theorems.Thm_RHX100000_Edge_piece_26
import Theorems.Thm_RHX100000_Edge_piece_27
import Theorems.Thm_RHX100000_Edge_piece_28
import Theorems.Thm_RHX100000_Edge_piece_29
import Theorems.Thm_RHX100000_Edge_piece_30
import Theorems.Thm_RHX100000_Edge_piece_31
import Theorems.Thm_RHX100000_Edge_piece_32
import Theorems.Thm_RHX100000_Edge_piece_33
import Theorems.Thm_RHX100000_Edge_piece_34
import Theorems.Thm_RHX100000_Edge_piece_35
import Theorems.Thm_RHX100000_Edge_piece_36
import Theorems.Thm_RHX100000_Edge_piece_37
import Theorems.Thm_RHX100000_Edge_piece_38
import Theorems.Thm_RHX100000_Edge_piece_39
import Theorems.Thm_RHX100000_Edge_piece_40
import Theorems.Thm_RHX100000_Edge_rest
import Theorems.Thm_RHX_cellOK_of
import Theorems.Thm_RHX_edgeRest_of
import Theorems.Thm_RHX_pieceJ_of
import Theorems.Thm_RHX_pieceOK_of
import Theorems.Thm_RHX_slabOK_of
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Arb4 Arb4.Q

/-- The horizontal argument change at height 100000, from the per-piece split
    (`H11K.edge_sound_of_split`): one kernel check per octant piece plus one for the rest. -/
theorem RHX100000.Edge.hAH :
    DiffractionCore.argChangeHoriz riemannZeta (100000 : ℝ) 2 (-1) ∈
      Set.Icc RHX100000.Edge.E.Lo.val RHX100000.Edge.E.Hi.val := by
  have hp : ∀ j, j < RHX100000.Edge.E.m → H11K.pieceJ RHX100000.Edge.E j = true := by
    intro j hj
    have hm : RHX100000.Edge.E.m = 41 := rfl
    rw [hm] at hj
    interval_cases j
    · exact RHX100000.Edge.piece_00
    · exact RHX100000.Edge.piece_01
    · exact RHX100000.Edge.piece_02
    · exact RHX100000.Edge.piece_03
    · exact RHX100000.Edge.piece_04
    · exact RHX100000.Edge.piece_05
    · exact RHX100000.Edge.piece_06
    · exact RHX100000.Edge.piece_07
    · exact RHX100000.Edge.piece_08
    · exact RHX100000.Edge.piece_09
    · exact RHX100000.Edge.piece_10
    · exact RHX100000.Edge.piece_11
    · exact RHX100000.Edge.piece_12
    · exact RHX100000.Edge.piece_13
    · exact RHX100000.Edge.piece_14
    · exact RHX100000.Edge.piece_15
    · exact RHX100000.Edge.piece_16
    · exact RHX100000.Edge.piece_17
    · exact RHX100000.Edge.piece_18
    · exact RHX100000.Edge.piece_19
    · exact RHX100000.Edge.piece_20
    · exact RHX100000.Edge.piece_21
    · exact RHX100000.Edge.piece_22
    · exact RHX100000.Edge.piece_23
    · exact RHX100000.Edge.piece_24
    · exact RHX100000.Edge.piece_25
    · exact RHX100000.Edge.piece_26
    · exact RHX100000.Edge.piece_27
    · exact RHX100000.Edge.piece_28
    · exact RHX100000.Edge.piece_29
    · exact RHX100000.Edge.piece_30
    · exact RHX100000.Edge.piece_31
    · exact RHX100000.Edge.piece_32
    · exact RHX100000.Edge.piece_33
    · exact RHX100000.Edge.piece_34
    · exact RHX100000.Edge.piece_35
    · exact RHX100000.Edge.piece_36
    · exact RHX100000.Edge.piece_37
    · exact RHX100000.Edge.piece_38
    · exact RHX100000.Edge.piece_39
    · exact RHX100000.Edge.piece_40
  have h := H11K.edge_sound_of_split RHX100000.Edge.E RHX100000.Edge.rest hp
  have hT : RHX100000.Edge.E.T = (100000 : ℝ) := by
    simp [Arb4.EdgeD.T, RHX100000.Edge.E]
  rw [hT] at h
  exact h
open Arb4 Arb4.Q in
theorem solution :
    DiffractionCore.argChangeHoriz riemannZeta (100000 : ℝ) 2 (-1) ∈
      Set.Icc RHX100000.Edge.E.Lo.val RHX100000.Edge.E.Hi.val := by
  apply RHX100000.Edge.hAH <;> assumption
