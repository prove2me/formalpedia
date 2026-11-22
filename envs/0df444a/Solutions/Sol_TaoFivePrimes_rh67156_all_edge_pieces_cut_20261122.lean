-- Prove2me | solution 1 for TaoFivePrimes.rh67156_all_edge_pieces_cut_20261122
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-21T22:41:01.514176+00:00
-- url     : https://prove2.me/submissions/e984eef3-b023-405b-b828-47ce039c331e

import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_rh67156_edge_piece_group_00_20261122
import Theorems.Thm_TaoFivePrimes_rh67156_edge_piece_group_01_20261122
import Theorems.Thm_TaoFivePrimes_rh67156_edge_piece_group_02_20261122
import Theorems.Thm_TaoFivePrimes_rh67156_edge_piece_group_03_20261122
import Theorems.Thm_TaoFivePrimes_rh67156_edge_piece_group_04_20261122
import Theorems.Thm_TaoFivePrimes_rh67156_edge_piece_group_05_20261122
import Theorems.Thm_TaoFivePrimes_rh67156_edge_piece_group_06_20261122
import Theorems.Thm_TaoFivePrimes_rh67156_edge_piece_group_07_20261122
import Theorems.Thm_TaoFivePrimes_rh67156_edge_piece_group_08_20261122
set_option autoImplicit false
set_option maxHeartbeats 20000000
noncomputable section
theorem solution (j : ℕ) (hj : j < RH67156Edge.withBoxes.m) : H11K.pieceJ RH67156Edge.withBoxes j = true := by
  have hj41 : j < 41 := by simpa only [show RH67156Edge.withBoxes.m = 41 from rfl] using hj
  by_cases h0 : j < 5
  · exact TaoFivePrimes.rh67156_edge_piece_group_00_20261122 j (by omega) h0
  by_cases h1 : j < 10
  · exact TaoFivePrimes.rh67156_edge_piece_group_01_20261122 j (by omega) h1
  by_cases h2 : j < 15
  · exact TaoFivePrimes.rh67156_edge_piece_group_02_20261122 j (by omega) h2
  by_cases h3 : j < 20
  · exact TaoFivePrimes.rh67156_edge_piece_group_03_20261122 j (by omega) h3
  by_cases h4 : j < 25
  · exact TaoFivePrimes.rh67156_edge_piece_group_04_20261122 j (by omega) h4
  by_cases h5 : j < 30
  · exact TaoFivePrimes.rh67156_edge_piece_group_05_20261122 j (by omega) h5
  by_cases h6 : j < 35
  · exact TaoFivePrimes.rh67156_edge_piece_group_06_20261122 j (by omega) h6
  by_cases h7 : j < 40
  · exact TaoFivePrimes.rh67156_edge_piece_group_07_20261122 j (by omega) h7
  exact TaoFivePrimes.rh67156_edge_piece_group_08_20261122 j (by omega) hj41
