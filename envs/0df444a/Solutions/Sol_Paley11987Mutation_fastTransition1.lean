-- Prove2me | solution 1 for Paley11987Mutation.fastTransition1
-- status  : ACCEPTED   (prove)
-- author  : @rgmohan
-- created : 2026-10-27T08:26:16.303018+00:00
-- url     : https://prove2.me/submissions/d43ff0cf-f3c0-40e4-8a8c-43e39d3f8850

import Definitions.Def_Paley11987MutationFastData
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-! Kernel-only row-structured verification of fast transition phase 1.
Bounds on row variables ensure only the semantic profile coordinates are
reduced; each closed arithmetic goal is checked by `decide +kernel`. -/
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option autoImplicit false
set_option Elab.async false

open Paley11987Mutation

namespace Paley11987MutationFastProof1


theorem aRow0 (j : Nat) (lower : 0 ≤ j) (upper : j < 20) :
    ZP.rawA Paley11987MutationFast.stage1 recipe1 0 j ≤ ZP.A Paley11987MutationFast.stage2 0 j := by
  interval_cases j <;> decide +kernel

theorem aRow1 (j : Nat) (lower : 1 ≤ j) (upper : j < 20) :
    ZP.rawA Paley11987MutationFast.stage1 recipe1 1 j ≤ ZP.A Paley11987MutationFast.stage2 1 j := by
  interval_cases j <;> decide +kernel

theorem aRow2 (j : Nat) (lower : 2 ≤ j) (upper : j < 20) :
    ZP.rawA Paley11987MutationFast.stage1 recipe1 2 j ≤ ZP.A Paley11987MutationFast.stage2 2 j := by
  interval_cases j <;> decide +kernel

theorem aRow3 (j : Nat) (lower : 3 ≤ j) (upper : j < 20) :
    ZP.rawA Paley11987MutationFast.stage1 recipe1 3 j ≤ ZP.A Paley11987MutationFast.stage2 3 j := by
  interval_cases j <;> decide +kernel

theorem aRow4 (j : Nat) (lower : 4 ≤ j) (upper : j < 20) :
    ZP.rawA Paley11987MutationFast.stage1 recipe1 4 j ≤ ZP.A Paley11987MutationFast.stage2 4 j := by
  interval_cases j <;> decide +kernel

theorem aRow5 (j : Nat) (lower : 5 ≤ j) (upper : j < 20) :
    ZP.rawA Paley11987MutationFast.stage1 recipe1 5 j ≤ ZP.A Paley11987MutationFast.stage2 5 j := by
  interval_cases j <;> decide +kernel

theorem aRow6 (j : Nat) (lower : 6 ≤ j) (upper : j < 20) :
    ZP.rawA Paley11987MutationFast.stage1 recipe1 6 j ≤ ZP.A Paley11987MutationFast.stage2 6 j := by
  interval_cases j <;> decide +kernel

theorem aRow7 (j : Nat) (lower : 7 ≤ j) (upper : j < 20) :
    ZP.rawA Paley11987MutationFast.stage1 recipe1 7 j ≤ ZP.A Paley11987MutationFast.stage2 7 j := by
  interval_cases j <;> decide +kernel

theorem aRow8 (j : Nat) (lower : 8 ≤ j) (upper : j < 20) :
    ZP.rawA Paley11987MutationFast.stage1 recipe1 8 j ≤ ZP.A Paley11987MutationFast.stage2 8 j := by
  interval_cases j <;> decide +kernel

theorem aRow9 (j : Nat) (lower : 9 ≤ j) (upper : j < 20) :
    ZP.rawA Paley11987MutationFast.stage1 recipe1 9 j ≤ ZP.A Paley11987MutationFast.stage2 9 j := by
  interval_cases j <;> decide +kernel

theorem aRow10 (j : Nat) (lower : 10 ≤ j) (upper : j < 20) :
    ZP.rawA Paley11987MutationFast.stage1 recipe1 10 j ≤ ZP.A Paley11987MutationFast.stage2 10 j := by
  interval_cases j <;> decide +kernel

theorem aRow11 (j : Nat) (lower : 11 ≤ j) (upper : j < 20) :
    ZP.rawA Paley11987MutationFast.stage1 recipe1 11 j ≤ ZP.A Paley11987MutationFast.stage2 11 j := by
  interval_cases j <;> decide +kernel

theorem aRow12 (j : Nat) (lower : 12 ≤ j) (upper : j < 20) :
    ZP.rawA Paley11987MutationFast.stage1 recipe1 12 j ≤ ZP.A Paley11987MutationFast.stage2 12 j := by
  interval_cases j <;> decide +kernel

theorem aRow13 (j : Nat) (lower : 13 ≤ j) (upper : j < 20) :
    ZP.rawA Paley11987MutationFast.stage1 recipe1 13 j ≤ ZP.A Paley11987MutationFast.stage2 13 j := by
  interval_cases j <;> decide +kernel

theorem aRow14 (j : Nat) (lower : 14 ≤ j) (upper : j < 20) :
    ZP.rawA Paley11987MutationFast.stage1 recipe1 14 j ≤ ZP.A Paley11987MutationFast.stage2 14 j := by
  interval_cases j <;> decide +kernel

theorem aRow15 (j : Nat) (lower : 15 ≤ j) (upper : j < 20) :
    ZP.rawA Paley11987MutationFast.stage1 recipe1 15 j ≤ ZP.A Paley11987MutationFast.stage2 15 j := by
  interval_cases j <;> decide +kernel

theorem aRow16 (j : Nat) (lower : 16 ≤ j) (upper : j < 20) :
    ZP.rawA Paley11987MutationFast.stage1 recipe1 16 j ≤ ZP.A Paley11987MutationFast.stage2 16 j := by
  interval_cases j <;> decide +kernel

theorem aRow17 (j : Nat) (lower : 17 ≤ j) (upper : j < 20) :
    ZP.rawA Paley11987MutationFast.stage1 recipe1 17 j ≤ ZP.A Paley11987MutationFast.stage2 17 j := by
  interval_cases j <;> decide +kernel

theorem aRow18 (j : Nat) (lower : 18 ≤ j) (upper : j < 20) :
    ZP.rawA Paley11987MutationFast.stage1 recipe1 18 j ≤ ZP.A Paley11987MutationFast.stage2 18 j := by
  interval_cases j <;> decide +kernel

theorem aRow19 (j : Nat) (lower : 19 ≤ j) (upper : j < 20) :
    ZP.rawA Paley11987MutationFast.stage1 recipe1 19 j ≤ ZP.A Paley11987MutationFast.stage2 19 j := by
  interval_cases j <;> decide +kernel

theorem bRow0 (j : Nat) (lower : 0 ≤ j) (upper : j < 20) :
    ZP.rawB Paley11987MutationFast.stage1 recipe1 0 j ≤ ZP.B Paley11987MutationFast.stage2 0 j := by
  interval_cases j <;> decide +kernel

theorem bRow1 (j : Nat) (lower : 1 ≤ j) (upper : j < 20) :
    ZP.rawB Paley11987MutationFast.stage1 recipe1 1 j ≤ ZP.B Paley11987MutationFast.stage2 1 j := by
  interval_cases j <;> decide +kernel

theorem bRow2 (j : Nat) (lower : 2 ≤ j) (upper : j < 20) :
    ZP.rawB Paley11987MutationFast.stage1 recipe1 2 j ≤ ZP.B Paley11987MutationFast.stage2 2 j := by
  interval_cases j <;> decide +kernel

theorem bRow3 (j : Nat) (lower : 3 ≤ j) (upper : j < 20) :
    ZP.rawB Paley11987MutationFast.stage1 recipe1 3 j ≤ ZP.B Paley11987MutationFast.stage2 3 j := by
  interval_cases j <;> decide +kernel

theorem bRow4 (j : Nat) (lower : 4 ≤ j) (upper : j < 20) :
    ZP.rawB Paley11987MutationFast.stage1 recipe1 4 j ≤ ZP.B Paley11987MutationFast.stage2 4 j := by
  interval_cases j <;> decide +kernel

theorem bRow5 (j : Nat) (lower : 5 ≤ j) (upper : j < 20) :
    ZP.rawB Paley11987MutationFast.stage1 recipe1 5 j ≤ ZP.B Paley11987MutationFast.stage2 5 j := by
  interval_cases j <;> decide +kernel

theorem bRow6 (j : Nat) (lower : 6 ≤ j) (upper : j < 20) :
    ZP.rawB Paley11987MutationFast.stage1 recipe1 6 j ≤ ZP.B Paley11987MutationFast.stage2 6 j := by
  interval_cases j <;> decide +kernel

theorem bRow7 (j : Nat) (lower : 7 ≤ j) (upper : j < 20) :
    ZP.rawB Paley11987MutationFast.stage1 recipe1 7 j ≤ ZP.B Paley11987MutationFast.stage2 7 j := by
  interval_cases j <;> decide +kernel

theorem bRow8 (j : Nat) (lower : 8 ≤ j) (upper : j < 20) :
    ZP.rawB Paley11987MutationFast.stage1 recipe1 8 j ≤ ZP.B Paley11987MutationFast.stage2 8 j := by
  interval_cases j <;> decide +kernel

theorem bRow9 (j : Nat) (lower : 9 ≤ j) (upper : j < 20) :
    ZP.rawB Paley11987MutationFast.stage1 recipe1 9 j ≤ ZP.B Paley11987MutationFast.stage2 9 j := by
  interval_cases j <;> decide +kernel

theorem bRow10 (j : Nat) (lower : 10 ≤ j) (upper : j < 20) :
    ZP.rawB Paley11987MutationFast.stage1 recipe1 10 j ≤ ZP.B Paley11987MutationFast.stage2 10 j := by
  interval_cases j <;> decide +kernel

theorem bRow11 (j : Nat) (lower : 11 ≤ j) (upper : j < 20) :
    ZP.rawB Paley11987MutationFast.stage1 recipe1 11 j ≤ ZP.B Paley11987MutationFast.stage2 11 j := by
  interval_cases j <;> decide +kernel

theorem bRow12 (j : Nat) (lower : 12 ≤ j) (upper : j < 20) :
    ZP.rawB Paley11987MutationFast.stage1 recipe1 12 j ≤ ZP.B Paley11987MutationFast.stage2 12 j := by
  interval_cases j <;> decide +kernel

theorem bRow13 (j : Nat) (lower : 13 ≤ j) (upper : j < 20) :
    ZP.rawB Paley11987MutationFast.stage1 recipe1 13 j ≤ ZP.B Paley11987MutationFast.stage2 13 j := by
  interval_cases j <;> decide +kernel

theorem bRow14 (j : Nat) (lower : 14 ≤ j) (upper : j < 20) :
    ZP.rawB Paley11987MutationFast.stage1 recipe1 14 j ≤ ZP.B Paley11987MutationFast.stage2 14 j := by
  interval_cases j <;> decide +kernel

theorem bRow15 (j : Nat) (lower : 15 ≤ j) (upper : j < 20) :
    ZP.rawB Paley11987MutationFast.stage1 recipe1 15 j ≤ ZP.B Paley11987MutationFast.stage2 15 j := by
  interval_cases j <;> decide +kernel

theorem bRow16 (j : Nat) (lower : 16 ≤ j) (upper : j < 20) :
    ZP.rawB Paley11987MutationFast.stage1 recipe1 16 j ≤ ZP.B Paley11987MutationFast.stage2 16 j := by
  interval_cases j <;> decide +kernel

theorem bRow17 (j : Nat) (lower : 17 ≤ j) (upper : j < 20) :
    ZP.rawB Paley11987MutationFast.stage1 recipe1 17 j ≤ ZP.B Paley11987MutationFast.stage2 17 j := by
  interval_cases j <;> decide +kernel

theorem bRow18 (j : Nat) (lower : 18 ≤ j) (upper : j < 20) :
    ZP.rawB Paley11987MutationFast.stage1 recipe1 18 j ≤ ZP.B Paley11987MutationFast.stage2 18 j := by
  interval_cases j <;> decide +kernel

theorem bRow19 (j : Nat) (lower : 19 ≤ j) (upper : j < 20) :
    ZP.rawB Paley11987MutationFast.stage1 recipe1 19 j ≤ ZP.B Paley11987MutationFast.stage2 19 j := by
  interval_cases j <;> decide +kernel

theorem mRow0 (j : Nat) (lower : 0 ≤ j) (upper : j + 1 < 20) :
    ZP.rawM Paley11987MutationFast.stage1 recipe1 0 j ≤ ZP.M Paley11987MutationFast.stage2 0 j := by
  have jUpper : j < 19 := by omega
  interval_cases j <;> decide +kernel

theorem mRow1 (j : Nat) (lower : 1 ≤ j) (upper : j + 1 < 20) :
    ZP.rawM Paley11987MutationFast.stage1 recipe1 1 j ≤ ZP.M Paley11987MutationFast.stage2 1 j := by
  have jUpper : j < 19 := by omega
  interval_cases j <;> decide +kernel

theorem mRow2 (j : Nat) (lower : 2 ≤ j) (upper : j + 1 < 20) :
    ZP.rawM Paley11987MutationFast.stage1 recipe1 2 j ≤ ZP.M Paley11987MutationFast.stage2 2 j := by
  have jUpper : j < 19 := by omega
  interval_cases j <;> decide +kernel

theorem mRow3 (j : Nat) (lower : 3 ≤ j) (upper : j + 1 < 20) :
    ZP.rawM Paley11987MutationFast.stage1 recipe1 3 j ≤ ZP.M Paley11987MutationFast.stage2 3 j := by
  have jUpper : j < 19 := by omega
  interval_cases j <;> decide +kernel

theorem mRow4 (j : Nat) (lower : 4 ≤ j) (upper : j + 1 < 20) :
    ZP.rawM Paley11987MutationFast.stage1 recipe1 4 j ≤ ZP.M Paley11987MutationFast.stage2 4 j := by
  have jUpper : j < 19 := by omega
  interval_cases j <;> decide +kernel

theorem mRow5 (j : Nat) (lower : 5 ≤ j) (upper : j + 1 < 20) :
    ZP.rawM Paley11987MutationFast.stage1 recipe1 5 j ≤ ZP.M Paley11987MutationFast.stage2 5 j := by
  have jUpper : j < 19 := by omega
  interval_cases j <;> decide +kernel

theorem mRow6 (j : Nat) (lower : 6 ≤ j) (upper : j + 1 < 20) :
    ZP.rawM Paley11987MutationFast.stage1 recipe1 6 j ≤ ZP.M Paley11987MutationFast.stage2 6 j := by
  have jUpper : j < 19 := by omega
  interval_cases j <;> decide +kernel

theorem mRow7 (j : Nat) (lower : 7 ≤ j) (upper : j + 1 < 20) :
    ZP.rawM Paley11987MutationFast.stage1 recipe1 7 j ≤ ZP.M Paley11987MutationFast.stage2 7 j := by
  have jUpper : j < 19 := by omega
  interval_cases j <;> decide +kernel

theorem mRow8 (j : Nat) (lower : 8 ≤ j) (upper : j + 1 < 20) :
    ZP.rawM Paley11987MutationFast.stage1 recipe1 8 j ≤ ZP.M Paley11987MutationFast.stage2 8 j := by
  have jUpper : j < 19 := by omega
  interval_cases j <;> decide +kernel

theorem mRow9 (j : Nat) (lower : 9 ≤ j) (upper : j + 1 < 20) :
    ZP.rawM Paley11987MutationFast.stage1 recipe1 9 j ≤ ZP.M Paley11987MutationFast.stage2 9 j := by
  have jUpper : j < 19 := by omega
  interval_cases j <;> decide +kernel

theorem mRow10 (j : Nat) (lower : 10 ≤ j) (upper : j + 1 < 20) :
    ZP.rawM Paley11987MutationFast.stage1 recipe1 10 j ≤ ZP.M Paley11987MutationFast.stage2 10 j := by
  have jUpper : j < 19 := by omega
  interval_cases j <;> decide +kernel

theorem mRow11 (j : Nat) (lower : 11 ≤ j) (upper : j + 1 < 20) :
    ZP.rawM Paley11987MutationFast.stage1 recipe1 11 j ≤ ZP.M Paley11987MutationFast.stage2 11 j := by
  have jUpper : j < 19 := by omega
  interval_cases j <;> decide +kernel

theorem mRow12 (j : Nat) (lower : 12 ≤ j) (upper : j + 1 < 20) :
    ZP.rawM Paley11987MutationFast.stage1 recipe1 12 j ≤ ZP.M Paley11987MutationFast.stage2 12 j := by
  have jUpper : j < 19 := by omega
  interval_cases j <;> decide +kernel

theorem mRow13 (j : Nat) (lower : 13 ≤ j) (upper : j + 1 < 20) :
    ZP.rawM Paley11987MutationFast.stage1 recipe1 13 j ≤ ZP.M Paley11987MutationFast.stage2 13 j := by
  have jUpper : j < 19 := by omega
  interval_cases j <;> decide +kernel

theorem mRow14 (j : Nat) (lower : 14 ≤ j) (upper : j + 1 < 20) :
    ZP.rawM Paley11987MutationFast.stage1 recipe1 14 j ≤ ZP.M Paley11987MutationFast.stage2 14 j := by
  have jUpper : j < 19 := by omega
  interval_cases j <;> decide +kernel

theorem mRow15 (j : Nat) (lower : 15 ≤ j) (upper : j + 1 < 20) :
    ZP.rawM Paley11987MutationFast.stage1 recipe1 15 j ≤ ZP.M Paley11987MutationFast.stage2 15 j := by
  have jUpper : j < 19 := by omega
  interval_cases j <;> decide +kernel

theorem mRow16 (j : Nat) (lower : 16 ≤ j) (upper : j + 1 < 20) :
    ZP.rawM Paley11987MutationFast.stage1 recipe1 16 j ≤ ZP.M Paley11987MutationFast.stage2 16 j := by
  have jUpper : j < 19 := by omega
  interval_cases j <;> decide +kernel

theorem mRow17 (j : Nat) (lower : 17 ≤ j) (upper : j + 1 < 20) :
    ZP.rawM Paley11987MutationFast.stage1 recipe1 17 j ≤ ZP.M Paley11987MutationFast.stage2 17 j := by
  have jUpper : j < 19 := by omega
  interval_cases j <;> decide +kernel

theorem mRow18 (j : Nat) (lower : 18 ≤ j) (upper : j + 1 < 20) :
    ZP.rawM Paley11987MutationFast.stage1 recipe1 18 j ≤ ZP.M Paley11987MutationFast.stage2 18 j := by
  have jUpper : j < 19 := by omega
  interval_cases j <;> decide +kernel

theorem pRow0 (ell : Nat) (lower : 0 < ell) (upper : ell < 20) :
    ZP.rawP Paley11987MutationFast.stage1 recipe1 0 ell ≤ ZP.P Paley11987MutationFast.stage2 0 ell := by
  interval_cases ell <;> decide +kernel

theorem pRow1 (ell : Nat) (lower : 1 < ell) (upper : ell < 20) :
    ZP.rawP Paley11987MutationFast.stage1 recipe1 1 ell ≤ ZP.P Paley11987MutationFast.stage2 1 ell := by
  interval_cases ell <;> decide +kernel

theorem pRow2 (ell : Nat) (lower : 2 < ell) (upper : ell < 20) :
    ZP.rawP Paley11987MutationFast.stage1 recipe1 2 ell ≤ ZP.P Paley11987MutationFast.stage2 2 ell := by
  interval_cases ell <;> decide +kernel

theorem pRow3 (ell : Nat) (lower : 3 < ell) (upper : ell < 20) :
    ZP.rawP Paley11987MutationFast.stage1 recipe1 3 ell ≤ ZP.P Paley11987MutationFast.stage2 3 ell := by
  interval_cases ell <;> decide +kernel

theorem pRow4 (ell : Nat) (lower : 4 < ell) (upper : ell < 20) :
    ZP.rawP Paley11987MutationFast.stage1 recipe1 4 ell ≤ ZP.P Paley11987MutationFast.stage2 4 ell := by
  interval_cases ell <;> decide +kernel

theorem pRow5 (ell : Nat) (lower : 5 < ell) (upper : ell < 20) :
    ZP.rawP Paley11987MutationFast.stage1 recipe1 5 ell ≤ ZP.P Paley11987MutationFast.stage2 5 ell := by
  interval_cases ell <;> decide +kernel

theorem pRow6 (ell : Nat) (lower : 6 < ell) (upper : ell < 20) :
    ZP.rawP Paley11987MutationFast.stage1 recipe1 6 ell ≤ ZP.P Paley11987MutationFast.stage2 6 ell := by
  interval_cases ell <;> decide +kernel

theorem pRow7 (ell : Nat) (lower : 7 < ell) (upper : ell < 20) :
    ZP.rawP Paley11987MutationFast.stage1 recipe1 7 ell ≤ ZP.P Paley11987MutationFast.stage2 7 ell := by
  interval_cases ell <;> decide +kernel

theorem pRow8 (ell : Nat) (lower : 8 < ell) (upper : ell < 20) :
    ZP.rawP Paley11987MutationFast.stage1 recipe1 8 ell ≤ ZP.P Paley11987MutationFast.stage2 8 ell := by
  interval_cases ell <;> decide +kernel

theorem pRow9 (ell : Nat) (lower : 9 < ell) (upper : ell < 20) :
    ZP.rawP Paley11987MutationFast.stage1 recipe1 9 ell ≤ ZP.P Paley11987MutationFast.stage2 9 ell := by
  interval_cases ell <;> decide +kernel

theorem pRow10 (ell : Nat) (lower : 10 < ell) (upper : ell < 20) :
    ZP.rawP Paley11987MutationFast.stage1 recipe1 10 ell ≤ ZP.P Paley11987MutationFast.stage2 10 ell := by
  interval_cases ell <;> decide +kernel

theorem pRow11 (ell : Nat) (lower : 11 < ell) (upper : ell < 20) :
    ZP.rawP Paley11987MutationFast.stage1 recipe1 11 ell ≤ ZP.P Paley11987MutationFast.stage2 11 ell := by
  interval_cases ell <;> decide +kernel

theorem pRow12 (ell : Nat) (lower : 12 < ell) (upper : ell < 20) :
    ZP.rawP Paley11987MutationFast.stage1 recipe1 12 ell ≤ ZP.P Paley11987MutationFast.stage2 12 ell := by
  interval_cases ell <;> decide +kernel

theorem pRow13 (ell : Nat) (lower : 13 < ell) (upper : ell < 20) :
    ZP.rawP Paley11987MutationFast.stage1 recipe1 13 ell ≤ ZP.P Paley11987MutationFast.stage2 13 ell := by
  interval_cases ell <;> decide +kernel

theorem pRow14 (ell : Nat) (lower : 14 < ell) (upper : ell < 20) :
    ZP.rawP Paley11987MutationFast.stage1 recipe1 14 ell ≤ ZP.P Paley11987MutationFast.stage2 14 ell := by
  interval_cases ell <;> decide +kernel

theorem pRow15 (ell : Nat) (lower : 15 < ell) (upper : ell < 20) :
    ZP.rawP Paley11987MutationFast.stage1 recipe1 15 ell ≤ ZP.P Paley11987MutationFast.stage2 15 ell := by
  interval_cases ell <;> decide +kernel

theorem pRow16 (ell : Nat) (lower : 16 < ell) (upper : ell < 20) :
    ZP.rawP Paley11987MutationFast.stage1 recipe1 16 ell ≤ ZP.P Paley11987MutationFast.stage2 16 ell := by
  interval_cases ell <;> decide +kernel

theorem pRow17 (ell : Nat) (lower : 17 < ell) (upper : ell < 20) :
    ZP.rawP Paley11987MutationFast.stage1 recipe1 17 ell ≤ ZP.P Paley11987MutationFast.stage2 17 ell := by
  interval_cases ell <;> decide +kernel

theorem pRow18 (ell : Nat) (lower : 18 < ell) (upper : ell < 20) :
    ZP.rawP Paley11987MutationFast.stage1 recipe1 18 ell ≤ ZP.P Paley11987MutationFast.stage2 18 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow0_0 (ell : Nat) (lower : 0 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 0 0 ell ≤ ZP.D Paley11987MutationFast.stage2 0 0 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow0_1 (ell : Nat) (lower : 1 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 0 1 ell ≤ ZP.D Paley11987MutationFast.stage2 0 1 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow0_2 (ell : Nat) (lower : 2 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 0 2 ell ≤ ZP.D Paley11987MutationFast.stage2 0 2 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow0_3 (ell : Nat) (lower : 3 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 0 3 ell ≤ ZP.D Paley11987MutationFast.stage2 0 3 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow0_4 (ell : Nat) (lower : 4 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 0 4 ell ≤ ZP.D Paley11987MutationFast.stage2 0 4 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow0_5 (ell : Nat) (lower : 5 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 0 5 ell ≤ ZP.D Paley11987MutationFast.stage2 0 5 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow0_6 (ell : Nat) (lower : 6 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 0 6 ell ≤ ZP.D Paley11987MutationFast.stage2 0 6 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow0_7 (ell : Nat) (lower : 7 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 0 7 ell ≤ ZP.D Paley11987MutationFast.stage2 0 7 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow0_8 (ell : Nat) (lower : 8 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 0 8 ell ≤ ZP.D Paley11987MutationFast.stage2 0 8 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow0_9 (ell : Nat) (lower : 9 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 0 9 ell ≤ ZP.D Paley11987MutationFast.stage2 0 9 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow0_10 (ell : Nat) (lower : 10 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 0 10 ell ≤ ZP.D Paley11987MutationFast.stage2 0 10 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow0_11 (ell : Nat) (lower : 11 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 0 11 ell ≤ ZP.D Paley11987MutationFast.stage2 0 11 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow0_12 (ell : Nat) (lower : 12 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 0 12 ell ≤ ZP.D Paley11987MutationFast.stage2 0 12 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow0_13 (ell : Nat) (lower : 13 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 0 13 ell ≤ ZP.D Paley11987MutationFast.stage2 0 13 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow0_14 (ell : Nat) (lower : 14 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 0 14 ell ≤ ZP.D Paley11987MutationFast.stage2 0 14 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow0_15 (ell : Nat) (lower : 15 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 0 15 ell ≤ ZP.D Paley11987MutationFast.stage2 0 15 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow0_16 (ell : Nat) (lower : 16 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 0 16 ell ≤ ZP.D Paley11987MutationFast.stage2 0 16 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow0_17 (ell : Nat) (lower : 17 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 0 17 ell ≤ ZP.D Paley11987MutationFast.stage2 0 17 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow0_18 (ell : Nat) (lower : 18 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 0 18 ell ≤ ZP.D Paley11987MutationFast.stage2 0 18 ell := by
  interval_cases ell <;> decide +kernel

theorem dForI0 (j ell : Nat) (firstOrder : 0 ≤ j)
    (secondOrder : j < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 0 j ell ≤ ZP.D Paley11987MutationFast.stage2 0 j ell := by
  have jUpper : j < 19 := by omega
  interval_cases j
  · exact dRow0_0 ell secondOrder upper
  · exact dRow0_1 ell secondOrder upper
  · exact dRow0_2 ell secondOrder upper
  · exact dRow0_3 ell secondOrder upper
  · exact dRow0_4 ell secondOrder upper
  · exact dRow0_5 ell secondOrder upper
  · exact dRow0_6 ell secondOrder upper
  · exact dRow0_7 ell secondOrder upper
  · exact dRow0_8 ell secondOrder upper
  · exact dRow0_9 ell secondOrder upper
  · exact dRow0_10 ell secondOrder upper
  · exact dRow0_11 ell secondOrder upper
  · exact dRow0_12 ell secondOrder upper
  · exact dRow0_13 ell secondOrder upper
  · exact dRow0_14 ell secondOrder upper
  · exact dRow0_15 ell secondOrder upper
  · exact dRow0_16 ell secondOrder upper
  · exact dRow0_17 ell secondOrder upper
  · exact dRow0_18 ell secondOrder upper

theorem dRow1_1 (ell : Nat) (lower : 1 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 1 1 ell ≤ ZP.D Paley11987MutationFast.stage2 1 1 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow1_2 (ell : Nat) (lower : 2 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 1 2 ell ≤ ZP.D Paley11987MutationFast.stage2 1 2 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow1_3 (ell : Nat) (lower : 3 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 1 3 ell ≤ ZP.D Paley11987MutationFast.stage2 1 3 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow1_4 (ell : Nat) (lower : 4 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 1 4 ell ≤ ZP.D Paley11987MutationFast.stage2 1 4 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow1_5 (ell : Nat) (lower : 5 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 1 5 ell ≤ ZP.D Paley11987MutationFast.stage2 1 5 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow1_6 (ell : Nat) (lower : 6 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 1 6 ell ≤ ZP.D Paley11987MutationFast.stage2 1 6 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow1_7 (ell : Nat) (lower : 7 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 1 7 ell ≤ ZP.D Paley11987MutationFast.stage2 1 7 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow1_8 (ell : Nat) (lower : 8 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 1 8 ell ≤ ZP.D Paley11987MutationFast.stage2 1 8 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow1_9 (ell : Nat) (lower : 9 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 1 9 ell ≤ ZP.D Paley11987MutationFast.stage2 1 9 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow1_10 (ell : Nat) (lower : 10 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 1 10 ell ≤ ZP.D Paley11987MutationFast.stage2 1 10 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow1_11 (ell : Nat) (lower : 11 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 1 11 ell ≤ ZP.D Paley11987MutationFast.stage2 1 11 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow1_12 (ell : Nat) (lower : 12 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 1 12 ell ≤ ZP.D Paley11987MutationFast.stage2 1 12 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow1_13 (ell : Nat) (lower : 13 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 1 13 ell ≤ ZP.D Paley11987MutationFast.stage2 1 13 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow1_14 (ell : Nat) (lower : 14 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 1 14 ell ≤ ZP.D Paley11987MutationFast.stage2 1 14 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow1_15 (ell : Nat) (lower : 15 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 1 15 ell ≤ ZP.D Paley11987MutationFast.stage2 1 15 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow1_16 (ell : Nat) (lower : 16 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 1 16 ell ≤ ZP.D Paley11987MutationFast.stage2 1 16 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow1_17 (ell : Nat) (lower : 17 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 1 17 ell ≤ ZP.D Paley11987MutationFast.stage2 1 17 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow1_18 (ell : Nat) (lower : 18 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 1 18 ell ≤ ZP.D Paley11987MutationFast.stage2 1 18 ell := by
  interval_cases ell <;> decide +kernel

theorem dForI1 (j ell : Nat) (firstOrder : 1 ≤ j)
    (secondOrder : j < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 1 j ell ≤ ZP.D Paley11987MutationFast.stage2 1 j ell := by
  have jUpper : j < 19 := by omega
  interval_cases j
  · exact dRow1_1 ell secondOrder upper
  · exact dRow1_2 ell secondOrder upper
  · exact dRow1_3 ell secondOrder upper
  · exact dRow1_4 ell secondOrder upper
  · exact dRow1_5 ell secondOrder upper
  · exact dRow1_6 ell secondOrder upper
  · exact dRow1_7 ell secondOrder upper
  · exact dRow1_8 ell secondOrder upper
  · exact dRow1_9 ell secondOrder upper
  · exact dRow1_10 ell secondOrder upper
  · exact dRow1_11 ell secondOrder upper
  · exact dRow1_12 ell secondOrder upper
  · exact dRow1_13 ell secondOrder upper
  · exact dRow1_14 ell secondOrder upper
  · exact dRow1_15 ell secondOrder upper
  · exact dRow1_16 ell secondOrder upper
  · exact dRow1_17 ell secondOrder upper
  · exact dRow1_18 ell secondOrder upper

theorem dRow2_2 (ell : Nat) (lower : 2 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 2 2 ell ≤ ZP.D Paley11987MutationFast.stage2 2 2 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow2_3 (ell : Nat) (lower : 3 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 2 3 ell ≤ ZP.D Paley11987MutationFast.stage2 2 3 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow2_4 (ell : Nat) (lower : 4 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 2 4 ell ≤ ZP.D Paley11987MutationFast.stage2 2 4 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow2_5 (ell : Nat) (lower : 5 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 2 5 ell ≤ ZP.D Paley11987MutationFast.stage2 2 5 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow2_6 (ell : Nat) (lower : 6 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 2 6 ell ≤ ZP.D Paley11987MutationFast.stage2 2 6 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow2_7 (ell : Nat) (lower : 7 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 2 7 ell ≤ ZP.D Paley11987MutationFast.stage2 2 7 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow2_8 (ell : Nat) (lower : 8 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 2 8 ell ≤ ZP.D Paley11987MutationFast.stage2 2 8 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow2_9 (ell : Nat) (lower : 9 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 2 9 ell ≤ ZP.D Paley11987MutationFast.stage2 2 9 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow2_10 (ell : Nat) (lower : 10 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 2 10 ell ≤ ZP.D Paley11987MutationFast.stage2 2 10 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow2_11 (ell : Nat) (lower : 11 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 2 11 ell ≤ ZP.D Paley11987MutationFast.stage2 2 11 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow2_12 (ell : Nat) (lower : 12 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 2 12 ell ≤ ZP.D Paley11987MutationFast.stage2 2 12 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow2_13 (ell : Nat) (lower : 13 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 2 13 ell ≤ ZP.D Paley11987MutationFast.stage2 2 13 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow2_14 (ell : Nat) (lower : 14 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 2 14 ell ≤ ZP.D Paley11987MutationFast.stage2 2 14 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow2_15 (ell : Nat) (lower : 15 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 2 15 ell ≤ ZP.D Paley11987MutationFast.stage2 2 15 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow2_16 (ell : Nat) (lower : 16 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 2 16 ell ≤ ZP.D Paley11987MutationFast.stage2 2 16 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow2_17 (ell : Nat) (lower : 17 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 2 17 ell ≤ ZP.D Paley11987MutationFast.stage2 2 17 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow2_18 (ell : Nat) (lower : 18 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 2 18 ell ≤ ZP.D Paley11987MutationFast.stage2 2 18 ell := by
  interval_cases ell <;> decide +kernel

theorem dForI2 (j ell : Nat) (firstOrder : 2 ≤ j)
    (secondOrder : j < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 2 j ell ≤ ZP.D Paley11987MutationFast.stage2 2 j ell := by
  have jUpper : j < 19 := by omega
  interval_cases j
  · exact dRow2_2 ell secondOrder upper
  · exact dRow2_3 ell secondOrder upper
  · exact dRow2_4 ell secondOrder upper
  · exact dRow2_5 ell secondOrder upper
  · exact dRow2_6 ell secondOrder upper
  · exact dRow2_7 ell secondOrder upper
  · exact dRow2_8 ell secondOrder upper
  · exact dRow2_9 ell secondOrder upper
  · exact dRow2_10 ell secondOrder upper
  · exact dRow2_11 ell secondOrder upper
  · exact dRow2_12 ell secondOrder upper
  · exact dRow2_13 ell secondOrder upper
  · exact dRow2_14 ell secondOrder upper
  · exact dRow2_15 ell secondOrder upper
  · exact dRow2_16 ell secondOrder upper
  · exact dRow2_17 ell secondOrder upper
  · exact dRow2_18 ell secondOrder upper

theorem dRow3_3 (ell : Nat) (lower : 3 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 3 3 ell ≤ ZP.D Paley11987MutationFast.stage2 3 3 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow3_4 (ell : Nat) (lower : 4 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 3 4 ell ≤ ZP.D Paley11987MutationFast.stage2 3 4 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow3_5 (ell : Nat) (lower : 5 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 3 5 ell ≤ ZP.D Paley11987MutationFast.stage2 3 5 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow3_6 (ell : Nat) (lower : 6 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 3 6 ell ≤ ZP.D Paley11987MutationFast.stage2 3 6 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow3_7 (ell : Nat) (lower : 7 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 3 7 ell ≤ ZP.D Paley11987MutationFast.stage2 3 7 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow3_8 (ell : Nat) (lower : 8 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 3 8 ell ≤ ZP.D Paley11987MutationFast.stage2 3 8 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow3_9 (ell : Nat) (lower : 9 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 3 9 ell ≤ ZP.D Paley11987MutationFast.stage2 3 9 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow3_10 (ell : Nat) (lower : 10 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 3 10 ell ≤ ZP.D Paley11987MutationFast.stage2 3 10 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow3_11 (ell : Nat) (lower : 11 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 3 11 ell ≤ ZP.D Paley11987MutationFast.stage2 3 11 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow3_12 (ell : Nat) (lower : 12 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 3 12 ell ≤ ZP.D Paley11987MutationFast.stage2 3 12 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow3_13 (ell : Nat) (lower : 13 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 3 13 ell ≤ ZP.D Paley11987MutationFast.stage2 3 13 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow3_14 (ell : Nat) (lower : 14 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 3 14 ell ≤ ZP.D Paley11987MutationFast.stage2 3 14 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow3_15 (ell : Nat) (lower : 15 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 3 15 ell ≤ ZP.D Paley11987MutationFast.stage2 3 15 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow3_16 (ell : Nat) (lower : 16 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 3 16 ell ≤ ZP.D Paley11987MutationFast.stage2 3 16 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow3_17 (ell : Nat) (lower : 17 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 3 17 ell ≤ ZP.D Paley11987MutationFast.stage2 3 17 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow3_18 (ell : Nat) (lower : 18 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 3 18 ell ≤ ZP.D Paley11987MutationFast.stage2 3 18 ell := by
  interval_cases ell <;> decide +kernel

theorem dForI3 (j ell : Nat) (firstOrder : 3 ≤ j)
    (secondOrder : j < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 3 j ell ≤ ZP.D Paley11987MutationFast.stage2 3 j ell := by
  have jUpper : j < 19 := by omega
  interval_cases j
  · exact dRow3_3 ell secondOrder upper
  · exact dRow3_4 ell secondOrder upper
  · exact dRow3_5 ell secondOrder upper
  · exact dRow3_6 ell secondOrder upper
  · exact dRow3_7 ell secondOrder upper
  · exact dRow3_8 ell secondOrder upper
  · exact dRow3_9 ell secondOrder upper
  · exact dRow3_10 ell secondOrder upper
  · exact dRow3_11 ell secondOrder upper
  · exact dRow3_12 ell secondOrder upper
  · exact dRow3_13 ell secondOrder upper
  · exact dRow3_14 ell secondOrder upper
  · exact dRow3_15 ell secondOrder upper
  · exact dRow3_16 ell secondOrder upper
  · exact dRow3_17 ell secondOrder upper
  · exact dRow3_18 ell secondOrder upper

theorem dRow4_4 (ell : Nat) (lower : 4 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 4 4 ell ≤ ZP.D Paley11987MutationFast.stage2 4 4 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow4_5 (ell : Nat) (lower : 5 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 4 5 ell ≤ ZP.D Paley11987MutationFast.stage2 4 5 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow4_6 (ell : Nat) (lower : 6 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 4 6 ell ≤ ZP.D Paley11987MutationFast.stage2 4 6 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow4_7 (ell : Nat) (lower : 7 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 4 7 ell ≤ ZP.D Paley11987MutationFast.stage2 4 7 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow4_8 (ell : Nat) (lower : 8 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 4 8 ell ≤ ZP.D Paley11987MutationFast.stage2 4 8 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow4_9 (ell : Nat) (lower : 9 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 4 9 ell ≤ ZP.D Paley11987MutationFast.stage2 4 9 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow4_10 (ell : Nat) (lower : 10 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 4 10 ell ≤ ZP.D Paley11987MutationFast.stage2 4 10 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow4_11 (ell : Nat) (lower : 11 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 4 11 ell ≤ ZP.D Paley11987MutationFast.stage2 4 11 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow4_12 (ell : Nat) (lower : 12 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 4 12 ell ≤ ZP.D Paley11987MutationFast.stage2 4 12 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow4_13 (ell : Nat) (lower : 13 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 4 13 ell ≤ ZP.D Paley11987MutationFast.stage2 4 13 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow4_14 (ell : Nat) (lower : 14 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 4 14 ell ≤ ZP.D Paley11987MutationFast.stage2 4 14 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow4_15 (ell : Nat) (lower : 15 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 4 15 ell ≤ ZP.D Paley11987MutationFast.stage2 4 15 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow4_16 (ell : Nat) (lower : 16 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 4 16 ell ≤ ZP.D Paley11987MutationFast.stage2 4 16 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow4_17 (ell : Nat) (lower : 17 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 4 17 ell ≤ ZP.D Paley11987MutationFast.stage2 4 17 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow4_18 (ell : Nat) (lower : 18 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 4 18 ell ≤ ZP.D Paley11987MutationFast.stage2 4 18 ell := by
  interval_cases ell <;> decide +kernel

theorem dForI4 (j ell : Nat) (firstOrder : 4 ≤ j)
    (secondOrder : j < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 4 j ell ≤ ZP.D Paley11987MutationFast.stage2 4 j ell := by
  have jUpper : j < 19 := by omega
  interval_cases j
  · exact dRow4_4 ell secondOrder upper
  · exact dRow4_5 ell secondOrder upper
  · exact dRow4_6 ell secondOrder upper
  · exact dRow4_7 ell secondOrder upper
  · exact dRow4_8 ell secondOrder upper
  · exact dRow4_9 ell secondOrder upper
  · exact dRow4_10 ell secondOrder upper
  · exact dRow4_11 ell secondOrder upper
  · exact dRow4_12 ell secondOrder upper
  · exact dRow4_13 ell secondOrder upper
  · exact dRow4_14 ell secondOrder upper
  · exact dRow4_15 ell secondOrder upper
  · exact dRow4_16 ell secondOrder upper
  · exact dRow4_17 ell secondOrder upper
  · exact dRow4_18 ell secondOrder upper

theorem dRow5_5 (ell : Nat) (lower : 5 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 5 5 ell ≤ ZP.D Paley11987MutationFast.stage2 5 5 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow5_6 (ell : Nat) (lower : 6 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 5 6 ell ≤ ZP.D Paley11987MutationFast.stage2 5 6 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow5_7 (ell : Nat) (lower : 7 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 5 7 ell ≤ ZP.D Paley11987MutationFast.stage2 5 7 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow5_8 (ell : Nat) (lower : 8 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 5 8 ell ≤ ZP.D Paley11987MutationFast.stage2 5 8 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow5_9 (ell : Nat) (lower : 9 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 5 9 ell ≤ ZP.D Paley11987MutationFast.stage2 5 9 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow5_10 (ell : Nat) (lower : 10 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 5 10 ell ≤ ZP.D Paley11987MutationFast.stage2 5 10 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow5_11 (ell : Nat) (lower : 11 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 5 11 ell ≤ ZP.D Paley11987MutationFast.stage2 5 11 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow5_12 (ell : Nat) (lower : 12 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 5 12 ell ≤ ZP.D Paley11987MutationFast.stage2 5 12 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow5_13 (ell : Nat) (lower : 13 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 5 13 ell ≤ ZP.D Paley11987MutationFast.stage2 5 13 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow5_14 (ell : Nat) (lower : 14 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 5 14 ell ≤ ZP.D Paley11987MutationFast.stage2 5 14 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow5_15 (ell : Nat) (lower : 15 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 5 15 ell ≤ ZP.D Paley11987MutationFast.stage2 5 15 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow5_16 (ell : Nat) (lower : 16 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 5 16 ell ≤ ZP.D Paley11987MutationFast.stage2 5 16 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow5_17 (ell : Nat) (lower : 17 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 5 17 ell ≤ ZP.D Paley11987MutationFast.stage2 5 17 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow5_18 (ell : Nat) (lower : 18 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 5 18 ell ≤ ZP.D Paley11987MutationFast.stage2 5 18 ell := by
  interval_cases ell <;> decide +kernel

theorem dForI5 (j ell : Nat) (firstOrder : 5 ≤ j)
    (secondOrder : j < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 5 j ell ≤ ZP.D Paley11987MutationFast.stage2 5 j ell := by
  have jUpper : j < 19 := by omega
  interval_cases j
  · exact dRow5_5 ell secondOrder upper
  · exact dRow5_6 ell secondOrder upper
  · exact dRow5_7 ell secondOrder upper
  · exact dRow5_8 ell secondOrder upper
  · exact dRow5_9 ell secondOrder upper
  · exact dRow5_10 ell secondOrder upper
  · exact dRow5_11 ell secondOrder upper
  · exact dRow5_12 ell secondOrder upper
  · exact dRow5_13 ell secondOrder upper
  · exact dRow5_14 ell secondOrder upper
  · exact dRow5_15 ell secondOrder upper
  · exact dRow5_16 ell secondOrder upper
  · exact dRow5_17 ell secondOrder upper
  · exact dRow5_18 ell secondOrder upper

theorem dRow6_6 (ell : Nat) (lower : 6 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 6 6 ell ≤ ZP.D Paley11987MutationFast.stage2 6 6 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow6_7 (ell : Nat) (lower : 7 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 6 7 ell ≤ ZP.D Paley11987MutationFast.stage2 6 7 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow6_8 (ell : Nat) (lower : 8 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 6 8 ell ≤ ZP.D Paley11987MutationFast.stage2 6 8 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow6_9 (ell : Nat) (lower : 9 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 6 9 ell ≤ ZP.D Paley11987MutationFast.stage2 6 9 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow6_10 (ell : Nat) (lower : 10 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 6 10 ell ≤ ZP.D Paley11987MutationFast.stage2 6 10 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow6_11 (ell : Nat) (lower : 11 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 6 11 ell ≤ ZP.D Paley11987MutationFast.stage2 6 11 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow6_12 (ell : Nat) (lower : 12 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 6 12 ell ≤ ZP.D Paley11987MutationFast.stage2 6 12 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow6_13 (ell : Nat) (lower : 13 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 6 13 ell ≤ ZP.D Paley11987MutationFast.stage2 6 13 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow6_14 (ell : Nat) (lower : 14 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 6 14 ell ≤ ZP.D Paley11987MutationFast.stage2 6 14 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow6_15 (ell : Nat) (lower : 15 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 6 15 ell ≤ ZP.D Paley11987MutationFast.stage2 6 15 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow6_16 (ell : Nat) (lower : 16 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 6 16 ell ≤ ZP.D Paley11987MutationFast.stage2 6 16 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow6_17 (ell : Nat) (lower : 17 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 6 17 ell ≤ ZP.D Paley11987MutationFast.stage2 6 17 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow6_18 (ell : Nat) (lower : 18 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 6 18 ell ≤ ZP.D Paley11987MutationFast.stage2 6 18 ell := by
  interval_cases ell <;> decide +kernel

theorem dForI6 (j ell : Nat) (firstOrder : 6 ≤ j)
    (secondOrder : j < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 6 j ell ≤ ZP.D Paley11987MutationFast.stage2 6 j ell := by
  have jUpper : j < 19 := by omega
  interval_cases j
  · exact dRow6_6 ell secondOrder upper
  · exact dRow6_7 ell secondOrder upper
  · exact dRow6_8 ell secondOrder upper
  · exact dRow6_9 ell secondOrder upper
  · exact dRow6_10 ell secondOrder upper
  · exact dRow6_11 ell secondOrder upper
  · exact dRow6_12 ell secondOrder upper
  · exact dRow6_13 ell secondOrder upper
  · exact dRow6_14 ell secondOrder upper
  · exact dRow6_15 ell secondOrder upper
  · exact dRow6_16 ell secondOrder upper
  · exact dRow6_17 ell secondOrder upper
  · exact dRow6_18 ell secondOrder upper

theorem dRow7_7 (ell : Nat) (lower : 7 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 7 7 ell ≤ ZP.D Paley11987MutationFast.stage2 7 7 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow7_8 (ell : Nat) (lower : 8 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 7 8 ell ≤ ZP.D Paley11987MutationFast.stage2 7 8 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow7_9 (ell : Nat) (lower : 9 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 7 9 ell ≤ ZP.D Paley11987MutationFast.stage2 7 9 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow7_10 (ell : Nat) (lower : 10 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 7 10 ell ≤ ZP.D Paley11987MutationFast.stage2 7 10 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow7_11 (ell : Nat) (lower : 11 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 7 11 ell ≤ ZP.D Paley11987MutationFast.stage2 7 11 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow7_12 (ell : Nat) (lower : 12 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 7 12 ell ≤ ZP.D Paley11987MutationFast.stage2 7 12 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow7_13 (ell : Nat) (lower : 13 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 7 13 ell ≤ ZP.D Paley11987MutationFast.stage2 7 13 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow7_14 (ell : Nat) (lower : 14 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 7 14 ell ≤ ZP.D Paley11987MutationFast.stage2 7 14 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow7_15 (ell : Nat) (lower : 15 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 7 15 ell ≤ ZP.D Paley11987MutationFast.stage2 7 15 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow7_16 (ell : Nat) (lower : 16 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 7 16 ell ≤ ZP.D Paley11987MutationFast.stage2 7 16 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow7_17 (ell : Nat) (lower : 17 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 7 17 ell ≤ ZP.D Paley11987MutationFast.stage2 7 17 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow7_18 (ell : Nat) (lower : 18 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 7 18 ell ≤ ZP.D Paley11987MutationFast.stage2 7 18 ell := by
  interval_cases ell <;> decide +kernel

theorem dForI7 (j ell : Nat) (firstOrder : 7 ≤ j)
    (secondOrder : j < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 7 j ell ≤ ZP.D Paley11987MutationFast.stage2 7 j ell := by
  have jUpper : j < 19 := by omega
  interval_cases j
  · exact dRow7_7 ell secondOrder upper
  · exact dRow7_8 ell secondOrder upper
  · exact dRow7_9 ell secondOrder upper
  · exact dRow7_10 ell secondOrder upper
  · exact dRow7_11 ell secondOrder upper
  · exact dRow7_12 ell secondOrder upper
  · exact dRow7_13 ell secondOrder upper
  · exact dRow7_14 ell secondOrder upper
  · exact dRow7_15 ell secondOrder upper
  · exact dRow7_16 ell secondOrder upper
  · exact dRow7_17 ell secondOrder upper
  · exact dRow7_18 ell secondOrder upper

theorem dRow8_8 (ell : Nat) (lower : 8 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 8 8 ell ≤ ZP.D Paley11987MutationFast.stage2 8 8 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow8_9 (ell : Nat) (lower : 9 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 8 9 ell ≤ ZP.D Paley11987MutationFast.stage2 8 9 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow8_10 (ell : Nat) (lower : 10 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 8 10 ell ≤ ZP.D Paley11987MutationFast.stage2 8 10 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow8_11 (ell : Nat) (lower : 11 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 8 11 ell ≤ ZP.D Paley11987MutationFast.stage2 8 11 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow8_12 (ell : Nat) (lower : 12 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 8 12 ell ≤ ZP.D Paley11987MutationFast.stage2 8 12 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow8_13 (ell : Nat) (lower : 13 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 8 13 ell ≤ ZP.D Paley11987MutationFast.stage2 8 13 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow8_14 (ell : Nat) (lower : 14 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 8 14 ell ≤ ZP.D Paley11987MutationFast.stage2 8 14 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow8_15 (ell : Nat) (lower : 15 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 8 15 ell ≤ ZP.D Paley11987MutationFast.stage2 8 15 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow8_16 (ell : Nat) (lower : 16 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 8 16 ell ≤ ZP.D Paley11987MutationFast.stage2 8 16 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow8_17 (ell : Nat) (lower : 17 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 8 17 ell ≤ ZP.D Paley11987MutationFast.stage2 8 17 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow8_18 (ell : Nat) (lower : 18 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 8 18 ell ≤ ZP.D Paley11987MutationFast.stage2 8 18 ell := by
  interval_cases ell <;> decide +kernel

theorem dForI8 (j ell : Nat) (firstOrder : 8 ≤ j)
    (secondOrder : j < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 8 j ell ≤ ZP.D Paley11987MutationFast.stage2 8 j ell := by
  have jUpper : j < 19 := by omega
  interval_cases j
  · exact dRow8_8 ell secondOrder upper
  · exact dRow8_9 ell secondOrder upper
  · exact dRow8_10 ell secondOrder upper
  · exact dRow8_11 ell secondOrder upper
  · exact dRow8_12 ell secondOrder upper
  · exact dRow8_13 ell secondOrder upper
  · exact dRow8_14 ell secondOrder upper
  · exact dRow8_15 ell secondOrder upper
  · exact dRow8_16 ell secondOrder upper
  · exact dRow8_17 ell secondOrder upper
  · exact dRow8_18 ell secondOrder upper

theorem dRow9_9 (ell : Nat) (lower : 9 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 9 9 ell ≤ ZP.D Paley11987MutationFast.stage2 9 9 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow9_10 (ell : Nat) (lower : 10 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 9 10 ell ≤ ZP.D Paley11987MutationFast.stage2 9 10 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow9_11 (ell : Nat) (lower : 11 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 9 11 ell ≤ ZP.D Paley11987MutationFast.stage2 9 11 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow9_12 (ell : Nat) (lower : 12 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 9 12 ell ≤ ZP.D Paley11987MutationFast.stage2 9 12 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow9_13 (ell : Nat) (lower : 13 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 9 13 ell ≤ ZP.D Paley11987MutationFast.stage2 9 13 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow9_14 (ell : Nat) (lower : 14 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 9 14 ell ≤ ZP.D Paley11987MutationFast.stage2 9 14 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow9_15 (ell : Nat) (lower : 15 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 9 15 ell ≤ ZP.D Paley11987MutationFast.stage2 9 15 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow9_16 (ell : Nat) (lower : 16 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 9 16 ell ≤ ZP.D Paley11987MutationFast.stage2 9 16 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow9_17 (ell : Nat) (lower : 17 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 9 17 ell ≤ ZP.D Paley11987MutationFast.stage2 9 17 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow9_18 (ell : Nat) (lower : 18 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 9 18 ell ≤ ZP.D Paley11987MutationFast.stage2 9 18 ell := by
  interval_cases ell <;> decide +kernel

theorem dForI9 (j ell : Nat) (firstOrder : 9 ≤ j)
    (secondOrder : j < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 9 j ell ≤ ZP.D Paley11987MutationFast.stage2 9 j ell := by
  have jUpper : j < 19 := by omega
  interval_cases j
  · exact dRow9_9 ell secondOrder upper
  · exact dRow9_10 ell secondOrder upper
  · exact dRow9_11 ell secondOrder upper
  · exact dRow9_12 ell secondOrder upper
  · exact dRow9_13 ell secondOrder upper
  · exact dRow9_14 ell secondOrder upper
  · exact dRow9_15 ell secondOrder upper
  · exact dRow9_16 ell secondOrder upper
  · exact dRow9_17 ell secondOrder upper
  · exact dRow9_18 ell secondOrder upper

theorem dRow10_10 (ell : Nat) (lower : 10 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 10 10 ell ≤ ZP.D Paley11987MutationFast.stage2 10 10 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow10_11 (ell : Nat) (lower : 11 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 10 11 ell ≤ ZP.D Paley11987MutationFast.stage2 10 11 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow10_12 (ell : Nat) (lower : 12 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 10 12 ell ≤ ZP.D Paley11987MutationFast.stage2 10 12 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow10_13 (ell : Nat) (lower : 13 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 10 13 ell ≤ ZP.D Paley11987MutationFast.stage2 10 13 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow10_14 (ell : Nat) (lower : 14 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 10 14 ell ≤ ZP.D Paley11987MutationFast.stage2 10 14 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow10_15 (ell : Nat) (lower : 15 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 10 15 ell ≤ ZP.D Paley11987MutationFast.stage2 10 15 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow10_16 (ell : Nat) (lower : 16 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 10 16 ell ≤ ZP.D Paley11987MutationFast.stage2 10 16 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow10_17 (ell : Nat) (lower : 17 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 10 17 ell ≤ ZP.D Paley11987MutationFast.stage2 10 17 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow10_18 (ell : Nat) (lower : 18 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 10 18 ell ≤ ZP.D Paley11987MutationFast.stage2 10 18 ell := by
  interval_cases ell <;> decide +kernel

theorem dForI10 (j ell : Nat) (firstOrder : 10 ≤ j)
    (secondOrder : j < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 10 j ell ≤ ZP.D Paley11987MutationFast.stage2 10 j ell := by
  have jUpper : j < 19 := by omega
  interval_cases j
  · exact dRow10_10 ell secondOrder upper
  · exact dRow10_11 ell secondOrder upper
  · exact dRow10_12 ell secondOrder upper
  · exact dRow10_13 ell secondOrder upper
  · exact dRow10_14 ell secondOrder upper
  · exact dRow10_15 ell secondOrder upper
  · exact dRow10_16 ell secondOrder upper
  · exact dRow10_17 ell secondOrder upper
  · exact dRow10_18 ell secondOrder upper

theorem dRow11_11 (ell : Nat) (lower : 11 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 11 11 ell ≤ ZP.D Paley11987MutationFast.stage2 11 11 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow11_12 (ell : Nat) (lower : 12 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 11 12 ell ≤ ZP.D Paley11987MutationFast.stage2 11 12 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow11_13 (ell : Nat) (lower : 13 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 11 13 ell ≤ ZP.D Paley11987MutationFast.stage2 11 13 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow11_14 (ell : Nat) (lower : 14 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 11 14 ell ≤ ZP.D Paley11987MutationFast.stage2 11 14 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow11_15 (ell : Nat) (lower : 15 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 11 15 ell ≤ ZP.D Paley11987MutationFast.stage2 11 15 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow11_16 (ell : Nat) (lower : 16 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 11 16 ell ≤ ZP.D Paley11987MutationFast.stage2 11 16 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow11_17 (ell : Nat) (lower : 17 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 11 17 ell ≤ ZP.D Paley11987MutationFast.stage2 11 17 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow11_18 (ell : Nat) (lower : 18 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 11 18 ell ≤ ZP.D Paley11987MutationFast.stage2 11 18 ell := by
  interval_cases ell <;> decide +kernel

theorem dForI11 (j ell : Nat) (firstOrder : 11 ≤ j)
    (secondOrder : j < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 11 j ell ≤ ZP.D Paley11987MutationFast.stage2 11 j ell := by
  have jUpper : j < 19 := by omega
  interval_cases j
  · exact dRow11_11 ell secondOrder upper
  · exact dRow11_12 ell secondOrder upper
  · exact dRow11_13 ell secondOrder upper
  · exact dRow11_14 ell secondOrder upper
  · exact dRow11_15 ell secondOrder upper
  · exact dRow11_16 ell secondOrder upper
  · exact dRow11_17 ell secondOrder upper
  · exact dRow11_18 ell secondOrder upper

theorem dRow12_12 (ell : Nat) (lower : 12 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 12 12 ell ≤ ZP.D Paley11987MutationFast.stage2 12 12 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow12_13 (ell : Nat) (lower : 13 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 12 13 ell ≤ ZP.D Paley11987MutationFast.stage2 12 13 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow12_14 (ell : Nat) (lower : 14 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 12 14 ell ≤ ZP.D Paley11987MutationFast.stage2 12 14 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow12_15 (ell : Nat) (lower : 15 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 12 15 ell ≤ ZP.D Paley11987MutationFast.stage2 12 15 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow12_16 (ell : Nat) (lower : 16 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 12 16 ell ≤ ZP.D Paley11987MutationFast.stage2 12 16 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow12_17 (ell : Nat) (lower : 17 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 12 17 ell ≤ ZP.D Paley11987MutationFast.stage2 12 17 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow12_18 (ell : Nat) (lower : 18 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 12 18 ell ≤ ZP.D Paley11987MutationFast.stage2 12 18 ell := by
  interval_cases ell <;> decide +kernel

theorem dForI12 (j ell : Nat) (firstOrder : 12 ≤ j)
    (secondOrder : j < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 12 j ell ≤ ZP.D Paley11987MutationFast.stage2 12 j ell := by
  have jUpper : j < 19 := by omega
  interval_cases j
  · exact dRow12_12 ell secondOrder upper
  · exact dRow12_13 ell secondOrder upper
  · exact dRow12_14 ell secondOrder upper
  · exact dRow12_15 ell secondOrder upper
  · exact dRow12_16 ell secondOrder upper
  · exact dRow12_17 ell secondOrder upper
  · exact dRow12_18 ell secondOrder upper

theorem dRow13_13 (ell : Nat) (lower : 13 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 13 13 ell ≤ ZP.D Paley11987MutationFast.stage2 13 13 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow13_14 (ell : Nat) (lower : 14 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 13 14 ell ≤ ZP.D Paley11987MutationFast.stage2 13 14 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow13_15 (ell : Nat) (lower : 15 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 13 15 ell ≤ ZP.D Paley11987MutationFast.stage2 13 15 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow13_16 (ell : Nat) (lower : 16 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 13 16 ell ≤ ZP.D Paley11987MutationFast.stage2 13 16 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow13_17 (ell : Nat) (lower : 17 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 13 17 ell ≤ ZP.D Paley11987MutationFast.stage2 13 17 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow13_18 (ell : Nat) (lower : 18 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 13 18 ell ≤ ZP.D Paley11987MutationFast.stage2 13 18 ell := by
  interval_cases ell <;> decide +kernel

theorem dForI13 (j ell : Nat) (firstOrder : 13 ≤ j)
    (secondOrder : j < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 13 j ell ≤ ZP.D Paley11987MutationFast.stage2 13 j ell := by
  have jUpper : j < 19 := by omega
  interval_cases j
  · exact dRow13_13 ell secondOrder upper
  · exact dRow13_14 ell secondOrder upper
  · exact dRow13_15 ell secondOrder upper
  · exact dRow13_16 ell secondOrder upper
  · exact dRow13_17 ell secondOrder upper
  · exact dRow13_18 ell secondOrder upper

theorem dRow14_14 (ell : Nat) (lower : 14 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 14 14 ell ≤ ZP.D Paley11987MutationFast.stage2 14 14 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow14_15 (ell : Nat) (lower : 15 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 14 15 ell ≤ ZP.D Paley11987MutationFast.stage2 14 15 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow14_16 (ell : Nat) (lower : 16 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 14 16 ell ≤ ZP.D Paley11987MutationFast.stage2 14 16 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow14_17 (ell : Nat) (lower : 17 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 14 17 ell ≤ ZP.D Paley11987MutationFast.stage2 14 17 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow14_18 (ell : Nat) (lower : 18 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 14 18 ell ≤ ZP.D Paley11987MutationFast.stage2 14 18 ell := by
  interval_cases ell <;> decide +kernel

theorem dForI14 (j ell : Nat) (firstOrder : 14 ≤ j)
    (secondOrder : j < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 14 j ell ≤ ZP.D Paley11987MutationFast.stage2 14 j ell := by
  have jUpper : j < 19 := by omega
  interval_cases j
  · exact dRow14_14 ell secondOrder upper
  · exact dRow14_15 ell secondOrder upper
  · exact dRow14_16 ell secondOrder upper
  · exact dRow14_17 ell secondOrder upper
  · exact dRow14_18 ell secondOrder upper

theorem dRow15_15 (ell : Nat) (lower : 15 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 15 15 ell ≤ ZP.D Paley11987MutationFast.stage2 15 15 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow15_16 (ell : Nat) (lower : 16 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 15 16 ell ≤ ZP.D Paley11987MutationFast.stage2 15 16 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow15_17 (ell : Nat) (lower : 17 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 15 17 ell ≤ ZP.D Paley11987MutationFast.stage2 15 17 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow15_18 (ell : Nat) (lower : 18 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 15 18 ell ≤ ZP.D Paley11987MutationFast.stage2 15 18 ell := by
  interval_cases ell <;> decide +kernel

theorem dForI15 (j ell : Nat) (firstOrder : 15 ≤ j)
    (secondOrder : j < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 15 j ell ≤ ZP.D Paley11987MutationFast.stage2 15 j ell := by
  have jUpper : j < 19 := by omega
  interval_cases j
  · exact dRow15_15 ell secondOrder upper
  · exact dRow15_16 ell secondOrder upper
  · exact dRow15_17 ell secondOrder upper
  · exact dRow15_18 ell secondOrder upper

theorem dRow16_16 (ell : Nat) (lower : 16 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 16 16 ell ≤ ZP.D Paley11987MutationFast.stage2 16 16 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow16_17 (ell : Nat) (lower : 17 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 16 17 ell ≤ ZP.D Paley11987MutationFast.stage2 16 17 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow16_18 (ell : Nat) (lower : 18 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 16 18 ell ≤ ZP.D Paley11987MutationFast.stage2 16 18 ell := by
  interval_cases ell <;> decide +kernel

theorem dForI16 (j ell : Nat) (firstOrder : 16 ≤ j)
    (secondOrder : j < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 16 j ell ≤ ZP.D Paley11987MutationFast.stage2 16 j ell := by
  have jUpper : j < 19 := by omega
  interval_cases j
  · exact dRow16_16 ell secondOrder upper
  · exact dRow16_17 ell secondOrder upper
  · exact dRow16_18 ell secondOrder upper

theorem dRow17_17 (ell : Nat) (lower : 17 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 17 17 ell ≤ ZP.D Paley11987MutationFast.stage2 17 17 ell := by
  interval_cases ell <;> decide +kernel

theorem dRow17_18 (ell : Nat) (lower : 18 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 17 18 ell ≤ ZP.D Paley11987MutationFast.stage2 17 18 ell := by
  interval_cases ell <;> decide +kernel

theorem dForI17 (j ell : Nat) (firstOrder : 17 ≤ j)
    (secondOrder : j < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 17 j ell ≤ ZP.D Paley11987MutationFast.stage2 17 j ell := by
  have jUpper : j < 19 := by omega
  interval_cases j
  · exact dRow17_17 ell secondOrder upper
  · exact dRow17_18 ell secondOrder upper

theorem dRow18_18 (ell : Nat) (lower : 18 < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 18 18 ell ≤ ZP.D Paley11987MutationFast.stage2 18 18 ell := by
  interval_cases ell <;> decide +kernel

theorem dForI18 (j ell : Nat) (firstOrder : 18 ≤ j)
    (secondOrder : j < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 18 j ell ≤ ZP.D Paley11987MutationFast.stage2 18 j ell := by
  have jUpper : j < 19 := by omega
  interval_cases j
  · exact dRow18_18 ell secondOrder upper

theorem aAll (i j : Nat) (iUpper : i < 20)
    (firstOrder : i ≤ j) (upper : j < 20) :
    ZP.rawA Paley11987MutationFast.stage1 recipe1 i j ≤ ZP.A Paley11987MutationFast.stage2 i j := by
  interval_cases i
  · exact aRow0 j firstOrder upper
  · exact aRow1 j firstOrder upper
  · exact aRow2 j firstOrder upper
  · exact aRow3 j firstOrder upper
  · exact aRow4 j firstOrder upper
  · exact aRow5 j firstOrder upper
  · exact aRow6 j firstOrder upper
  · exact aRow7 j firstOrder upper
  · exact aRow8 j firstOrder upper
  · exact aRow9 j firstOrder upper
  · exact aRow10 j firstOrder upper
  · exact aRow11 j firstOrder upper
  · exact aRow12 j firstOrder upper
  · exact aRow13 j firstOrder upper
  · exact aRow14 j firstOrder upper
  · exact aRow15 j firstOrder upper
  · exact aRow16 j firstOrder upper
  · exact aRow17 j firstOrder upper
  · exact aRow18 j firstOrder upper
  · exact aRow19 j firstOrder upper

theorem bAll (i j : Nat) (iUpper : i < 20)
    (firstOrder : i ≤ j) (upper : j < 20) :
    ZP.rawB Paley11987MutationFast.stage1 recipe1 i j ≤ ZP.B Paley11987MutationFast.stage2 i j := by
  interval_cases i
  · exact bRow0 j firstOrder upper
  · exact bRow1 j firstOrder upper
  · exact bRow2 j firstOrder upper
  · exact bRow3 j firstOrder upper
  · exact bRow4 j firstOrder upper
  · exact bRow5 j firstOrder upper
  · exact bRow6 j firstOrder upper
  · exact bRow7 j firstOrder upper
  · exact bRow8 j firstOrder upper
  · exact bRow9 j firstOrder upper
  · exact bRow10 j firstOrder upper
  · exact bRow11 j firstOrder upper
  · exact bRow12 j firstOrder upper
  · exact bRow13 j firstOrder upper
  · exact bRow14 j firstOrder upper
  · exact bRow15 j firstOrder upper
  · exact bRow16 j firstOrder upper
  · exact bRow17 j firstOrder upper
  · exact bRow18 j firstOrder upper
  · exact bRow19 j firstOrder upper

theorem mAll (i j : Nat) (iUpper : i < 20)
    (firstOrder : i ≤ j) (bound : j + 1 < 20) :
    ZP.rawM Paley11987MutationFast.stage1 recipe1 i j ≤ ZP.M Paley11987MutationFast.stage2 i j := by
  interval_cases i
  · exact mRow0 j firstOrder bound
  · exact mRow1 j firstOrder bound
  · exact mRow2 j firstOrder bound
  · exact mRow3 j firstOrder bound
  · exact mRow4 j firstOrder bound
  · exact mRow5 j firstOrder bound
  · exact mRow6 j firstOrder bound
  · exact mRow7 j firstOrder bound
  · exact mRow8 j firstOrder bound
  · exact mRow9 j firstOrder bound
  · exact mRow10 j firstOrder bound
  · exact mRow11 j firstOrder bound
  · exact mRow12 j firstOrder bound
  · exact mRow13 j firstOrder bound
  · exact mRow14 j firstOrder bound
  · exact mRow15 j firstOrder bound
  · exact mRow16 j firstOrder bound
  · exact mRow17 j firstOrder bound
  · exact mRow18 j firstOrder bound
  · omega

theorem pAll (j ell : Nat) (jUpper : j < 20)
    (firstOrder : j < ell) (upper : ell < 20) :
    ZP.rawP Paley11987MutationFast.stage1 recipe1 j ell ≤ ZP.P Paley11987MutationFast.stage2 j ell := by
  interval_cases j
  · exact pRow0 ell firstOrder upper
  · exact pRow1 ell firstOrder upper
  · exact pRow2 ell firstOrder upper
  · exact pRow3 ell firstOrder upper
  · exact pRow4 ell firstOrder upper
  · exact pRow5 ell firstOrder upper
  · exact pRow6 ell firstOrder upper
  · exact pRow7 ell firstOrder upper
  · exact pRow8 ell firstOrder upper
  · exact pRow9 ell firstOrder upper
  · exact pRow10 ell firstOrder upper
  · exact pRow11 ell firstOrder upper
  · exact pRow12 ell firstOrder upper
  · exact pRow13 ell firstOrder upper
  · exact pRow14 ell firstOrder upper
  · exact pRow15 ell firstOrder upper
  · exact pRow16 ell firstOrder upper
  · exact pRow17 ell firstOrder upper
  · exact pRow18 ell firstOrder upper
  · omega

theorem dAll (i j ell : Nat) (iUpper : i < 20)
    (firstOrder : i ≤ j) (secondOrder : j < ell) (upper : ell < 20) :
    ZP.rawD Paley11987MutationFast.stage1 recipe1 i j ell ≤ ZP.D Paley11987MutationFast.stage2 i j ell := by
  interval_cases i
  · exact dForI0 j ell firstOrder secondOrder upper
  · exact dForI1 j ell firstOrder secondOrder upper
  · exact dForI2 j ell firstOrder secondOrder upper
  · exact dForI3 j ell firstOrder secondOrder upper
  · exact dForI4 j ell firstOrder secondOrder upper
  · exact dForI5 j ell firstOrder secondOrder upper
  · exact dForI6 j ell firstOrder secondOrder upper
  · exact dForI7 j ell firstOrder secondOrder upper
  · exact dForI8 j ell firstOrder secondOrder upper
  · exact dForI9 j ell firstOrder secondOrder upper
  · exact dForI10 j ell firstOrder secondOrder upper
  · exact dForI11 j ell firstOrder secondOrder upper
  · exact dForI12 j ell firstOrder secondOrder upper
  · exact dForI13 j ell firstOrder secondOrder upper
  · exact dForI14 j ell firstOrder secondOrder upper
  · exact dForI15 j ell firstOrder secondOrder upper
  · exact dForI16 j ell firstOrder secondOrder upper
  · exact dForI17 j ell firstOrder secondOrder upper
  · exact dForI18 j ell firstOrder secondOrder upper
  · omega

end Paley11987MutationFastProof1

open Paley11987MutationFastProof1

theorem solution :
    ZP.TransitionCertificate Paley11987MutationFast.stage1 recipe1 Paley11987MutationFast.stage2 where
  a i j order := aAll i.val j.val i.isLt order j.isLt
  b i j order := bAll i.val j.val i.isLt order j.isLt
  m i j order bound := mAll i.val j.val i.isLt order bound
  p j ell order := pAll j.val ell.val j.isLt order ell.isLt
  d i j ell firstOrder secondOrder :=
    dAll i.val j.val ell.val i.isLt firstOrder secondOrder ell.isLt
