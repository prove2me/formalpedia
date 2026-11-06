-- Prove2me | solution 2 for QEC.Locality.daiLiCorrectedFamilyCount_lt_budget_div
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:29:56.345196+00:00
-- url     : https://prove2.me/submissions/10b7e9cd-bd4c-4d74-807c-9098e45f9e6a

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]

theorem solution
    (M totalF d budget : Nat) (hD : 0 < d) (hDLeBudget : d ≤ budget)
    (hCount : M * d ≤ 30 * totalF) (hTotal : 50 * totalF ≤ budget)
    (hEmptyOrBad : M = 0 ∨ d ≤ 10 * totalF) :
    M < budget / d := by
  rcases hEmptyOrBad with h | h
  · subst h
    exact Nat.div_pos hDLeBudget hD
  · have h1 : (M + 1) * d = M * d + d := by ring
    have h2 : (M + 1) * d ≤ budget := by omega
    exact (Nat.le_div_iff_mul_le hD).2 h2
