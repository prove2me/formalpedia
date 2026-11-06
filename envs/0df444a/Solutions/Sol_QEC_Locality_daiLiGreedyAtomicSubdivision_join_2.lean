-- Prove2me | solution 2 for QEC.Locality.daiLiGreedyAtomicSubdivision_join
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:27:33.091917+00:00
-- url     : https://prove2.me/submissions/1519ff67-5c5d-45f6-a94a-0016dcbe66c5

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

theorem QLAux.scan_flatten (d : Nat) : ∀ (bands pending : List DaiLiAtomicCounter)
    (emitted : List (List DaiLiAtomicCounter)),
    (daiLiGreedyScan d bands pending emitted).flatten = emitted.reverse.flatten ++ pending ++ bands := by
  intro bands
  induction bands with
  | nil =>
    intro pending emitted
    simp only [daiLiGreedyScan]
    split_ifs with h
    · subst h; simp
    · simp
  | cons a rest ih =>
    intro pending emitted
    simp only [daiLiGreedyScan]
    split_ifs with h1 h2
    · rw [ih]; simp
    · rw [ih]; subst h2; simp
    · rw [ih]; simp

theorem solution (d : Nat) (bands : List DaiLiAtomicCounter) :
    (daiLiGreedyAtomicSubdivision d bands).flatten = bands := by
  unfold daiLiGreedyAtomicSubdivision
  rw [QLAux.scan_flatten]
  simp
