-- Prove2me | solution 2 for QEC.Locality.daiLiGreedySubdivisionWith_map
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:29:52.722843+00:00
-- url     : https://prove2.me/submissions/1020f814-bd31-47d4-a318-9eb1bde81b2b

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

theorem QLAux.scanWith_map {α : Type*} (weight : α → Nat) (d : Nat) : ∀ (bands pending : List α)
    (emitted : List (List α)),
    (daiLiGreedyScanWith weight d bands pending emitted).map (List.map weight) =
      daiLiGreedyScan d (bands.map weight) (pending.map weight) (emitted.map (List.map weight)) := by
  intro bands
  induction bands with
  | nil =>
    intro pending emitted
    simp only [daiLiGreedyScanWith, List.map_nil, daiLiGreedyScan]
    by_cases h : pending = []
    · subst h; simp [List.map_reverse]
    · have h' : pending.map weight ≠ [] := by simpa using h
      simp [h, h', List.map_reverse]
  | cons a rest ih =>
    intro pending emitted
    simp only [daiLiGreedyScanWith, List.map_cons, daiLiGreedyScan]
    by_cases hLow : 10 * ((pending.map weight).sum + weight a) ≤ d
    · have hLow' : 10 * (daiLiAtomicMass (pending.map weight) + weight a) ≤ d := hLow
      rw [dif_pos hLow, dif_pos hLow', ih]; simp
    · have hLow' : ¬ 10 * (daiLiAtomicMass (pending.map weight) + weight a) ≤ d := hLow
      rw [dif_neg hLow, dif_neg hLow']
      by_cases hP : pending = []
      · subst hP
        first
          | (rw [dif_pos rfl, dif_pos rfl, ih]; simp)
          | simp [ih]
      · have h' : pending.map weight ≠ [] := by simpa using hP
        rw [dif_neg hP, dif_neg h', ih]; simp

theorem solution {α : Type*} (weight : α → Nat) (d : Nat)
    (bands : List α) :
    (daiLiGreedySubdivisionWith weight d bands).map (List.map weight) =
      daiLiGreedyAtomicSubdivision d (bands.map weight) := by
  unfold daiLiGreedySubdivisionWith daiLiGreedyAtomicSubdivision
  rw [QLAux.scanWith_map]
  simp
