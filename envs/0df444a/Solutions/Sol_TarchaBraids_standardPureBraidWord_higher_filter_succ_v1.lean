-- Prove2me | solution 1 for TarchaBraids.standardPureBraidWord_higher_filter_succ_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-22T17:49:27.191649+00:00
-- url     : https://prove2.me/submissions/ec6997bb-cf8e-471d-a254-7789e533ddd9

import Mathlib

/-- The higher-index filter is compatible with adjoining a new final strand. -/
theorem solution (n : ℕ) (j : Fin n) :
    (List.finRange (n + 1)).filter (fun k : Fin (n + 1) => j.castSucc < k) =
      (((List.finRange n).filter (fun k : Fin n => j < k)).map Fin.castSucc) ++
        [Fin.last n] := by
  have hmap : ∀ l : List (Fin n),
      (l.map Fin.castSucc).filter (fun k : Fin (n + 1) => j.castSucc < k) =
        (l.filter (fun k : Fin n => j < k)).map Fin.castSucc := by
    intro l
    induction l with
    | nil => rfl
    | cons k ks ih =>
      have hcmp : j.castSucc < k.castSucc ↔ j < k := by rfl
      by_cases h : j < k
      · simp [List.filter_cons, h, hcmp, ih]
      · simp [List.filter_cons, h, hcmp, ih]
  rw [List.finRange_succ_last, List.filter_append, hmap]
  have hlast : j.castSucc < Fin.last n := Fin.castSucc_lt_last j
  simp [hlast]
