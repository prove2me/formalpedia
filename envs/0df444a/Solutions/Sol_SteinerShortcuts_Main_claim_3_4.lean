-- Prove2me | solution 1 for SteinerShortcuts.Main.claim_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:18:30.951344+00:00
-- url     : https://prove2.me/submissions/0faccb9d-b890-499f-9320-15f2bd416d4e

import Definitions.Def_SteinerShortcuts_Main_TestFunctions

open SteinerShortcuts.Main

set_option maxRecDepth 4000
set_option maxHeartbeats 800000

theorem solution (L q : ℕ) (h : Admissible L q) (P Q : CriticalData q)
    (R T : Route Point) (hs : PairSetup L q P Q R T) :
    T3prime L q (testY P Q) := by
  let mo := lineSlope q P.a Q.a
  let me := lineSlope q P.b Q.b
  let no := lineIntercept q P.a Q.a
  let ne := lineIntercept q P.b Q.b
  refine ⟨![0, no^2, ne^2,
    2*mo*no, mo^2-2*no, (q:ℝ)*mo^2, -2*mo,
    2*me*ne, me^2-2*ne, (q:ℝ)*me^2, -2*me,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0], fun _ => 0, ?_⟩
  intro v hv t
  have hz : (t.val : ℝ)^2 =
      (q:ℝ) * ((((t.val : ℤ)^2 - labelY q t.val) / (q:ℤ) : ℤ) : ℝ) +
        (labelY q t.val : ℝ) := by
    have hi : (t.val : ℤ)^2 - labelY q t.val =
        (q:ℤ) * ((t.val : ℤ)^2 / (q:ℤ)) := by
      dsimp [labelY]
      have := Int.emod_add_mul_ediv ((t.val : ℤ)^2) (q:ℤ)
      omega
    have he : ((t.val : ℤ)^2 - labelY q t.val) / (q:ℤ) =
        (t.val : ℤ)^2 / (q:ℤ) := by
      rw [hi]
      exact Int.mul_ediv_cancel_left _ (by exact_mod_cast h.2.2.1.ne_zero)
    rw [he]
    have hi2 := (Int.mul_ediv_add_emod ((t.val : ℤ)^2) (q:ℤ)).symm
    dsimp [labelY]
    exact_mod_cast hi2
  by_cases ho : v 0 % 2 = 1
  · simp [testY, position, update, direction, ho, Fin.sum_univ_succ]
    dsimp [mo, no] at *
    nlinarith [hz]
  · simp [testY, position, update, direction, ho, Fin.sum_univ_succ]
    dsimp [me, ne] at *
    nlinarith [hz]
