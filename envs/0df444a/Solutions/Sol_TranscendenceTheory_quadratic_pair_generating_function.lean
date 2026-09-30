-- Prove2me | solution 1 for TranscendenceTheory.quadratic_pair_generating_function
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T21:16:04.574216+00:00
-- url     : https://prove2.me/submissions/c015e02b-29ad-452a-a3fa-d3818de598d7

import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.LinearCombination

open PowerSeries

private lemma pair_series_equations (R : Type*) [CommRing R] (d a b : R) :
    let T : ℕ → R × R := Nat.rec (1, 0)
      (fun _ t => (a * t.1 + d * b * t.2, b * t.1 + a * t.2))
    let U : PowerSeries R := mk fun n => (T n).1
    let V : PowerSeries R := mk fun n => (T n).2
    U = 1 + X * (C a * U + C (d * b) * V) ∧
      V = X * (C b * U + C a * V) := by
  dsimp only
  constructor <;> ext n <;> cases n with
  | zero => simp
  | succ n => simp [mul_assoc]

theorem solution
    (R : Type*) [CommRing R] (d a b : R) :
    let T : ℕ → R × R := Nat.rec (1, 0)
      (fun _ t => (a * t.1 + d * b * t.2, b * t.1 + a * t.2))
    let Q : PowerSeries R := 1 - C (2 * a) * X + C (a ^ 2 - d * b ^ 2) * X ^ 2
    let H := PowerSeries.invOfUnit Q (1 : Rˣ)
    PowerSeries.mk (fun n => (T n).1) = (1 - C a * X) * H ∧
      PowerSeries.mk (fun n => (T n).2) = C b * X * H := by
  dsimp only
  let T : ℕ → R × R := Nat.rec (1, 0)
    (fun _ t => (a * t.1 + d * b * t.2, b * t.1 + a * t.2))
  let U : PowerSeries R := mk fun n => (T n).1
  let V : PowerSeries R := mk fun n => (T n).2
  let Q : PowerSeries R := 1 - C (2 * a) * X + C (a ^ 2 - d * b ^ 2) * X ^ 2
  let H := PowerSeries.invOfUnit Q (1 : Rˣ)
  change U = (1 - C a * X) * H ∧ V = C b * X * H
  have hsystem : U = 1 + X * (C a * U + C (d * b) * V) ∧
      V = X * (C b * U + C a * V) := pair_series_equations R d a b
  obtain ⟨hU, hV⟩ := hsystem
  simp only [map_mul] at hU
  have hQU : Q * U = 1 - C a * X := by
    dsimp only [Q]
    simp only [map_mul, map_sub, map_pow, map_ofNat]
    linear_combination (1 - C a * X) * hU + C d * C b * X * hV
  have hQV : Q * V = C b * X := by
    dsimp only [Q]
    simp only [map_mul, map_sub, map_pow, map_ofNat]
    linear_combination C b * X * hU + (1 - C a * X) * hV
  have hInv : Q * H = 1 := PowerSeries.mul_invOfUnit Q 1 (by simp [Q])
  constructor
  · calc
      U = (Q * U) * H := by rw [mul_comm Q U, mul_assoc, hInv, mul_one]
      _ = (1 - C a * X) * H := by rw [hQU]
  · calc
      V = (Q * V) * H := by rw [mul_comm Q V, mul_assoc, hInv, mul_one]
      _ = C b * X * H := by rw [hQV]
