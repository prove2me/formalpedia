-- Prove2me | solution 1 for Schnir.mann_rank
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T11:37:33.378352+00:00
-- url     : https://prove2.me/submissions/e3c57da4-bc01-4952-9a0e-50513244a735

import Mathlib.Combinatorics.Schnirelmann
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Theorems.Thm_Schnir_mann

/-!
# Mann's theorem at arbitrary rank (Dyson's form)

`sigma(A_1 + ... + A_r) >= min(1, sum of the sigma(A_i))`, by induction on `r`
using the two-set Mann theorem proved on this platform (`Schnir.mann`).
-/

open Finset Pointwise Classical

/-- `min 1 .` is monotone. -/
theorem min_one_mono' {x y : ℝ} (h : x ≤ y) : min 1 x ≤ min 1 y := by
  rcases le_total 1 x with hx | hx
  · rw [min_eq_left hx]; exact le_min (le_refl 1) (hx.trans h)
  · rw [min_eq_right hx]; exact le_min hx h

/-- Zero lies in the pointwise sum of sets each containing zero. -/
theorem zero_mem_sumset {ι : Type*} [DecidableEq ι] (As : ι → Set ℕ) (s : Finset ι)
    (h0 : ∀ i ∈ s, 0 ∈ As i) : 0 ∈ ∑ i ∈ s, As i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ⟨0, h0 a (Finset.mem_insert_self _ _),
      0, ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi)), by simp⟩

open Pointwise Classical in
/-- Mann's theorem at arbitrary rank. -/
theorem mann_rank : ∀ (r : ℕ) (As : Fin r → Set ℕ), (∀ i, 0 ∈ As i) →
    min 1 (∑ i, schnirelmannDensity (As i)) ≤ schnirelmannDensity (∑ i, As i) := by
  intro r
  induction r with
  | zero =>
    intro As _
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact (min_le_right (1 : ℝ) 0).trans schnirelmannDensity_nonneg
  | succ r IH =>
    intro As h0
    have h0B : ∀ i : Fin r, 0 ∈ As (Fin.castSucc i) := fun i => h0 _
    have ih := IH (fun i => As (Fin.castSucc i)) h0B
    have h0p : 0 ∈ ∑ i : Fin r, As (Fin.castSucc i) :=
      zero_mem_sumset _ Finset.univ (fun i _ => h0B i)
    have hmann := Schnir.mann (∑ i : Fin r, As (Fin.castSucc i)) (As (Fin.last r))
      h0p (h0 _)
    simp only [Fin.sum_univ_castSucc]
    have hnn : (0 : ℝ) ≤ schnirelmannDensity (As (Fin.last r)) := schnirelmannDensity_nonneg
    have hkey : min 1 ((∑ i : Fin r, schnirelmannDensity (As (Fin.castSucc i)))
          + schnirelmannDensity (As (Fin.last r)))
        = min 1 (min 1 (∑ i : Fin r, schnirelmannDensity (As (Fin.castSucc i)))
          + schnirelmannDensity (As (Fin.last r))) := by
      rcases le_total 1 (∑ i : Fin r, schnirelmannDensity (As (Fin.castSucc i))) with h | h
      · rw [min_eq_left h, min_eq_left (by linarith), min_eq_left (by linarith)]
      · rw [min_eq_right h]
    calc min 1 ((∑ i : Fin r, schnirelmannDensity (As (Fin.castSucc i)))
          + schnirelmannDensity (As (Fin.last r)))
        = min 1 (min 1 (∑ i : Fin r, schnirelmannDensity (As (Fin.castSucc i)))
            + schnirelmannDensity (As (Fin.last r))) := hkey
      _ ≤ min 1 (schnirelmannDensity (∑ i : Fin r, As (Fin.castSucc i))
            + schnirelmannDensity (As (Fin.last r))) :=
          min_one_mono' (add_le_add ih (le_refl _))
      _ ≤ schnirelmannDensity ((∑ i : Fin r, As (Fin.castSucc i)) + As (Fin.last r)) := hmann

open Pointwise Classical in
/-- Mann's theorem at arbitrary rank (Dyson's form). -/
theorem solution {r : ℕ} (As : Fin r → Set ℕ) (h0 : ∀ i, 0 ∈ As i) :
    min 1 (∑ i, schnirelmannDensity (As i)) ≤ schnirelmannDensity (∑ i, As i) :=
  mann_rank r As h0
