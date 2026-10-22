-- Prove2me | solution 1 for SnarkGen.OddFactors.g81_egirth
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:26:43.65968+00:00
-- url     : https://prove2.me/submissions/06ceb861-2f1f-49b7-9711-76d0a2c3c2a8

import Mathlib
import Definitions.Def_SnarkGen_OddFactors_G81

set_option autoImplicit false
open SnarkGen.OddFactors

theorem g81_no3' : ∀ a b : Fin 26, G81.Adj a b → ∀ c : Fin 26, G81.Adj b c → G81.Adj c a → False := by
  decide +kernel

theorem g81_no3 : ∀ a b c : Fin 26, G81.Adj a b → G81.Adj b c → G81.Adj c a → False :=
  fun a b c h1 h2 h3 => g81_no3' a b h1 c h2 h3

theorem g81_no4' : ∀ a b : Fin 26, G81.Adj a b → ∀ c : Fin 26, G81.Adj b c → ∀ d : Fin 26, G81.Adj c d →
    G81.Adj d a → a = c ∨ b = d := by
  decide +kernel

theorem g81_no4 : ∀ a b c d : Fin 26, G81.Adj a b → G81.Adj b c → G81.Adj c d → G81.Adj d a →
    a = c ∨ b = d :=
  fun a b c d h1 h2 h3 h4 => g81_no4' a b h1 c h2 d h3 h4

theorem solution : 5 ≤ G81.egirth := by
  rw [SimpleGraph.le_egirth]
  intro a w hw
  have h3 := hw.three_le_length
  by_contra hlt
  have hlt' : w.length < 5 := by
    by_contra h
    exact hlt (by exact_mod_cast (not_lt.1 h))
  have hinj := hw.getVert_injOn
  have hend : w.getVert w.length = a := w.getVert_length
  have hstart : w.getVert 0 = a := w.getVert_zero
  have hadj : ∀ i, i < w.length → G81.Adj (w.getVert i) (w.getVert (i + 1)) :=
    fun i hi => w.adj_getVert_succ hi
  have hcases : w.length = 3 ∨ w.length = 4 := by omega
  rcases hcases with h | h
  · have a0 := hadj 0 (by omega)
    have a1 := hadj 1 (by omega)
    have a2 := hadj 2 (by omega)
    rw [hstart] at a0
    have e3 := hend
    rw [h] at e3
    rw [e3] at a2
    exact g81_no3 a (w.getVert 1) (w.getVert 2) a0 a1 a2
  · have a0 := hadj 0 (by omega)
    have a1 := hadj 1 (by omega)
    have a2 := hadj 2 (by omega)
    have a3 := hadj 3 (by omega)
    rw [hstart] at a0
    have e4 := hend
    rw [h] at e4
    rw [e4] at a3
    rcases g81_no4 a (w.getVert 1) (w.getVert 2) (w.getVert 3) a0 a1 a2 a3 with h1 | h1
    · have := hinj (show (2 : ℕ) ∈ {i | 1 ≤ i ∧ i ≤ w.length} by simp; omega)
        (show (4 : ℕ) ∈ {i | 1 ≤ i ∧ i ≤ w.length} by simp; omega) (by rw [e4]; exact h1.symm)
      omega
    · have := hinj (show (1 : ℕ) ∈ {i | 1 ≤ i ∧ i ≤ w.length} by simp; omega)
        (show (3 : ℕ) ∈ {i | 1 ≤ i ∧ i ≤ w.length} by simp; omega) h1
      omega
