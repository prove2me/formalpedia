-- Prove2me | solution 1 for SponsoredAssort.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:33:16.920428+00:00
-- url     : https://prove2.me/submissions/19ea03b7-c7ab-429b-b6d8-e8c1f1ea2d51

import Mathlib
import Definitions.Def_SponsoredAssort_IsIC

open scoped NNReal

open SponsoredAssort in
theorem solution {n : ℕ} (r : Fin n → ℝ) (m : Mechanism n) (hIC : IsIC r m) (v : Attr n)
    (i : Fin n) (y : ℝ≥0) (hS : m.alloc (Function.update v i y) = m.alloc v) :
    m.pay (Function.update v i y) i = m.pay v i := by
  have h1 := hIC i v y
  have h2 := hIC i (Function.update v i y) (v i)
  unfold utility at h1 h2
  rw [Function.update_eq_self, hS] at h1
  simp only [Function.update_idem, Function.update_self, Function.update_eq_self] at h2
  rw [hS] at h2
  linarith
