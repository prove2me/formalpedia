-- Prove2me | solution 1 for ReciprocityTheory.Cheb.natCast_mem_of_liesOver
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T12:15:10.64793+00:00
-- url     : https://prove2.me/submissions/c671dadb-ef05-449b-a1f6-2a6d1e33fc42

import Mathlib

open scoped NumberField

theorem solution {K : Type*} [Field K] [NumberField K] {p : ℕ}
    (P : Ideal (𝓞 K)) [P.LiesOver (Ideal.span {(p : ℤ)})] : (p : 𝓞 K) ∈ P := by
  have h : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.mem_span_singleton_self _
  rw [Ideal.mem_of_liesOver (p := Ideal.span {(p : ℤ)}) (P := P)] at h
  exact_mod_cast h
