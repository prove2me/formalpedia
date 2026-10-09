-- Prove2me | solution 1 for OCB2012.isTracePreserving_iff_ptrace_cj
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-09T10:15:04.620318+00:00
-- url     : https://prove2.me/submissions/7481d4d1-9ded-4d55-8d6a-b027ed9c7010

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs
import Definitions.Def_OCB2012_cj

open Matrix
open scoped Kronecker ComplexOrder

open OCB2012 in
theorem solution {x1 x2 : Type*} [Fintype x1] [Fintype x2]
    [DecidableEq x1] [DecidableEq x2] (Φ : Matrix x1 x1 ℂ →ₗ[ℂ] Matrix x2 x2 ℂ) :
    IsTracePreserving Φ ↔ ptrace₂ (cjMatrix Φ) = 1 := by
  have hpt : ∀ i j, ptrace₂ (cjMatrix Φ) i j = (Φ (single j i 1)).trace := by
    intro i j; simp [ptrace₂, cjMatrix, Matrix.trace]
  constructor
  · intro hTP
    ext i j
    rw [hpt, hTP, one_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  · intro h ρ
    have hρ : ρ = ∑ i, ∑ j, ρ i j • single i j (1 : ℂ) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single ρ]
      simp only [smul_single, smul_eq_mul, mul_one]
    have hΦ : ∀ i j, (Φ (single i j 1)).trace = if i = j then 1 else 0 := by
      intro i j; rw [← hpt, h, one_apply]; simp [eq_comm]
    conv_lhs => rw [hρ]
    simp only [map_sum, map_smul, trace_sum, trace_smul, hΦ, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp [Matrix.trace]
