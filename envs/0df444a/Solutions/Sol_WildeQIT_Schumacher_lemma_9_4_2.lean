-- Prove2me | solution 1 for WildeQIT.Schumacher.lemma_9_4_2
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-25T17:24:05.23882+00:00
-- url     : https://prove2.me/submissions/8f26eb6c-fe58-4c8e-aa79-4dc7d8817ef4

import Theorems.Thm_WildeQIT_Gentle_lemma_9_4_1
import Theorems.Thm_WildeQIT_Gentle_lemma_9_4_2
open Matrix WildeQIT
open scoped MatrixOrder ComplexOrder




/-- **Lemma 9.4.2 (Gentle Operator)** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, p. 278, eqs. (9.203)–(9.204)). Let `ρ` be a density operator and `Λ` a
measurement operator, `0 ≤ Λ ≤ I`. If `Tr{Λρ} ≥ 1 − ε` with `ε ∈ [0, 1]`, then
`‖ρ − √Λ ρ √Λ‖₁ ≤ 2√ε`.

**Formalization Note.** `0 ≤ Λ ≤ I` is `Λ.PosSemidef ∧ (1 − Λ).PosSemidef`; `√Λ` is `CFC.sqrt`;
`Tr{Λρ}` is the real part of the complex trace (real here); `‖·‖₁` is the published
`WildeQIT.traceNorm` (unhalved). -/
theorem solution {n : Type} [Fintype n] [DecidableEq n] (ρ Λ : Matrix n n ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ) (hΛ : Λ.PosSemidef) (hΛI : (1 - Λ).PosSemidef)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hdet : 1 - ε ≤ (Λ * ρ).trace.re) :
    WildeQIT.traceNorm (ρ - CFC.sqrt Λ * ρ * CFC.sqrt Λ) ≤ 2 * Real.sqrt ε := by
  exact WildeQIT.Gentle.lemma_9_4_2 ρ Λ hρ hΛ hΛI ε hε0 hε1 hdet