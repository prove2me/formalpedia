-- Prove2me | solution 1 for WildeQIT.Schumacher.lemma_9_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-25T17:23:58.959745+00:00
-- url     : https://prove2.me/submissions/f1244c95-9de4-4208-b556-9d3e4aa09f5f

import Theorems.Thm_WildeQIT_Gentle_lemma_9_4_1
import Theorems.Thm_WildeQIT_Gentle_lemma_9_4_2
open Matrix WildeQIT
open scoped MatrixOrder ComplexOrder




/-- **Lemma 9.4.1 (Gentle Measurement)** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, p. 277, eqs. (9.195)–(9.197)). Let `ρ` be a density operator and `Λ` a
measurement operator, `0 ≤ Λ ≤ I`. If `Tr{Λρ} ≥ 1 − ε` with `ε ∈ [0, 1]`, then the
post-measurement state `ρ′ = √Λ ρ √Λ / Tr{Λρ}` satisfies `‖ρ − ρ′‖₁ ≤ 2√ε`.

**Formalization Note.** `0 ≤ Λ ≤ I` is `Λ.PosSemidef ∧ (1 − Λ).PosSemidef`; `Tr{Λρ}` is the real
part of the complex trace (real here). The hypothesis `Tr{Λρ} ≠ 0` only excludes the case
(possible only at `ε = 1`) where the book's `ρ′` is undefined. `‖·‖₁` is the published
`WildeQIT.traceNorm` (unhalved). -/
theorem solution {n : Type} [Fintype n] [DecidableEq n] (ρ Λ : Matrix n n ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ) (hΛ : Λ.PosSemidef) (hΛI : (1 - Λ).PosSemidef)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hdet : 1 - ε ≤ (Λ * ρ).trace.re)
    (hne : (Λ * ρ).trace ≠ 0) :
    WildeQIT.traceNorm (ρ - WildeQIT.Gentle.postMeasurementState Λ ρ) ≤ 2 * Real.sqrt ε := by
  exact WildeQIT.Gentle.lemma_9_4_1 ρ Λ hρ hΛ hΛI ε hε0 hε1 hdet hne