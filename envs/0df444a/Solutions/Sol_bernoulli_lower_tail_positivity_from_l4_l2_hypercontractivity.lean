-- Prove2me | solution 1 for bernoulli_lower_tail_positivity_from_l4_l2_hypercontractivity
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T01:48:32.086705+00:00
-- url     : https://prove2.me/submissions/9080a665-1737-49b5-a335-85bd3a501ab9

import Theorems.Thm_bernoulli_l2_le_l1_of_l4_le_l2sq
import Theorems.Thm_bernoulli_paley_zygmund_meanzero_positivity
import Mathlib.Algebra.Order.Field.Basic
open MatrixCompletion
open scoped Classical BigOperators

/-
de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211), Lemma 2 (real-valued case),
the lower-bound assembly  P(F ≥ 0) ≥ c⁻¹.

The forward bound's heart (eq. (6), p.4) is the statement that the diagonal chaos
survives a fixed fraction of the decoupled mass:  P(‖x + Σ a ε‖ ≥ ‖x‖) ≥ c_k⁻¹.
Specialised to a real mean-zero statistic F it reads  P(F ≥ 0) ≥ c⁻¹, with c the
hypercontractivity constant.  de la Peña's proof composes exactly two ingredients:

  • the L4→L2→L1 moment transfer (Lemma 2 line "‖ξ‖₄ ≤ σ⁻²‖ξ‖₂ ⟹ ‖ξ‖₂ ≤ σ⁻⁴‖ξ‖₁"),
    here  E[F⁴] ≤ K(E F²)²  ⟹  E[F²] ≤ K(E|F|)²   (the brick
    `bernoulli_l2_le_l1_of_l4_le_l2sq`), and
  • Proposition 1 (Paley–Zygmund positivity),  (E|F|)² ≤ 4 E[F²]·P(F ≥ 0)
    (the brick `bernoulli_paley_zygmund_meanzero_positivity`).

Chaining them:
    E[F²] ≤ K(E|F|)² ≤ K·4 E[F²]·P(F ≥ 0) = 4K·E[F²]·P(F ≥ 0).
Dividing by E[F²] > 0 gives  1 ≤ 4K·P(F ≥ 0), i.e.  P(F ≥ 0) ≥ 1/(4K).

This is the assembled Lemma 2 lower bound for the discrete Bernoulli powerset
measure, REDUCED to the two proved scaffolding bricks.  The only ingredient it
takes as a HYPOTHESIS (rather than deriving) is the L4↔L2 hypercontractivity
`E[F⁴] ≤ K(E F²)²` — that constant for the σ-randomized multilinear chaos
(Kwapień–Szulga 1991, eq. 1.4) is the genuinely Mathlib-absent step and is left
to be supplied by the caller (e.g. the order-2 symmetric form
`centered_sampling_coefficient_symmetric_l4_l2_hypercontractivity`, K = 3).
-/

theorem solution
    {n₁ n₂ : ℕ} (p : ℝ) (K : ℝ)
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) :
    0 ≤ p → p ≤ 1 → 0 < K →
    bernoulliExpectation p F = 0 →
    0 < bernoulliExpectation p (fun Ω => (F Ω) ^ 2) →
    bernoulliExpectation p (fun Ω => (F Ω) ^ 4) ≤
        K * (bernoulliExpectation p (fun Ω => (F Ω) ^ 2)) ^ 2 →
    (1 : ℝ) / (4 * K) ≤ bernoulliEventProb p (fun Ω => 0 ≤ F Ω) := by
  intro hp0 hp1 hK hmean hvar hHC
  -- abbreviations
  set b : ℝ := bernoulliExpectation p (fun Ω => (F Ω) ^ 2) with hb
  set a : ℝ := bernoulliExpectation p (fun Ω => |F Ω|) with ha
  set P : ℝ := bernoulliEventProb p (fun Ω => 0 ≤ F Ω) with hP
  -- L4 → L2 → L1 transfer (brick b80931b4):  b ≤ K · a²
  have hTransfer : b ≤ K * a ^ 2 := by
    have := bernoulli_l2_le_l1_of_l4_le_l2sq p K F hp0 hp1 (le_of_lt hK) hHC
    simpa [hb, ha] using this
  -- Paley–Zygmund positivity (brick 12973b7e):  a² ≤ 4 · b · P
  have hPZ : a ^ 2 ≤ 4 * b * P := by
    have := bernoulli_paley_zygmund_meanzero_positivity p F hp0 hp1 hmean
    simpa [ha, hb, hP] using this
  -- chain:  b ≤ K·a² ≤ K·(4·b·P) = 4K·b·P
  have hchain : b ≤ 4 * K * b * P := by
    calc b ≤ K * a ^ 2 := hTransfer
      _ ≤ K * (4 * b * P) := by
            apply mul_le_mul_of_nonneg_left hPZ (le_of_lt hK)
      _ = 4 * K * b * P := by ring
  -- divide by b > 0 :  1 ≤ 4K·P, then by 4K > 0 :  1/(4K) ≤ P
  have h4Kpos : (0 : ℝ) < 4 * K := by linarith
  have hone : (1 : ℝ) ≤ 4 * K * P := by
    have hb' : b * 1 ≤ b * (4 * K * P) := by
      have : b ≤ b * (4 * K * P) := by
        calc b ≤ 4 * K * b * P := hchain
          _ = b * (4 * K * P) := by ring
      simpa using this
    exact le_of_mul_le_mul_left (by simpa using hb') hvar
  -- conclude
  rw [div_le_iff₀ h4Kpos]
  linarith [hone]
