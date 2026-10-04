-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.scalar_contraction_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T03:33:10.988002+00:00
-- url     : https://prove2.me/submissions/e6a17cbe-ac37-4a8a-9a63-73d3d951e63d

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

open ShorNonsmooth.SpaceDilation

/- The remote wrapper resolves the unqualified declaration name `solution`, so this
must be a genuine top-level declaration. -/
theorem solution {M N D P a : ℝ} (hN : 0 < N) (hNM : N ≤ M)
    (hD : 0 ≤ D) (hlo : N * D ≤ P) (hhi : P ≤ M * D) (ha1 : 1 ≤ a)
    (haMN : a * (M - N) ≤ M + N) :
    a ^ 2 * (P - 2 * M * N / (M + N) * D) ^ 2 ≤ P ^ 2 := by
  classical
  have hSum : 0 < M + N := by linarith
  have hha1 : 0 ≤ a - 1 := sub_nonneg.mpr ha1
  -- Keep the fraction `2*M*N/(M+N)` under the opaque name `c`. Earlier attempts let
  -- `linarith` / `le_div_iff₀` meet the division directly; `linarith` is linear and cannot
  -- clear a denominator, and letting `le_div_iff₀` elaborate first triggered metavariable
  -- drift. `c` keeps every later step polynomial, and only two places clear `M + N`.
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c * (M + N) = 2 * M * N :=
    ⟨2 * M * N / (M + N), by field_simp⟩
  -- One bracket drives both halves. It is `haMN` rewritten, using `M, N >= 0`.
  have hbracket : (a - 1) * M - (a + 1) * N ≤ 0 := by nlinarith
  -- Upper half: `(a-1)*M <= a*c`, then `(a-1)*P <= a*c*D` using `P <= M*D`.
  have key₁ : (a - 1) * M ≤ a * c := by
    have h1 : (a - 1) * M * (M + N) ≤ a * c * (M + N) :=
      mul_le_mul_of_nonneg_right (by nlinarith [hbracket]) hSum.le
    nlinarith
  have hup : a * (P - c * D) ≤ P := by
    have h1 : (a - 1) * P ≤ (a - 1) * (M * D) :=
      mul_le_mul_of_nonneg_left hhi hha1
    have h2 : (a - 1) * (M * D) ≤ a * c * D := by nlinarith [hD]
    nlinarith
  -- Lower half: `a*c <= (a+1)*N`, then `a*c*D <= (a+1)*P` using `P >= N*D`.
  have key₂ : a * c ≤ (a + 1) * N := by
    have h1 : a * c * (M + N) ≤ (a + 1) * N * (M + N) :=
      mul_le_mul_of_nonneg_right (by nlinarith [hbracket]) hSum.le
    nlinarith
  have hdn : -P ≤ a * (P - c * D) := by
    have h1 : a * c * D ≤ (a + 1) * (N * D) := by nlinarith [hD]
    have h2 : (a + 1) * (N * D) ≤ (a + 1) * P :=
      mul_le_mul_of_nonneg_left hlo (by linarith)
    nlinarith
  -- `sq_le_sq' (h1 : -b <= a) (h2 : a <= b) : a^2 <= b^2` consumes the two-sided
  -- bound directly. Going through `abs_le` + `sq_le_sq₀` instead forces `sq_le_sq₀`'s
  -- first argument to be a *nonnegativity*, which `|a (P - cD)| <= P` is not.
  have hsq : (a * (P - c * D)) ^ 2 ≤ P ^ 2 := sq_le_sq' hdn hup
  -- Replace `c` by its definition and restate in the goal's exact shape.
  have hcdef : c = 2 * M * N / (M + N) := by
    rw [eq_div_iff hSum.ne']
    exact hc
  have hsq' : (a * (P - 2 * M * N / (M + N) * D)) ^ 2 ≤ P ^ 2 := by
    rw [← hcdef]
    exact hsq
  have heq : (a * (P - 2 * M * N / (M + N) * D)) ^ 2
      = a ^ 2 * (P - 2 * M * N / (M + N) * D) ^ 2 := by ring
  rw [heq] at hsq'
  exact hsq'
