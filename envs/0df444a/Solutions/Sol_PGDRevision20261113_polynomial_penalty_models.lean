-- Prove2me | solution 1 for PGDRevision20261113.polynomial_penalty_models
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-13T10:20:15.062319+00:00
-- url     : https://prove2.me/submissions/eac1a5c6-bf2c-4ff6-9a8f-ea603a09c20e

import Definitions.Def_PGDRevision20261113_Examples
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1500000
open PGDRevision20261113
noncomputable section

private lemma pen1_first (lam x : ℝ) :
    HasDerivAt (polynomialPenalty1 lam) (lam * (x + x ^ 3 / 3)) x := by
  change HasDerivAt (fun t : ℝ => lam * (t ^ 2 / 2 + t ^ 4 / 12)) _ x
  convert ((((hasDerivAt_id x).pow 2).div_const 2).add
    (((hasDerivAt_id x).pow 4).div_const 12)).const_mul lam using 1 <;> first | rfl | norm_num <;> try ring <;> simp

private lemma pen2_first (lam x : ℝ) :
    HasDerivAt (polynomialPenalty2 lam) (lam * (x + x ^ 3 / 3 + x ^ 4 / 4 + x ^ 5 / 5)) x := by
  change HasDerivAt (fun t : ℝ => lam * (t ^ 2 / 2 + t ^ 4 / 12 + t ^ 5 / 20 + t ^ 6 / 30)) _ x
  convert ((((((hasDerivAt_id x).pow 2).div_const 2).add
    (((hasDerivAt_id x).pow 4).div_const 12)).add
    (((hasDerivAt_id x).pow 5).div_const 20)).add
    (((hasDerivAt_id x).pow 6).div_const 30)).const_mul lam using 1 <;> first | rfl | norm_num <;> try ring <;> simp

private lemma pen1_second (lam x : ℝ) :
    deriv (deriv (polynomialPenalty1 lam)) x = lam * polynomialB1 x := by
  have hf : deriv (polynomialPenalty1 lam) = fun t => lam * (t + t ^ 3 / 3) :=
    funext fun t => (pen1_first lam t).deriv
  rw [hf]
  have hd : HasDerivAt (fun t : ℝ => lam * (t + t ^ 3 / 3)) (lam * polynomialB1 x) x := by
    convert ((hasDerivAt_id x).add (((hasDerivAt_id x).pow 3).div_const 3)).const_mul lam
      using 1 <;> first | rfl | norm_num [polynomialB1] <;> ring
  exact hd.deriv

private lemma pen2_second (lam x : ℝ) :
    deriv (deriv (polynomialPenalty2 lam)) x = lam * polynomialB2 x := by
  have hf : deriv (polynomialPenalty2 lam) =
      fun t => lam * (t + t ^ 3 / 3 + t ^ 4 / 4 + t ^ 5 / 5) :=
    funext fun t => (pen2_first lam t).deriv
  rw [hf]
  have hd : HasDerivAt (fun t : ℝ => lam * (t + t ^ 3 / 3 + t ^ 4 / 4 + t ^ 5 / 5))
      (lam * polynomialB2 x) x := by
    convert ((((hasDerivAt_id x).add (((hasDerivAt_id x).pow 3).div_const 3)).add
      (((hasDerivAt_id x).pow 4).div_const 4)).add
      (((hasDerivAt_id x).pow 5).div_const 5)).const_mul lam using 1
      <;> first | rfl | norm_num [polynomialB2] <;> ring
  exact hd.deriv

private lemma b1_deriv (x : ℝ) : HasDerivAt polynomialB1 (2 * x) x := by
  convert (((hasDerivAt_id x).pow 2).const_add 1) using 1
    <;> first | rfl | norm_num <;> try ring <;> simp

private lemma b2_deriv (x : ℝ) : HasDerivAt polynomialB2 (x * (2 + 3 * x + 4 * x ^ 2)) x := by
  convert (((((hasDerivAt_id x).pow 2).const_add 1).add ((hasDerivAt_id x).pow 3)).add
    ((hasDerivAt_id x).pow 4)) using 1 <;> first | rfl | norm_num <;> try ring <;> simp

private lemma b2_strict (x : ℝ) (hx : x ≠ 0) : 1 < polynomialB2 x := by
  have hp : 0 < x ^ 2 + x + 1 := by nlinarith [sq_nonneg (x + 1 / 2)]
  have hs := mul_pos (sq_pos_of_ne_zero hx) hp
  unfold polynomialB2
  nlinarith

private lemma b2_lower (x : ℝ) : 1 + (3 / 4) * x ^ 2 ≤ polynomialB2 x := by
  have hp := mul_nonneg (sq_nonneg x) (sq_nonneg (x + 1 / 2))
  unfold polynomialB2
  nlinarith

private lemma polynomial_tail (b : ℝ → ℝ) (hb : ∀ x, 1 + (3 / 4) * x ^ 2 ≤ b x) :
    ∀ M : ℝ, ∃ R > (0 : ℝ), ∀ x : ℝ, R ≤ |x| → M ≤ b x := by
  intro M
  refine ⟨|M| + 2, by positivity, ?_⟩
  intro x hx
  have hp := mul_nonneg (by linarith [abs_nonneg M] : 0 ≤ |x| - 2) (abs_nonneg x)
  nlinarith [hb x, sq_abs x, le_abs_self M]

private lemma model_admissible (b : ℝ → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (hcd : ContDiff ℝ 1 b) (hb0 : b 0 = 1)
    (hb1 : ∀ x : ℝ, x ≠ 0 → 1 < b x)
    (hm : ∀ x < 0, deriv b x < 0) (hp : ∀ x : ℝ, 0 < x → 0 < deriv b x)
    (ht : ∀ M : ℝ, ∃ R > (0 : ℝ), ∀ x : ℝ, R ≤ |x| → M ≤ b x) :
    AdmissibleGeometry (realLineExample b (fun _ => 1) lam) := by
  refine ⟨hlam, fun _ _ => by norm_num [realLineExample], ?_, ?_, ?_⟩
  · refine ⟨1, ?_⟩
    rintro v ⟨x, _, rfl⟩
    exact le_rfl
  · exact ⟨0, Set.mem_univ _, by norm_num [realLineExample]⟩
  · exact ⟨contDiff_const, hcd, hb0, hb1, hm, hp, ht⟩

theorem solution : PolynomialPenaltyModelsClaim := by
  intro lam hlam
  refine ⟨pen1_second lam, pen2_second lam, ?_, fun x => (b2_deriv x).deriv, ?_⟩
  · intro x
    constructor
    · unfold polynomialB1
      nlinarith [sq_nonneg x]
    · exact (by nlinarith [sq_nonneg x] : 1 ≤ 1 + (3 / 4) * x ^ 2).trans (b2_lower x)
  · intro b hb
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hb :
      b = polynomialB1 ∨ b = polynomialB2) with rfl | rfl
    · apply model_admissible polynomialB1 lam hlam
      · unfold polynomialB1; fun_prop
      · norm_num [polynomialB1]
      · intro x hx
        unfold polynomialB1
        nlinarith [sq_pos_of_ne_zero hx]
      · intro x hx
        rw [(b1_deriv x).deriv]
        linarith
      · intro x hx
        rw [(b1_deriv x).deriv]
        linarith
      · apply polynomial_tail
        intro x
        unfold polynomialB1
        nlinarith [sq_nonneg x]
    · apply model_admissible polynomialB2 lam hlam
      · unfold polynomialB2; fun_prop
      · norm_num [polynomialB2]
      · exact b2_strict
      · intro x hx
        rw [(b2_deriv x).deriv]
        exact mul_neg_of_neg_of_pos hx (by nlinarith [sq_nonneg (x + 3 / 8)])
      · intro x hx
        rw [(b2_deriv x).deriv]
        exact mul_pos hx (by nlinarith [sq_nonneg (x + 3 / 8)])
      · exact polynomial_tail _ b2_lower
