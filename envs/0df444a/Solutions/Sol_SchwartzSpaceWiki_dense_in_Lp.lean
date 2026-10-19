-- Prove2me | solution 1 for SchwartzSpaceWiki.dense_in_Lp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T12:19:18.823418+00:00
-- url     : https://prove2.me/submissions/43f32284-21b1-499d-98c4-286bf9eefa24

import Theorems.Thm_SchwartzSpaceWiki_contDiff_hasCompactSupport_mem

open SchwartzSpaceWiki MeasureTheory
open scoped ENNReal

private lemma multi_zero {n : ℕ} (f : Rn n → ℂ) :
    iteratedPartialDeriv (0 : MultiIndex n) f = f := by
  have h : ∀ l : List (Fin n),
      l.foldr (fun i g => (partialDeriv i)^[(0 : MultiIndex n) i] g) f = f := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih => simp_all
  exact h (List.finRange n)

private lemma monomial_bound {n : ℕ} (f : Rn n → ℂ) (hf : f ∈ schwartzSpace n)
    (α : MultiIndex n) : ∃ C : ℝ, ∀ x, ‖(monomial α x : ℂ) * f x‖ ≤ C := by
  refine ⟨(schwartzSeminorm α 0 f).toReal, fun x => ?_⟩
  have h := le_iSup (fun y : Rn n =>
    ‖(monomial α y : ℂ) * iteratedPartialDeriv 0 f y‖ₑ) x
  have h' : ‖(monomial α x : ℂ) * f x‖ₑ ≤ schwartzSeminorm α 0 f := by
    simpa only [schwartzSeminorm, multi_zero] using h
  exact_mod_cast ENNReal.toReal_mono (hf.2 α 0).ne h'

private lemma polynomial_bound {n : ℕ} (f : Rn n → ℂ) (hf : f ∈ schwartzSpace n)
    (P : MvPolynomial (Fin n) ℂ) :
    ∃ C : ℝ, ∀ x, ‖MvPolynomial.eval (fun i => (x i : ℂ)) P * f x‖ ≤ C := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    obtain ⟨C, hC⟩ := monomial_bound f hf (fun i => d i)
    refine ⟨‖c‖ * C, fun x => ?_⟩
    have he : MvPolynomial.eval (fun i => (x i : ℂ)) (MvPolynomial.monomial d c) =
        c * (monomial (fun i => d i) x : ℂ) := by
      rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      simp [monomial]
    rw [he, mul_assoc, norm_mul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)
  | add P Q hP hQ =>
    obtain ⟨CP, hCP⟩ := hP
    obtain ⟨CQ, hCQ⟩ := hQ
    refine ⟨CP + CQ, fun x => ?_⟩
    simpa only [map_add, add_mul] using
      (norm_add_le (MvPolynomial.eval (fun i => (x i : ℂ)) P * f x)
        (MvPolynomial.eval (fun i => (x i : ℂ)) Q * f x)).trans
        (add_le_add (hCP x) (hCQ x))

private lemma power_bound {n : ℕ} (f : Rn n → ℂ) (hf : f ∈ schwartzSpace n)
    (k : ℕ) : ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖f x‖ ≤ C := by
  classical
  let P : MvPolynomial (Fin n) ℂ := (1 + ∑ i : Fin n, MvPolynomial.X i ^ 2) ^ k
  obtain ⟨C, hC⟩ := polynomial_bound f hf P
  refine ⟨C, fun x => ?_⟩
  have he : MvPolynomial.eval (fun i => (x i : ℂ)) P =
      ((1 + ‖x‖ ^ 2 : ℝ) : ℂ) ^ k := by
    simp only [P, map_pow, map_add, map_one, map_sum, MvPolynomial.eval_X]
    congr 2
    exact_mod_cast congrArg (fun t : ℝ => 1 + t) (EuclideanSpace.real_norm_sq_eq x).symm
  have hx : ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]
  calc
    ‖x‖ ^ k * ‖f x‖ ≤ (1 + ‖x‖ ^ 2) ^ k * ‖f x‖ := by
      gcongr
    _ = ‖MvPolynomial.eval (fun i => (x i : ℂ)) P * f x‖ := by
      rw [he, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ ≤ C := hC x

private lemma schwartz_memLp {n : ℕ} (f : Rn n → ℂ) (hf : f ∈ schwartzSpace n)
    (p : ℝ≥0∞) : MemLp f p (volume : Measure (Rn n)) := by
  obtain ⟨k, hk⟩ := (inferInstance : (volume : Measure (Rn n)).HasTemperateGrowth).exists_eLpNorm_lt_top p
  have hc : Continuous (fun x : Rn n => (1 + ‖x‖) ^ (-(k : ℝ))) := by
    apply Continuous.rpow_const (continuous_const.add continuous_norm)
    intro x
    left
    exact (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg x)).ne'
  have hm : MemLp (fun x : Rn n => (1 + ‖x‖) ^ (-(k : ℝ))) p volume :=
    ⟨hc.aestronglyMeasurable, hk⟩
  obtain ⟨C₀, hC₀⟩ := power_bound f hf 0
  obtain ⟨Ck, hCk⟩ := power_bound f hf k
  apply hm.of_le_mul hf.1.continuous.aestronglyMeasurable
    (c := 2 ^ k * (C₀ + Ck))
  filter_upwards with x
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  simpa using pow_mul_le_of_le_of_pow_mul_le (k := 0) (l := k)
    (norm_nonneg x) (norm_nonneg (f x)) (by simpa using hC₀ x) (by simpa using hCk x)

theorem solution (n : ℕ) (p : ENNReal) (hp1 : 1 ≤ p) (hptop : p ≠ ⊤) :
    (∀ f ∈ schwartzSpace n, MemLp f p (volume : Measure (Rn n))) ∧
    (∀ g : Rn n → ℂ, MemLp g p (volume : Measure (Rn n)) →
      ∀ ε : ENNReal, 0 < ε →
        ∃ f ∈ schwartzSpace n, eLpNorm (g - f) p (volume : Measure (Rn n)) < ε) := by
  refine ⟨fun f hf => schwartz_memLp f hf p, ?_⟩
  intro g hg ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  have hδ' : 0 < (δ : ℝ) := by exact_mod_cast hδ
  obtain ⟨f, hfc, hfs, hfg⟩ := hg.exist_eLpNorm_sub_le hptop hp1 hδ'
  refine ⟨f, contDiff_hasCompactSupport_mem n f hfs hfc, hfg.trans_lt ?_⟩
  simpa using hδε
