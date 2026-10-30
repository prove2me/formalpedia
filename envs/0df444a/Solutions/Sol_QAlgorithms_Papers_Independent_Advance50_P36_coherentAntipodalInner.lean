-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P36.coherentAntipodalInner
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:14:59.847201+00:00
-- url     : https://prove2.me/submissions/127ebae7-611e-47fc-9ec5-c9a85ac94796

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P36
noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P36

open QAlgorithms.Papers.Independent.Frontier30.P21
  (WordFock coherentWord CoherentWordRealized binaryErrorValues)

open scoped Matrix

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)
open QAlgorithms.Papers.Independent.Frontier30.P21 (coherentWordCoefficient)

def p36cS (x y : ℂ) : ℂ :=
  ((Real.exp (-Complex.normSq x / 2) * Real.exp (-Complex.normSq y / 2) : ℝ) : ℂ) *
    Complex.exp ((starRingEnd ℂ) x * y)

lemma p36c_pt (x y : ℂ) (n : ℕ) :
    coherentCoefficient y n * (starRingEnd ℂ) (coherentCoefficient x n) =
      ((Real.exp (-Complex.normSq x / 2) * Real.exp (-Complex.normSq y / 2) : ℝ) : ℂ) *
        (((starRingEnd ℂ) x * y) ^ n / (Nat.factorial n : ℂ)) := by
  have hs : ((Real.sqrt (Nat.factorial n : ℝ) : ℝ) : ℂ) * ((Real.sqrt (Nat.factorial n : ℝ) : ℝ) : ℂ)
      = (Nat.factorial n : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]; push_cast; rfl
  have hne : ((Real.sqrt (Nat.factorial n : ℝ) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  simp only [coherentCoefficient, map_div₀, map_mul, map_pow, Complex.conj_ofReal]
  rw [← hs]
  push_cast
  field_simp
  ring

lemma p36c_single (x y : ℂ) :
    Summable (fun n => ‖coherentCoefficient y n * (starRingEnd ℂ) (coherentCoefficient x n)‖) ∧
    HasSum (fun n => coherentCoefficient y n * (starRingEnd ℂ) (coherentCoefficient x n))
      (p36cS x y) := by
  simp only [p36c_pt]
  constructor
  · simp only [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    exact (Real.summable_pow_div_factorial _).mul_left _
  · unfold p36cS
    apply HasSum.mul_left
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _

lemma p36c_word (L : ℕ) : ∀ a b : Fin L → ℂ,
    Summable (fun k => ‖coherentWordCoefficient b k * (starRingEnd ℂ) (coherentWordCoefficient a k)‖) ∧
    HasSum (fun k => coherentWordCoefficient b k * (starRingEnd ℂ) (coherentWordCoefficient a k))
      (∏ i, p36cS (a i) (b i)) := by
  induction L with
  | zero =>
    intro a b
    simp only [coherentWordCoefficient, Finset.univ_eq_empty, Finset.prod_empty, map_one, mul_one,
      norm_one]
    exact ⟨Summable.of_finite, by
      simpa using hasSum_fintype (fun _ : Fin 0 → ℕ => (1:ℂ))⟩
  | succ L ih =>
    intro a b
    obtain ⟨h1, h2⟩ := ih (Fin.tail a) (Fin.tail b)
    obtain ⟨g1, g2⟩ := p36c_single (a 0) (b 0)
    let e := Fin.consEquiv (fun _ : Fin (L+1) => ℕ)
    have hpt : ∀ c : Fin (L+1) → ℂ, ∀ p : ℕ × (Fin L → ℕ),
        coherentWordCoefficient c (e p) =
          coherentCoefficient (c 0) p.1 * coherentWordCoefficient (Fin.tail c) p.2 := by
      intro c p
      simp only [coherentWordCoefficient, Fin.prod_univ_succ, e, Fin.consEquiv_apply, Fin.cons_zero,
        Fin.cons_succ, Fin.tail]
    have hf : ∀ p : ℕ × (Fin L → ℕ),
        coherentWordCoefficient b (e p) * (starRingEnd ℂ) (coherentWordCoefficient a (e p)) =
          (coherentCoefficient (b 0) p.1 * (starRingEnd ℂ) (coherentCoefficient (a 0) p.1)) *
          (coherentWordCoefficient (Fin.tail b) p.2 *
            (starRingEnd ℂ) (coherentWordCoefficient (Fin.tail a) p.2)) := by
      intro p; rw [hpt, hpt, map_mul]; ring
    constructor
    · rw [← e.summable_iff]
      have := Summable.mul_of_nonneg g1 h1 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      refine this.congr (fun p => ?_)
      simp only [Function.comp, hf, norm_mul]
    · rw [← e.hasSum_iff, Fin.prod_univ_succ]
      have := HasSum.mul g2 h2 (summable_mul_of_summable_norm
        (f := fun n => coherentCoefficient (b 0) n * (starRingEnd ℂ) (coherentCoefficient (a 0) n))
        (g := fun k => coherentWordCoefficient (Fin.tail b) k *
            (starRingEnd ℂ) (coherentWordCoefficient (Fin.tail a) k)) g1 h1)
      rw [show ((fun k => coherentWordCoefficient b k * (starRingEnd ℂ) (coherentWordCoefficient a k)) ∘ e)
        = fun p => (coherentCoefficient (b 0) p.1 * (starRingEnd ℂ) (coherentCoefficient (a 0) p.1)) *
          (coherentWordCoefficient (Fin.tail b) p.2 *
            (starRingEnd ℂ) (coherentWordCoefficient (Fin.tail a) p.2)) from funext hf]
      exact this

lemma p36cS_self (x : ℂ) : p36cS x x = 1 := by
  unfold p36cS
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_mul, Complex.ofReal_exp,
    ← Complex.exp_add, ← Complex.exp_add]
  rw [← Complex.exp_zero]; congr 1; push_cast; ring

lemma p36c_mem {L : ℕ} (a : Fin L → ℂ) : Memℓp (coherentWordCoefficient a) 2 := by
  apply memℓp_gen
  refine ((p36c_word L a a).1).congr (fun k => ?_)
  simp only [norm_mul, Complex.norm_conj, ENNReal.toReal_ofNat, Real.rpow_two]
  ring

lemma p36c_coef {L : ℕ} (a : Fin L → ℂ) (k : Fin L → ℕ) :
    coherentWord a k = coherentWordCoefficient a k := by
  have h : ∃ u : WordFock L, ∀ occupation, u occupation = coherentWordCoefficient a occupation :=
    ⟨⟨coherentWordCoefficient a, p36c_mem a⟩, fun _ => rfl⟩
  unfold coherentWord
  rw [dif_pos h]
  exact Classical.choose_spec h k

lemma p36c_inner {L : ℕ} (a b : Fin L → ℂ) :
    inner (𝕜 := ℂ) (coherentWord a) (coherentWord b) = ∏ i, p36cS (a i) (b i) := by
  refine (lp.hasSum_inner (coherentWord a) (coherentWord b)).unique ?_
  refine ((p36c_word L a b).2).congr_fun (fun k => ?_)
  simp [p36c_coef]

lemma p36c_realized {L : ℕ} (a : Fin L → ℂ) : CoherentWordRealized a := by
  refine ⟨p36c_coef a, ?_⟩
  have h2 : ‖coherentWord a‖ ^ 2 = 1 := by
    rw [@norm_sq_eq_re_inner ℂ, p36c_inner]; simp [p36cS_self]
  have := norm_nonneg (coherentWord a)
  nlinarith

lemma p36cS_eq (x y : ℂ) : p36cS x y =
    Complex.exp (-(Complex.normSq x : ℂ) / 2 - (Complex.normSq y : ℂ) / 2 + (starRingEnd ℂ) x * y) := by
  unfold p36cS
  rw [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1; push_cast; ring

lemma p36cS_neg (x : ℂ) : p36cS x (-x) = (Real.exp (-2 * Complex.normSq x) : ℂ) := by
  rw [p36cS_eq, Complex.ofReal_exp, mul_neg, ← Complex.normSq_eq_conj_mul_self]
  congr 1; simp only [Complex.normSq_neg]; push_cast; ring

end QAlgorithms.Papers.Independent.Advance50.P36

open QAlgorithms.Papers.Independent.Advance50.P36
open QAlgorithms.Papers.Independent.Frontier30.P21
  (WordFock coherentWord CoherentWordRealized binaryErrorValues)

theorem solution (alpha : ℂ) :
    CoherentWordRealized ![alpha] ∧ CoherentWordRealized ![-alpha] ∧
    inner (𝕜 := ℂ) (coherentWord ![alpha]) (coherentWord ![-alpha]) =
      (Real.exp (-2 * Complex.normSq alpha) : ℂ) := by
  refine ⟨p36c_realized _, p36c_realized _, ?_⟩
  rw [p36c_inner, Fin.prod_univ_one]
  simpa using p36cS_neg alpha
end
