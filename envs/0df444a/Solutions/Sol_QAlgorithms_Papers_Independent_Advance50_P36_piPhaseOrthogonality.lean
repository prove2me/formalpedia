-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P36.piPhaseOrthogonality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:21:42.668204+00:00
-- url     : https://prove2.me/submissions/7dfbf572-1def-4215-bc04-05d90ac3a44d

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

lemma p36cS_negl (x : ℂ) : p36cS (-x) x = (Real.exp (-2 * Complex.normSq x) : ℂ) := by
  have := p36cS_neg (-x); rw [neg_neg, Complex.normSq_neg] at this; exact this

lemma p36q_realized (alpha : ℂ) : QuasiBellCoherentRealized alpha :=
  ⟨p36c_realized _, p36c_realized _, p36c_realized _, p36c_realized _⟩

lemma p36q_w2 (a b : Fin 2 → ℂ) :
    inner (𝕜 := ℂ) (coherentWord a) (coherentWord b) = p36cS (a 0) (b 0) * p36cS (a 1) (b 1) := by
  rw [p36c_inner, Fin.prod_univ_two]

lemma p36q_phase (theta : ℝ) (x y : ℂ) :
    modeBPhaseShift theta (coherentWord ![x, y]) =
      coherentWord ![x, y * Complex.exp (-(theta : ℂ) * Complex.I)] := by
  apply lp.ext
  funext k
  change Complex.exp (Complex.ofReal (-theta * (k 1 : ℝ)) * Complex.I) * coherentWord ![x, y] k = _
  rw [p36c_coef, p36c_coef]
  simp only [coherentWordCoefficient, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    coherentCoefficient]
  have hn : Complex.normSq (y * Complex.exp (-(theta : ℂ) * Complex.I)) = Complex.normSq y := by
    have : Complex.exp (-(theta:ℂ) * Complex.I) = Complex.exp (((-theta : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring_nf
    rw [this, Complex.normSq_mul, Complex.normSq_eq_norm_sq (Complex.exp _),
      Complex.norm_exp_ofReal_mul_I]; ring
  have he : Complex.exp (Complex.ofReal (-theta * (k 1 : ℝ)) * Complex.I) =
      Complex.exp (-(theta : ℂ) * Complex.I) ^ (k 1) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [hn, he, mul_pow]
  ring

lemma p36q_norm_sq (u : WordFock 2) (hu : inner (𝕜 := ℂ) u u = 1) :
    ‖u‖ = 1 := by
  have h2 : ‖u‖ ^ 2 = 1 := by rw [@norm_sq_eq_re_inner ℂ, hu]; simp
  have := norm_nonneg u
  nlinarith

lemma p36q_kappa_lt (alpha : ℂ) (h : alpha ≠ 0) : antipodalOverlap alpha < 1 := by
  unfold antipodalOverlap
  rw [← Real.exp_zero, Real.exp_lt_exp]
  have := Complex.normSq_pos.2 h
  linarith

lemma p36q_na (alpha : ℂ) :
    (quasiBellNormalization alpha 0 : ℂ) * (quasiBellNormalization alpha 0 : ℂ) =
      1 / (2 * (1 + (antipodalOverlap alpha : ℂ) ^ 2)) := by
  have h : quasiBellNormalization alpha 0 = 1 / Real.sqrt (2 * (1 + antipodalOverlap alpha ^ 2)) := by
    simp [quasiBellNormalization]
  rw [← Complex.ofReal_mul, h, div_mul_div_comm, one_mul, Real.mul_self_sqrt (by positivity)]
  push_cast; ring

lemma p36q_nb (alpha : ℂ) (ha : alpha ≠ 0) :
    (quasiBellNormalization alpha 1 : ℂ) * (quasiBellNormalization alpha 1 : ℂ) =
      1 / (2 * (1 - (antipodalOverlap alpha : ℂ) ^ 2)) := by
  have h : quasiBellNormalization alpha 1 = 1 / Real.sqrt (2 * (1 - antipodalOverlap alpha ^ 2)) := by
    have h1 : ¬ ((1 : Fin 4) = 0 ∨ (1 : Fin 4) = 2) := by decide
    simp only [quasiBellNormalization, if_neg h1]
  have hk := p36q_kappa_lt alpha ha
  have hk0 : 0 < antipodalOverlap alpha := Real.exp_pos _
  rw [← Complex.ofReal_mul, h, div_mul_div_comm, one_mul, Real.mul_self_sqrt (by nlinarith)]
  push_cast; ring

lemma p36q_n2 (alpha : ℂ) : quasiBellNormalization alpha 2 = quasiBellNormalization alpha 0 := by
  simp [quasiBellNormalization]

lemma p36q_n3 (alpha : ℂ) : quasiBellNormalization alpha 3 = quasiBellNormalization alpha 1 := by
  have h3 : ¬ ((3 : Fin 4) = 0 ∨ (3 : Fin 4) = 2) := by decide
  have h1 : ¬ ((1 : Fin 4) = 0 ∨ (1 : Fin 4) = 2) := by decide
  simp only [quasiBellNormalization, if_neg h3, if_neg h1]

/-- Gram values of the four product coherent words. -/
lemma p36q_g (alpha : ℂ) :
    let A := coherentWord ![alpha, alpha]
    let B := coherentWord ![-alpha, -alpha]
    let C := coherentWord ![alpha, -alpha]
    let D := coherentWord ![-alpha, alpha]
    let k : ℂ := (antipodalOverlap alpha : ℂ)
    inner (𝕜 := ℂ) A A = 1 ∧ inner (𝕜 := ℂ) B B = 1 ∧ inner (𝕜 := ℂ) C C = 1 ∧
    inner (𝕜 := ℂ) D D = 1 ∧
    inner (𝕜 := ℂ) A B = k ^ 2 ∧ inner (𝕜 := ℂ) B A = k ^ 2 ∧
    inner (𝕜 := ℂ) C D = k ^ 2 ∧ inner (𝕜 := ℂ) D C = k ^ 2 ∧
    inner (𝕜 := ℂ) A C = k ∧ inner (𝕜 := ℂ) C A = k ∧
    inner (𝕜 := ℂ) A D = k ∧ inner (𝕜 := ℂ) D A = k ∧
    inner (𝕜 := ℂ) B C = k ∧ inner (𝕜 := ℂ) C B = k ∧
    inner (𝕜 := ℂ) B D = k ∧ inner (𝕜 := ℂ) D B = k := by
  intro A B C D k
  simp only [A, B, C, D, k, p36q_w2, Matrix.cons_val_zero, Matrix.cons_val_one, p36cS_self, p36cS_neg,
    p36cS_negl, antipodalOverlap]
  simp only [mul_one, one_mul, sq, and_self]

lemma p36q_smul_inner (c d : ℝ) (u v : WordFock 2) :
    inner (𝕜 := ℂ) ((c : ℂ) • u) ((d : ℂ) • v) = ((c : ℂ) * (d : ℂ)) * inner (𝕜 := ℂ) u v := by
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]; ring

lemma p36q_phase_lin (theta : ℝ) (c : ℂ) (u v : WordFock 2) :
    modeBPhaseShift theta (c • (u - v)) = c • (modeBPhaseShift theta u - modeBPhaseShift theta v) := by
  apply lp.ext; funext k
  change Complex.exp (Complex.ofReal (-theta * (k 1 : ℝ)) * Complex.I) * (c * (u k - v k)) =
    c * (Complex.exp (Complex.ofReal (-theta * (k 1 : ℝ)) * Complex.I) * u k -
      Complex.exp (Complex.ofReal (-theta * (k 1 : ℝ)) * Complex.I) * v k)
  ring

lemma p36q_exp_pi : Complex.exp (-((Real.pi : ℝ) : ℂ) * Complex.I) = -1 := by
  rw [neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num

end QAlgorithms.Papers.Independent.Advance50.P36

open QAlgorithms.Papers.Independent.Advance50.P36
open QAlgorithms.Papers.Independent.Frontier30.P21
  (WordFock coherentWord CoherentWordRealized binaryErrorValues)

theorem solution (alpha : ℂ) (halpha : alpha ≠ 0) :
    QuasiBellCoherentRealized alpha ∧
    ‖quasiBellState alpha 1‖ = 1 ∧ ‖quasiBellState alpha 3‖ = 1 ∧
    modeBPhaseShift Real.pi (quasiBellState alpha 1) = quasiBellState alpha 3 ∧
    inner (𝕜 := ℂ) (quasiBellState alpha 1) (quasiBellState alpha 3) = 0 := by
  obtain ⟨gAA, gBB, gCC, gDD, gAB, gBA, gCD, gDC, gAC, gCA, gAD, gDA, gBC, gCB, gBD, gDB⟩ :=
    p36q_g alpha
  have hb := p36q_nb alpha halpha
  have hk := p36q_kappa_lt alpha halpha
  have hk0 : 0 < antipodalOverlap alpha := Real.exp_pos _
  have hne : (1 - (antipodalOverlap alpha : ℂ) ^ 2) ≠ 0 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_ne_zero]
    nlinarith
  have h1 : quasiBellState alpha 1 = (quasiBellNormalization alpha 1 : ℂ) •
      (coherentWord ![alpha, alpha] - coherentWord ![-alpha, -alpha]) := by simp [quasiBellState]
  have h3 : quasiBellState alpha 3 = (quasiBellNormalization alpha 1 : ℂ) •
      (coherentWord ![alpha, -alpha] - coherentWord ![-alpha, alpha]) := by
    simp [quasiBellState, p36q_n3]
  refine ⟨p36q_realized alpha, ?_, ?_, ?_, ?_⟩
  · apply p36q_norm_sq
    rw [h1, p36q_smul_inner, hb]
    simp only [inner_sub_left, inner_sub_right, gAA, gBB, gAB, gBA]
    field_simp; ring
  · apply p36q_norm_sq
    rw [h3, p36q_smul_inner, hb]
    simp only [inner_sub_left, inner_sub_right, gCC, gDD, gCD, gDC]
    field_simp; ring
  · rw [h1, h3, p36q_phase_lin, p36q_phase, p36q_phase, p36q_exp_pi]
    simp
  · rw [h1, h3, p36q_smul_inner]
    simp only [inner_sub_left, inner_sub_right, gAC, gAD, gBC, gBD]
    ring

end
