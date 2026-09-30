-- Prove2me | solution 1 for UnderstandingML.adaboost_training_error
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T15:07:38.81298+00:00
-- url     : https://prove2.me/submissions/1cb72d87-7451-46b6-8ed5-38ad8ce5c6c3

import Definitions.Def_UnderstandingML_Boosting

open MeasureTheory

namespace UnderstandingML

section AdaBoostProof

variable {X : Type*} {m : ℕ}

/-- Cumulative margin `F_t(i) = ∑_{s<t} w_s y_i h_s(x_i)` of example `i` after `t` rounds. -/
private noncomputable def cumMargin (S : Fin m → X × Bool) (h : ℕ → X → Bool) (t : ℕ)
    (i : Fin m) : ℝ :=
  ∑ s ∈ Finset.range t, adaWeight (adaError S h s) * sgn (S i).2 * sgn (h s (S i).1)

/-- Normalizer `P_t = (1/m) ∑ᵢ exp(−F_t(i))`. -/
private noncomputable def potential (S : Fin m → X × Bool) (h : ℕ → X → Bool) (t : ℕ) : ℝ :=
  (∑ i, Real.exp (-cumMargin S h t i)) / m

private lemma sumExp_pos (S : Fin m → X × Bool) (h : ℕ → X → Bool) (t : ℕ) (hm : 0 < m) :
    0 < ∑ i, Real.exp (-cumMargin S h t i) := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty

private lemma potential_pos (S : Fin m → X × Bool) (h : ℕ → X → Bool) (t : ℕ) (hm : 0 < m) :
    0 < potential S h t := by
  unfold potential
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact div_pos (Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty)
    (by exact_mod_cast hm)

/-- Closed form of the AdaBoost distributions. -/
private lemma adaDist_eq (S : Fin m → X × Bool) (h : ℕ → X → Bool) (hm : 0 < m) (t : ℕ)
    (i : Fin m) :
    adaDist S h t i = Real.exp (-cumMargin S h t i) / (m * potential S h t) := by
  induction t generalizing i with
  | zero =>
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    simp [adaDist, cumMargin, potential, hm']
  | succ t ih =>
    have hP := potential_pos S h t hm
    have hP' := potential_pos S h (t + 1) hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hstep : ∀ j, Real.exp (-cumMargin S h (t + 1) j) = Real.exp (-cumMargin S h t j) *
        Real.exp (-(adaWeight (adaError S h t) * sgn (S j).2 * sgn (h t (S j).1))) := by
      intro j
      rw [← Real.exp_add]
      congr 1
      simp [cumMargin, Finset.sum_range_succ]
      ring
    have hsum : ∑ j, Real.exp (-cumMargin S h (t + 1) j) = m * potential S h (t + 1) := by
      unfold potential; field_simp
    have key : ∀ j, adaDist S h t j *
        Real.exp (-(adaWeight (adaError S h t) * sgn (S j).2 * sgn (h t (S j).1))) =
        Real.exp (-cumMargin S h (t + 1) j) / (m * potential S h t) := by
      intro j
      rw [ih, hstep]
      ring
    rw [show adaDist S h (t + 1) i = adaDist S h t i *
        Real.exp (-(adaWeight (adaError S h t) * sgn (S i).2 * sgn (h t (S i).1))) /
        ∑ j, adaDist S h t j *
          Real.exp (-(adaWeight (adaError S h t) * sgn (S j).2 * sgn (h t (S j).1))) from rfl]
    simp only [key]
    rw [← Finset.sum_div, hsum]
    field_simp

/-- The normalizers multiply by `Z_t = ∑ᵢ D⁽ᵗ⁾ᵢ exp(−wₜ yᵢ hₜ(xᵢ))`. -/
private lemma potential_succ (S : Fin m → X × Bool) (h : ℕ → X → Bool) (hm : 0 < m) (t : ℕ) :
    potential S h (t + 1) = potential S h t *
      ∑ i, adaDist S h t i *
        Real.exp (-(adaWeight (adaError S h t) * sgn (S i).2 * sgn (h t (S i).1))) := by
  have hP := potential_pos S h t hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  simp only [adaDist_eq S h hm]
  rw [Finset.mul_sum]
  unfold potential
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have : Real.exp (-cumMargin S h (t + 1) j) = Real.exp (-cumMargin S h t j) *
      Real.exp (-(adaWeight (adaError S h t) * sgn (S j).2 * sgn (h t (S j).1))) := by
    rw [← Real.exp_add]
    congr 1
    simp [cumMargin, Finset.sum_range_succ]
    ring
  rw [this]
  have := sumExp_pos S h t hm
  field_simp

/-- The AdaBoost distributions sum to one. -/
private lemma adaDist_sum (S : Fin m → X × Bool) (h : ℕ → X → Bool) (hm : 0 < m) (t : ℕ) :
    ∑ i, adaDist S h t i = 1 := by
  have hP := potential_pos S h t hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  simp only [adaDist_eq S h hm]
  rw [← Finset.sum_div]
  have := sumExp_pos S h t hm
  unfold potential
  field_simp

private lemma adaDist_nonneg (S : Fin m → X × Bool) (h : ℕ → X → Bool) (hm : 0 < m) (t : ℕ)
    (i : Fin m) : 0 ≤ adaDist S h t i := by
  rw [adaDist_eq S h hm]
  have := potential_pos S h t hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  positivity

/-- The one-round bound `Z_t ≤ exp(−2γ²)`. -/
private lemma round_factor_le (S : Fin m → X × Bool) (h : ℕ → X → Bool) (hm : 0 < m) (t : ℕ)
    {γ : ℝ} (hγ : 0 < γ) (hε : 0 < adaError S h t ∧ adaError S h t ≤ 1 / 2 - γ) :
    ∑ i, adaDist S h t i *
        Real.exp (-(adaWeight (adaError S h t) * sgn (S i).2 * sgn (h t (S i).1))) ≤
      Real.exp (-(2 * γ ^ 2)) := by
  set ε := adaError S h t with hεdef
  set w := adaWeight ε
  set a := Real.exp w with ha
  have ha0 : 0 < a := Real.exp_pos _
  have ha2 : a ^ 2 = 1 / ε - 1 := by
    rw [ha, ← Real.exp_nat_mul]
    simp only [w, adaWeight]
    rw [show ((2 : ℕ) : ℝ) * (1 / 2 * Real.log (1 / ε - 1)) = Real.log (1 / ε - 1) by push_cast; ring]
    apply Real.exp_log
    rw [sub_pos, lt_div_iff₀ hε.1]
    linarith
  -- rewrite each summand as `D i * (a⁻¹ + (a - a⁻¹) * 𝟙[wrong])`
  have hterm : ∀ i, adaDist S h t i * Real.exp (-(w * sgn (S i).2 * sgn (h t (S i).1))) =
      adaDist S h t i * a⁻¹ +
        (a - a⁻¹) * (adaDist S h t i * (if h t (S i).1 = (S i).2 then 0 else 1)) := by
    intro i
    rw [ha, ← Real.exp_neg]
    cases h1 : h t (S i).1 <;> cases h2 : (S i).2 <;> simp [sgn] <;> ring
  have hZ : ∑ i, adaDist S h t i * Real.exp (-(w * sgn (S i).2 * sgn (h t (S i).1))) =
      (1 - ε) * a⁻¹ + ε * a := by
    rw [Finset.sum_congr rfl fun i _ ↦ hterm i, Finset.sum_add_distrib, ← Finset.sum_mul,
      adaDist_sum S h hm, ← Finset.mul_sum]
    change 1 * a⁻¹ + (a - a⁻¹) * weightedError (adaDist S h t) S (h t) = _
    rw [← adaError, ← hεdef]
    ring
  show ∑ i, adaDist S h t i * Real.exp (-(w * sgn (S i).2 * sgn (h t (S i).1))) ≤ _
  rw [hZ]
  have hε1 : ε < 1 := by linarith
  -- `(1 - ε) a⁻¹ = ε a`, so `Z = 2 ε a` and `Z² = 4 ε (1 - ε)`
  have hεa : ε * a ^ 2 = 1 - ε := by rw [ha2, mul_sub, mul_one_div_cancel hε.1.ne', mul_one]
  have hkey : (1 - ε) * a⁻¹ = ε * a := by
    field_simp
    linarith
  rw [hkey]
  have hZsq : (ε * a + ε * a) ^ 2 = 4 * ε * (1 - ε) := by
    nlinarith [hεa]
  have hbound : 4 * ε * (1 - ε) ≤ 1 - 4 * γ ^ 2 := by nlinarith
  have hexp : 1 - 4 * γ ^ 2 ≤ Real.exp (-(2 * γ ^ 2)) ^ 2 := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * -(2 * γ ^ 2) = -(4 * γ ^ 2) by push_cast; ring]
    linarith [Real.add_one_le_exp (-(4 * γ ^ 2))]
  have h0 : 0 ≤ ε * a + ε * a := by have := hε.1; positivity
  exact (pow_le_pow_iff_left₀ h0 (Real.exp_pos _).le two_ne_zero).1 (by rw [hZsq]; linarith)

/-- The normalizer after `T` rounds is at most `exp(−2γ²T)`. -/
private lemma potential_le (S : Fin m → X × Bool) (h : ℕ → X → Bool) (hm : 0 < m) {γ : ℝ}
    (hγ : 0 < γ) (T : ℕ)
    (hε : ∀ t < T, 0 < adaError S h t ∧ adaError S h t ≤ 1 / 2 - γ) :
    potential S h T ≤ Real.exp (-(2 * γ ^ 2 * T)) := by
  induction T with
  | zero =>
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    simp [potential, cumMargin, hm']
  | succ T ih =>
    rw [potential_succ S h hm]
    have h1 := ih fun t ht ↦ hε t (by omega)
    have h2 := round_factor_le S h hm T hγ (hε T (by omega))
    have hZ0 : 0 ≤ ∑ i, adaDist S h T i *
        Real.exp (-(adaWeight (adaError S h T) * sgn (S i).2 * sgn (h T (S i).1))) :=
      Finset.sum_nonneg fun i _ ↦ mul_nonneg (adaDist_nonneg S h hm T i) (Real.exp_pos _).le
    calc _ ≤ Real.exp (-(2 * γ ^ 2 * T)) * Real.exp (-(2 * γ ^ 2)) :=
          mul_le_mul h1 h2 hZ0 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; push_cast; ring_nf

/-- The 0–1 loss of the AdaBoost output is bounded by the exponential loss. -/
private lemma loss01_le_exp (S : Fin m → X × Bool) (h : ℕ → X → Bool) (T : ℕ) (i : Fin m) :
    loss01 (adaBoost S h T) (S i) ≤ Real.exp (-cumMargin S h T i) := by
  have hF : cumMargin S h T i = sgn (S i).2 *
      ∑ t ∈ Finset.range T, adaWeight (adaError S h t) * sgn (h t (S i).1) := by
    unfold cumMargin
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [hF]
  unfold loss01 adaBoost
  set f := ∑ t ∈ Finset.range T, adaWeight (adaError S h t) * sgn (h t (S i).1)
  split_ifs with hc
  · exact (Real.exp_pos _).le
  · cases hy : (S i).2 <;> rw [hy] at hc <;> simp only [sgn] <;> simp at hc ⊢
    · linarith [Real.add_one_le_exp f]
    · linarith [Real.add_one_le_exp (-f)]

end AdaBoostProof

end UnderstandingML

open UnderstandingML in
theorem solution {X : Type*} {m : ℕ} (S : Fin m → X × Bool) (h : ℕ → X → Bool)
    (T : ℕ) {γ : ℝ} (hγ : 0 < γ)
    (hε : ∀ t < T, 0 < adaError S h t ∧ adaError S h t ≤ 1 / 2 - γ) :
    empRisk loss01 S (adaBoost S h T) ≤ Real.exp (-(2 * γ ^ 2 * T)) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp [empRisk]
    positivity
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  calc empRisk loss01 S (adaBoost S h T)
      ≤ potential S h T := by
        unfold empRisk potential
        gcongr with i
        exact loss01_le_exp S h T i
    _ ≤ _ := potential_le S h hm hγ T hε
