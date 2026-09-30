-- Prove2me | solution 1 for UnderstandingML.massart_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T15:52:25.443544+00:00
-- url     : https://prove2.me/submissions/2868074d-386c-40a3-9de2-a5f959643f2a

import Definitions.Def_UnderstandingML_Rademacher
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Logic.Equiv.Bool

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML.MassartAux

/-- Flipping every sign is a bijection of `{±1}^m`, so the signs average to zero. -/
lemma sum_signVec_eq_zero {m : ℕ} (i : Fin m) :
    ∑ σ : Fin m → Bool, signVec σ i = 0 := by
  have h : ∑ σ : Fin m → Bool, signVec σ i =
      ∑ σ : Fin m → Bool, signVec (fun j ↦ !σ j) i :=
    (Fintype.sum_equiv (Equiv.piCongrRight fun (_ : Fin m) ↦ Equiv.boolNot) _ _
      (fun _ ↦ rfl)).symm
  have h2 : ∀ σ : Fin m → Bool, signVec (fun j ↦ !σ j) i = - signVec σ i := by
    intro σ; unfold signVec; cases h : σ i <;> simp [h]
  simp only [h2, Finset.sum_neg_distrib] at h
  linarith

/-- The sum of `exp (λ ⟨σ, u⟩)` over sign vectors is `2^m ∏ cosh (λ uᵢ)`. -/
lemma sum_exp_signVec {m : ℕ} (l : ℝ) (u : Fin m → ℝ) :
    ∑ σ : Fin m → Bool, Real.exp (l * ∑ i, signVec σ i * u i) =
      2 ^ m * ∏ i, Real.cosh (l * u i) := by
  have h := Fintype.prod_sum (fun (i : Fin m) (b : Bool) ↦
    Real.exp (l * ((if b then 1 else -1) * u i)))
  have e : ∀ σ : Fin m → Bool, Real.exp (l * ∑ i, signVec σ i * u i) =
      ∏ i, Real.exp (l * ((if σ i then 1 else -1) * u i)) := by
    intro σ
    rw [Finset.mul_sum, Real.exp_sum]
    rfl
  rw [Finset.sum_congr rfl (fun σ _ ↦ e σ), ← h]
  rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ ↦ ?_)
  rw [Fintype.sum_bool, Real.cosh_eq]
  simp only [if_true, one_mul, Bool.false_eq_true, if_false, neg_mul, mul_neg]
  ring

lemma sum_exp_signVec_le {m : ℕ} (l : ℝ) (u : Fin m → ℝ) :
    ∑ σ : Fin m → Bool, Real.exp (l * ∑ i, signVec σ i * u i) ≤
      2 ^ m * Real.exp (l ^ 2 * (∑ i, u i ^ 2) / 2) := by
  rw [sum_exp_signVec]
  gcongr
  calc ∏ i, Real.cosh (l * u i) ≤ ∏ i, Real.exp ((l * u i) ^ 2 / 2) :=
        Finset.prod_le_prod (fun i _ ↦ (Real.cosh_pos _).le)
          (fun i _ ↦ Real.cosh_le_exp_half_sq _)
    _ = Real.exp (l ^ 2 * (∑ i, u i ^ 2) / 2) := by
        rw [← Real.exp_sum]; congr 1; rw [Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl (fun i _ ↦ ?_); ring

/-- If `X ≤ a/λ + λ b` for every `λ > 0` with `a, b ≥ 0`, then `X ≤ 2 √(a b)`. -/
lemma le_of_forall_lambda {X a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ l : ℝ, 0 < l → X ≤ a / l + l * b) : X ≤ 2 * Real.sqrt (a * b) := by
  rcases ha.lt_or_eq with ha | ha
  · rcases hb.lt_or_eq with hb | hb
    · set s := Real.sqrt (a / b) with hs_def
      have hl : 0 < s := Real.sqrt_pos.2 (div_pos ha hb)
      have hs : s ^ 2 = a / b := Real.sq_sqrt (div_pos ha hb).le
      have e1 : a / s = s * b := by
        rw [div_eq_iff hl.ne']
        have : s * b * s = s ^ 2 * b := by ring
        rw [this, hs, div_mul_cancel₀ _ hb.ne']
      have e2 : s * b = Real.sqrt (a * b) := by
        rw [← Real.sqrt_sq (by positivity : 0 ≤ s * b)]
        congr 1
        rw [mul_pow, hs]; field_simp
      have := h _ hl
      rw [e1, e2] at this
      linarith
    · subst hb
      simp only [mul_zero, Real.sqrt_zero, add_zero] at h ⊢
      refine le_of_forall_pos_le_add (fun ε hε ↦ ?_)
      have := h (a / ε + 1) (by positivity)
      have h2 : a / (a / ε + 1) ≤ ε := by
        rw [div_le_iff₀ (by positivity)]
        have : ε * (a / ε + 1) = a + ε := by field_simp
        rw [this]; linarith
      linarith
  · subst ha
    simp only [zero_div, zero_add, zero_mul, Real.sqrt_zero, mul_zero] at h ⊢
    refine le_of_forall_pos_le_add (fun ε hε ↦ ?_)
    have := h (ε / (b + 1)) (by positivity)
    have h2 : ε / (b + 1) * b ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith

end UnderstandingML.MassartAux

open UnderstandingML UnderstandingML.MassartAux in
theorem solution {m : ℕ} (A : Finset (Fin m → ℝ)) (hA : A.Nonempty) :
    rademacher (↑A : Set (Fin m → ℝ)) ≤
      (⨆ a : A, Real.sqrt (∑ i, ((a : Fin m → ℝ) i - (∑ b ∈ A, b i) / A.card) ^ 2)) *
        Real.sqrt (2 * Real.log A.card) / m := by
  classical
  -- notation
  set N : ℕ := A.card with hN
  set abar : Fin m → ℝ := fun i ↦ (∑ b ∈ A, b i) / N with habar
  set r : ℝ := ⨆ a : A, Real.sqrt (∑ i, ((a : Fin m → ℝ) i - (∑ b ∈ A, b i) / N) ^ 2) with hr
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hA.card_pos
  have : Nonempty (↑A : Set (Fin m → ℝ)) := hA.coe_sort
  have hfin : ∀ f : (↑A : Set (Fin m → ℝ)) → ℝ, BddAbove (Set.range f) :=
    fun f ↦ (Set.finite_range f).bddAbove
  -- every `a ∈ A` has `‖a − ā‖² ≤ r²`
  have hr0 : 0 ≤ r := by
    obtain ⟨a, ha⟩ := hA
    exact le_trans (Real.sqrt_nonneg _) (le_ciSup (f := fun a : (↑A : Set (Fin m → ℝ)) ↦
        Real.sqrt (∑ i, ((a : Fin m → ℝ) i - (∑ b ∈ A, b i) / N) ^ 2)) (hfin _) ⟨a, ha⟩)
  have hnorm : ∀ a ∈ A, ∑ i, (a i - abar i) ^ 2 ≤ r ^ 2 := by
    intro a ha
    have h1 : Real.sqrt (∑ i, (a i - abar i) ^ 2) ≤ r :=
      le_ciSup (f := fun a : (↑A : Set (Fin m → ℝ)) ↦
        Real.sqrt (∑ i, ((a : Fin m → ℝ) i - (∑ b ∈ A, b i) / N) ^ 2)) (hfin _) ⟨a, ha⟩
    have h2 : 0 ≤ ∑ i, (a i - abar i) ^ 2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
    calc ∑ i, (a i - abar i) ^ 2 = Real.sqrt (∑ i, (a i - abar i) ^ 2) ^ 2 :=
          (Real.sq_sqrt h2).symm
      _ ≤ r ^ 2 := by gcongr
  -- the per-sign-vector supremum
  set M : (Fin m → Bool) → ℝ := fun σ ↦
    ⨆ a : (↑A : Set (Fin m → ℝ)), ∑ i, signVec σ i * (a : Fin m → ℝ) i with hM
  have hsum_abar : ∑ σ : Fin m → Bool, ∑ i, signVec σ i * abar i = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun i _ ↦ ?_)
    rw [← Finset.sum_mul, sum_signVec_eq_zero, zero_mul]
  -- the key exponential-moment bound, for every `λ > 0`
  have key : ∀ l : ℝ, 0 < l →
      (1 / 2 ^ m) * ∑ σ, M σ ≤ Real.log N / l + l * (r ^ 2 / 2) := by
    intro l hl
    set Y : (Fin m → Bool) → ℝ := fun σ ↦ M σ - ∑ i, signVec σ i * abar i with hY
    have hYsum : ∑ σ, M σ = ∑ σ, Y σ := by
      simp only [hY, Finset.sum_sub_distrib, hsum_abar, sub_zero]
    -- `exp (λ Y σ) ≤ ∑_{a ∈ A} exp (λ ⟨σ, a − ā⟩)`
    have hYexp : ∀ σ, Real.exp (l * Y σ) ≤
        ∑ a ∈ A, Real.exp (l * ∑ i, signVec σ i * (a i - abar i)) := by
      intro σ
      obtain ⟨a, ha⟩ := exists_eq_ciSup_of_finite
        (f := fun a : (↑A : Set (Fin m → ℝ)) ↦ ∑ i, signVec σ i * (a : Fin m → ℝ) i)
      have : Y σ = ∑ i, signVec σ i * ((a : Fin m → ℝ) i - abar i) := by
        simp only [hY, hM, ← ha, mul_sub, Finset.sum_sub_distrib]
      rw [this]
      exact Finset.single_le_sum (f := fun a ↦ Real.exp (l * ∑ i, signVec σ i * (a i - abar i)))
        (fun _ _ ↦ (Real.exp_pos _).le) a.2
    -- Jensen for `exp`
    have hjensen : Real.exp (l * ((1 / 2 ^ m) * ∑ σ, Y σ)) ≤
        (1 / 2 ^ m) * ∑ σ, Real.exp (l * Y σ) := by
      have := (convexOn_exp).map_sum_le (t := Finset.univ) (w := fun _ ↦ (1 / 2 ^ m : ℝ))
        (p := fun σ : Fin m → Bool ↦ l * Y σ) (fun _ _ ↦ by positivity)
        (by simp [Finset.card_univ, Fintype.card_bool, Fintype.card_fin])
        (fun _ _ ↦ Set.mem_univ _)
      simp only [smul_eq_mul] at this
      have e1 : l * ((1 / 2 ^ m) * ∑ σ, Y σ) = ∑ σ, (1 / 2 ^ m : ℝ) * (l * Y σ) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
      rw [e1, Finset.mul_sum]
      exact this
    have hbound : (1 / 2 ^ m) * ∑ σ, Real.exp (l * Y σ) ≤
        N * Real.exp (l ^ 2 * r ^ 2 / 2) := by
      calc (1 / 2 ^ m) * ∑ σ, Real.exp (l * Y σ)
          ≤ (1 / 2 ^ m) * ∑ σ, ∑ a ∈ A, Real.exp (l * ∑ i, signVec σ i * (a i - abar i)) := by
            gcongr with σ; exact hYexp σ
        _ = ∑ a ∈ A, (1 / 2 ^ m) * ∑ σ, Real.exp (l * ∑ i, signVec σ i * (a i - abar i)) := by
            rw [Finset.sum_comm, Finset.mul_sum]
        _ ≤ ∑ a ∈ A, (1 / 2 ^ m) * (2 ^ m * Real.exp (l ^ 2 * r ^ 2 / 2)) := by
            refine Finset.sum_le_sum (fun a ha ↦ ?_)
            gcongr
            refine (sum_exp_signVec_le l (fun i ↦ a i - abar i)).trans ?_
            gcongr
            exact hnorm a ha
        _ = N * Real.exp (l ^ 2 * r ^ 2 / 2) := by
            rw [Finset.sum_const, nsmul_eq_mul, ← hN]; field_simp
    have hlog : l * ((1 / 2 ^ m) * ∑ σ, Y σ) ≤ Real.log N + l ^ 2 * r ^ 2 / 2 := by
      rw [← Real.log_exp (l * _), ← Real.log_exp (l ^ 2 * r ^ 2 / 2),
        ← Real.log_mul hNpos.ne' (Real.exp_pos _).ne']
      exact Real.log_le_log (Real.exp_pos _) (hjensen.trans hbound)
    rw [hYsum]
    rw [div_add' _ _ _ hl.ne', le_div_iff₀ hl]
    nlinarith [hlog]
  -- optimize over `λ`
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hA.card_pos)
  have hopt := le_of_forall_lambda hlogN (by positivity : 0 ≤ r ^ 2 / 2) key
  have hsq : 2 * Real.sqrt (Real.log N * (r ^ 2 / 2)) = r * Real.sqrt (2 * Real.log N) := by
    have : Real.log N * (r ^ 2 / 2) = (r / 2) ^ 2 * (2 * Real.log N) := by ring
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    ring
  rw [hsq] at hopt
  -- conclude
  change (1 / (m : ℝ)) * ((1 / 2 ^ m) * ∑ σ, M σ) ≤ r * Real.sqrt (2 * Real.log N) / m
  rw [one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right hopt (Nat.cast_nonneg m)
