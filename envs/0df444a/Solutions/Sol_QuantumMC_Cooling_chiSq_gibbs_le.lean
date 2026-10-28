-- Prove2me | solution 1 for QuantumMC.Cooling.chiSq_gibbs_le
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:41:42.790693+00:00
-- url     : https://prove2.me/submissions/b9876dba-0748-4f51-a882-16875595116b

import Definitions.Def_QuantumMC_Cooling_Setting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false
open QuantumMC.Cooling Finset
open scoped ENNReal

private lemma weight_nonneg (b : ℝ≥0∞) (h : ℕ) : 0 ≤ weight b h := by
  unfold weight
  split_ifs <;> positivity

private lemma weight_zero (b : ℝ≥0∞) : weight b 0 = 1 := by
  simp [weight]

private lemma partition_pos {Ω : Type*} [Fintype Ω] (H : Ω → ℕ)
    (hZ : ∃ x, H x = 0) (b : ℝ≥0∞) : 0 < Z H b := by
  classical
  obtain ⟨x,hx⟩ := hZ
  have hs : weight b (H x) ≤ Z H b :=
    single_le_sum (fun y _ => weight_nonneg b (H y)) (mem_univ x)
  rw [hx,weight_zero] at hs
  linarith

private lemma weight_identity (a b : ℝ≥0∞) (hab : a < b) (h : ℕ) :
    weight b h ^ 2 = weight (2*b-a) h * weight a h := by
  have ha : a ≠ ⊤ := ne_top_of_lt hab
  by_cases hb : b = ⊤
  · subst b
    have hc : 2* (⊤ : ℝ≥0∞)-a = ⊤ := by
      rw [ENNReal.mul_top (by norm_num),ENNReal.top_sub ha]
    by_cases hh : h = 0 <;> simp [weight,hc,hh]
  · have h2 : (2 : ℝ≥0∞)*b ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hb
    have hle : a ≤ 2*b := hab.le.trans (by
      calc
        b = b+0 := by rw [add_zero]
        _ ≤ b+b := add_le_add le_rfl (show (0 : ℝ≥0∞) ≤ b from bot_le)
        _ = 2*b := (two_mul b).symm)
    have hc : 2*b-a ≠ ⊤ := ENNReal.sub_ne_top h2
    simp only [weight,if_neg ha,if_neg hb,if_neg hc,
      ENNReal.toReal_sub_of_le hle h2,ENNReal.toReal_mul,ENNReal.toReal_ofNat]
    rw [pow_two,← Real.exp_add,← Real.exp_add]
    congr 1
    ring

private lemma chi_identity {Ω : Type*} [Fintype Ω] (H : Ω → ℕ)
    (hZ : ∃ x, H x = 0) (a b : ℝ≥0∞) (hab : a < b) :
    chiSq (gibbs H b) (gibbs H a) = Z H (2*b-a)*Z H a/Z H b^2-1 := by
  classical
  have ha : a ≠ ⊤ := ne_top_of_lt hab
  have hZa : Z H a ≠ 0 := ne_of_gt (partition_pos H hZ a)
  have hZb : Z H b ≠ 0 := ne_of_gt (partition_pos H hZ b)
  have hpoint (x : Ω) : gibbs H a x * (gibbs H b x / gibbs H a x-1)^2 =
      (Z H a/Z H b^2)*weight (2*b-a) (H x) - 2*(weight b (H x)/Z H b) +
        weight a (H x)/Z H a := by
    have hw : weight a (H x) ≠ 0 := by
      simp only [weight,if_neg ha]
      exact ne_of_gt (Real.exp_pos _)
    dsimp only [gibbs]
    calc
      _ = weight b (H x)^2 * Z H a / (weight a (H x)*Z H b^2) -
          2*(weight b (H x)/Z H b) + weight a (H x)/Z H a := by
        field_simp
        <;> ring
      _ = _ := by
        rw [weight_identity a b hab]
        field_simp
        <;> ring
  unfold chiSq
  simp_rw [hpoint]
  simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,← sum_div]
  change (Z H a/Z H b^2)*Z H (2*b-a)-2*(Z H b/Z H b)+Z H a/Z H a = _
  rw [div_self hZa,div_self hZb]
  ring

theorem solution {Ω : Type*} [Fintype Ω] (H : Ω → ℕ) (hZ : ∃ x, H x = 0)
    (β : ℕ → ℝ≥0∞) (ℓ : ℕ) (B : ℝ) (hsched : IsChebyshevSchedule H β ℓ B) :
    ∀ i < ℓ, chiSq (gibbs H (β (i + 1))) (gibbs H (β i)) ≤ B - 1 := by
  intro i hi
  rw [chi_identity H hZ _ _ (hsched.1.2.1 i hi)]
  linarith [hsched.2 i hi]

#print axioms solution

