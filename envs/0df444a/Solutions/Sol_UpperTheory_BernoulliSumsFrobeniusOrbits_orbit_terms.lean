-- Prove2me | solution 1 for UpperTheory.BernoulliSumsFrobeniusOrbits.orbit_terms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:13:57.523191+00:00
-- url     : https://prove2.me/submissions/7c1de4cf-1069-44f8-96b8-eba687b1e35f

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLowBounds
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_orbitTerms
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_markedLow_bounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
private theorem ot_binUpper_le (G N : ℕ) (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1)
    (hN : 6 * Real.exp 1 * (G : ℝ) * δ ≤ N) :
    Formalism.G0.binUpper G δ N ≤ Real.exp (-(N : ℝ)) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    simp only [Nat.cast_zero, neg_zero, Real.exp_zero]
    unfold Formalism.G0.binUpper
    have hset : Icc 0 G = range (G + 1) := by
      ext j
      simp [Nat.lt_succ_iff]
    rw [hset]
    calc ∑ j ∈ range (G + 1), (G.choose j : ℝ) * δ ^ j * (1 - δ) ^ (G - j)
        = ∑ j ∈ range (G + 1), δ ^ j * (1 - δ) ^ (G - j) * (G.choose j : ℝ) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = (δ + (1 - δ)) ^ G := (add_pow δ (1 - δ) G).symm
      _ ≤ 1 := by simp
  · have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hepos : 0 < Real.exp 1 := Real.exp_pos 1
    unfold Formalism.G0.binUpper
    have hterm : ∀ j ∈ Icc N G, (G.choose j : ℝ) * δ ^ j * (1 - δ) ^ (G - j) ≤ (1 / 6 : ℝ) ^ j := by
      intro j hj
      have hjN : N ≤ j := (Finset.mem_Icc.mp hj).1
      have hjpos : (0 : ℝ) < j := by exact_mod_cast lt_of_lt_of_le hNpos hjN
      have hjne : (j : ℝ) ≠ 0 := hjpos.ne'
      have hc := Nat.choose_le_pow_div (α := ℝ) j G
      have hf := Real.pow_div_factorial_le_exp (j : ℝ) hjpos.le j
      have hfpos : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
      have h1d : (1 - δ) ^ (G - j) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      have hNj : (N : ℝ) ≤ j := by exact_mod_cast hjN
      have hq : Real.exp 1 * G * δ / j ≤ 1 / 6 := by
        rw [div_le_iff₀ hjpos]
        linarith
      have hq0 : 0 ≤ Real.exp 1 * G * δ / j := by positivity
      calc (G.choose j : ℝ) * δ ^ j * (1 - δ) ^ (G - j) ≤ (G.choose j : ℝ) * δ ^ j * 1 := by
            apply mul_le_mul_of_nonneg_left h1d
            positivity
        _ ≤ (G : ℝ) ^ j / j.factorial * δ ^ j := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_right hc (by positivity)
        _ = (G * δ / j) ^ j * ((j : ℝ) ^ j / j.factorial) := by
            rw [div_pow, mul_pow]
            field_simp
        _ ≤ (G * δ / j) ^ j * Real.exp j := mul_le_mul_of_nonneg_left hf (by positivity)
        _ = (Real.exp 1 * G * δ / j) ^ j := by
            rw [show Real.exp j = Real.exp 1 ^ j by rw [← Real.exp_nat_mul, mul_one], ← mul_pow]
            congr 1
            ring
        _ ≤ (1 / 6) ^ j := pow_le_pow_left₀ hq0 hq j
    calc ∑ j ∈ Icc N G, (G.choose j : ℝ) * δ ^ j * (1 - δ) ^ (G - j)
        ≤ ∑ j ∈ Icc N G, (1 / 6 : ℝ) ^ j := Finset.sum_le_sum hterm
      _ = ∑ j ∈ Ico N (G + 1), (1 / 6 : ℝ) ^ j := by rw [Finset.Ico_add_one_right_eq_Icc]
      _ ≤ (1 / 6 : ℝ) ^ N / (1 - 1 / 6) := geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
      _ ≤ Real.exp (-(N : ℝ)) := by
          have h3 : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
            rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (by norm_num) hepos]
            linarith
          have hexp : Real.exp (-(N : ℝ)) = Real.exp (-1) ^ N := by
            rw [← Real.exp_nat_mul]
            congr 1
            ring
          rw [hexp]
          have h6 : (1 / 6 : ℝ) ^ N = (1 / 3) ^ N * (1 / 2) ^ N := by
            rw [← mul_pow]
            norm_num
          have h2 : (1 / 2 : ℝ) ^ N ≤ 1 / 2 := by
            calc (1 / 2 : ℝ) ^ N ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hNpos
              _ = 1 / 2 := by norm_num
          have h3N : (1 / 3 : ℝ) ^ N ≤ Real.exp (-1) ^ N := pow_le_pow_left₀ (by norm_num) h3 N
          have h30 : 0 ≤ (1 / 3 : ℝ) ^ N := by positivity
          have hprod := mul_le_mul_of_nonneg_left h2 h30
          rw [h6, div_le_iff₀ (by norm_num)]
          linarith
private theorem ot_exists_log_le_rpow (C a : ℝ) (hC : 0 < C) (ha : 0 < a) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → C * (Real.log x + 1) ≤ x ^ a := by
  have h1 := (isLittleO_log_rpow_atTop ha).bound (c := 1 / (2 * C)) (by positivity)
  have h2 := (tendsto_rpow_atTop ha).eventually_ge_atTop (2 * C)
  have h3 := Filter.eventually_ge_atTop (1 : ℝ)
  obtain ⟨x₀, hx⟩ := Filter.eventually_atTop.1 (h1.and (h2.and h3))
  refine ⟨x₀, fun x hxx => ?_⟩
  obtain ⟨b1, b2, b3⟩ := hx x hxx
  rw [Real.norm_of_nonneg (Real.log_nonneg b3), Real.norm_of_nonneg (by positivity)] at b1
  have : C * Real.log x ≤ x ^ a / 2 := by
    calc C * Real.log x ≤ C * (1 / (2 * C) * x ^ a) := mul_le_mul_of_nonneg_left b1 hC.le
      _ = x ^ a / 2 := by field_simp
  linarith
end

set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
set_option maxHeartbeats 400000
namespace UpperTheory.BernoulliSumsFrobeniusOrbits
theorem _root_.solution :
    ∀ eps Co Lb : ℝ, 0 < eps → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ x ≥ x₀, ∀ n L₂ : ℕ, x ^ (eps / 4) ≤ (n : ℝ) → (n : ℝ) ≤ Co * x ^ hE eps →
      (L₂ : ℝ) ≤ Lb →
      (Formalism.MainNotions.G.orbitSmallMultiplicity (rE eps) (hE eps) x + 1) * ((6 * rE eps + 1) * Formalism.MainNotions.G.goodU (dE eps x)) ≤ n ∧
      (n : ℝ) * (L₂.choose (KE eps) : ℝ) * dE eps x ^ KE eps +
        n * (1 - markedLow (dE eps x) (rE eps) (Formalism.MainNotions.G.goodU (dE eps x))) ^ Formalism.MainNotions.G.orbitSmallMultiplicity (rE eps) (hE eps) x +
        n * binUpper (Formalism.MainNotions.G.goodG' (rE eps) (dE eps x) (hE eps) x) (dE eps x)
          (Formalism.MainNotions.G.orbitWindowCount (rE eps) (dE eps x) (hE eps) x - 1) ≤ Cb * x ^ (-2 : ℝ) := by
  intro eps Co Lb heps
  have hhv : hE eps = 2 + 8 * eps := rfl
  have hhpos : 0 < hE eps := by rw [hhv]; linarith
  have hKge : 8 * (hE eps + 2) / eps ≤ (KE eps : ℝ) := Nat.le_ceil _
  have hepsK : hE eps + 2 ≤ eps / 8 * (KE eps : ℝ) := by
    rw [div_le_iff₀ heps] at hKge
    linarith
  have hM0eq : ∀ x : ℝ, Formalism.MainNotions.G.orbitSmallMultiplicity (rE eps) (hE eps) x
      = ⌈(hE eps + 3) * Real.log x * (10 : ℝ) ^ (6 * rE eps + 1)⌉₊ := by
    intro x
    unfold Formalism.MainNotions.G.orbitSmallMultiplicity
    rw [zpow_neg, div_inv_eq_mul]
    norm_cast
  set K := KE eps with hK
  set h := hE eps with hh
  set r := rE eps with hr
  set P : ℝ := (10 : ℝ) ^ (6 * r + 1) with hP
  have hPpos : 0 < P := by positivity
  set A : ℝ := |Co| + 1 with hA
  set B : ℝ := (max Lb 1) ^ K with hB
  have hApos : 0 < A := by rw [hA]; positivity
  have hB1 : 1 ≤ B := one_le_pow₀ (le_max_right _ _)
  set C1 : ℝ := (h + 3) * P + 2 with hC1
  have hhP : 0 < (h + 3) * P := mul_pos (by linarith) hPpos
  have hC1pos : 0 < C1 := by rw [hC1]; linarith
  obtain ⟨y₀, hy₀⟩ := ot_exists_log_le_rpow (2 * (6 * (r : ℝ) + 1) * C1) (eps / 8)
    (mul_pos (by positivity) hC1pos) (by positivity)
  refine ⟨A * (B + 2), max (max y₀ 1) ((100 : ℝ) ^ (8 / eps)), mul_pos hApos (by linarith), ?_⟩
  intro x hx n L₂ hn1 hn2 hL
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)
  have hxy : y₀ ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
  have hx100 : (100 : ℝ) ^ (8 / eps) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  set δ := dE eps x with hδ
  have hδv : δ = x ^ (-(eps / 8)) := rfl
  have hδpos : 0 < δ := by rw [hδv]; exact Real.rpow_pos_of_pos hx0 _
  have hδinv : δ⁻¹ = x ^ (eps / 8) := by rw [hδv, Real.rpow_neg hx0.le, inv_inv]
  have hδ100 : δ ≤ 1 / 100 := by
    have h100 : (100 : ℝ) ≤ x ^ (eps / 8) := by
      calc (100 : ℝ) = ((100 : ℝ) ^ (8 / eps)) ^ (eps / 8) := by
            rw [← Real.rpow_mul (by norm_num), show (8 / eps * (eps / 8)) = (1 : ℝ) by field_simp,
              Real.rpow_one]
        _ ≤ x ^ (eps / 8) := Real.rpow_le_rpow (by positivity) hx100 (by positivity)
    have := inv_anti₀ (by norm_num) h100
    rw [← hδinv, inv_inv] at this
    rw [one_div]
    exact this
  have hδ1 : δ ≤ 1 := by linarith
  have hexpb : ∀ t : ℝ, (h + 3) * Real.log x ≤ t → Real.exp (-t) ≤ x ^ (-(h + 3)) := by
    intro t ht
    rw [Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hM0ge : (h + 3) * Real.log x * P ≤ (Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) := by
    rw [hM0eq]
    exact Nat.le_ceil _
  have hM0le : (Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) ≤ (h + 3) * Real.log x * P + 1 := by
    rw [hM0eq]
    exact (Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg (by linarith) hlogx) hPpos.le)).le
  constructor
  · have hu0 : (Formalism.MainNotions.G.goodU δ : ℝ) ≤ 2 * x ^ (eps / 8) := by
      have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 1 / δ by positivity)
      unfold Formalism.MainNotions.G.goodU
      have h1x : 1 ≤ x ^ (eps / 8) := Real.one_le_rpow hx1 (by positivity)
      rw [one_div, hδinv] at hc ⊢
      linarith
    have hsq : x ^ (eps / 8) * x ^ (eps / 8) = x ^ (eps / 4) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    have hMle : (Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) + 1 ≤ C1 * (Real.log x + 1) := by
      rw [hC1]
      nlinarith
    have hy := hy₀ x hxy
    have hxe : 0 ≤ x ^ (eps / 8) := Real.rpow_nonneg hx0.le _
    have key : ((Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) + 1) * ((6 * (r : ℝ) + 1) * (Formalism.MainNotions.G.goodU δ : ℝ)) ≤ n := by
      calc _ ≤ (C1 * (Real.log x + 1)) * ((6 * (r : ℝ) + 1) * (2 * x ^ (eps / 8))) := by
            apply mul_le_mul hMle (mul_le_mul_of_nonneg_left hu0 (by positivity)) (by positivity)
            exact mul_nonneg hC1pos.le (by linarith)
        _ = (2 * (6 * (r : ℝ) + 1) * C1 * (Real.log x + 1)) * x ^ (eps / 8) := by ring
        _ ≤ x ^ (eps / 8) * x ^ (eps / 8) := mul_le_mul_of_nonneg_right hy hxe
        _ = x ^ (eps / 4) := hsq
        _ ≤ n := hn1
    exact_mod_cast key
  · have hxh : 0 ≤ x ^ h := Real.rpow_nonneg hx0.le _
    have hnA : (n : ℝ) ≤ A * x ^ h :=
      le_trans hn2 (mul_le_mul_of_nonneg_right (by rw [hA]; linarith [le_abs_self Co]) hxh)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hd3 : x ^ h * x ^ (-(h + 3)) ≤ x ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hx0]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hd2 : x ^ h * x ^ (-(h + 2)) ≤ x ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hx0]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hT1 : (L₂.choose K : ℝ) * δ ^ K ≤ B * x ^ (-(h + 2)) := by
      have hLb : (L₂ : ℝ) ≤ max Lb 1 := le_trans hL (le_max_left _ _)
      have hc : (L₂.choose K : ℝ) ≤ (L₂ : ℝ) ^ K := by exact_mod_cast Nat.choose_le_pow L₂ K
      have hcB : (L₂.choose K : ℝ) ≤ B := le_trans hc (pow_le_pow_left₀ (Nat.cast_nonneg _) hLb K)
      have hδK : δ ^ K ≤ x ^ (-(h + 2)) := by
        rw [hδv, ← Real.rpow_mul_natCast hx0.le]
        exact Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith)
      exact mul_le_mul hcB hδK (pow_nonneg hδpos.le _) (by linarith)
    have hu := markedLow_bounds δ r hδpos hδ100
    have hT2 : (1 - markedLow δ r (Formalism.MainNotions.G.goodU δ)) ^ Formalism.MainNotions.G.orbitSmallMultiplicity r h x ≤ x ^ (-(h + 3)) := by
      have hq0 : (0 : ℝ) ≤ (1 / 10) ^ (6 * r + 1) := by positivity
      have hq1 : (1 / 10 : ℝ) ^ (6 * r + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hp1 : (1 / 10 : ℝ) ^ (6 * r + 1) * P = 1 := by
        rw [hP, ← mul_pow]
        norm_num
      have hprod := mul_le_mul_of_nonneg_right hM0ge hq0
      have hid : (h + 3) * Real.log x * P * (1 / 10 : ℝ) ^ (6 * r + 1) = (h + 3) * Real.log x := by
        rw [mul_assoc ((h + 3) * Real.log x), mul_comm P, hp1, mul_one]
      calc (1 - markedLow δ r (Formalism.MainNotions.G.goodU δ)) ^ Formalism.MainNotions.G.orbitSmallMultiplicity r h x
          ≤ (1 - (1 / 10 : ℝ) ^ (6 * r + 1)) ^ Formalism.MainNotions.G.orbitSmallMultiplicity r h x :=
            pow_le_pow_left₀ (by linarith [hu.2]) (by linarith [hu.1]) _
        _ ≤ Real.exp (-(1 / 10 : ℝ) ^ (6 * r + 1)) ^ Formalism.MainNotions.G.orbitSmallMultiplicity r h x :=
            pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-(1 / 10 : ℝ) ^ (6 * r + 1))]) _
        _ = Real.exp (-((Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) * (1 / 10 : ℝ) ^ (6 * r + 1))) := by
            rw [← Real.exp_nat_mul]
            congr 1
            ring
        _ ≤ x ^ (-(h + 3)) := hexpb _ (by linarith)
    have hN1 : Formalism.MainNotions.G.orbitWindowCount r δ h x - 1
        = ⌈max (6 * Real.exp 1 * (Formalism.MainNotions.G.goodG' r δ h x : ℝ) * δ) ((h + 3) * Real.logb 2 x)⌉₊ := by
      simp only [Formalism.MainNotions.G.orbitWindowCount, Nat.add_sub_cancel]
    have hT3 : binUpper (Formalism.MainNotions.G.goodG' r δ h x) δ (Formalism.MainNotions.G.orbitWindowCount r δ h x - 1) ≤ x ^ (-(h + 3)) := by
      rw [hN1]
      refine le_trans (ot_binUpper_le _ _ δ hδpos.le hδ1 (le_trans (le_max_left _ _) (Nat.le_ceil _))) ?_
      apply hexpb
      have hl2 : Real.log x ≤ Real.logb 2 x := by
        rw [Real.logb, le_div_iff₀ (Real.log_pos one_lt_two)]
        have := Real.log_two_lt_d9
        nlinarith
      calc (h + 3) * Real.log x ≤ (h + 3) * Real.logb 2 x := mul_le_mul_of_nonneg_left hl2 (by linarith)
        _ ≤ max (6 * Real.exp 1 * (Formalism.MainNotions.G.goodG' r δ h x : ℝ) * δ) ((h + 3) * Real.logb 2 x) :=
            le_max_right _ _
        _ ≤ _ := Nat.le_ceil _
    have hBx : 0 ≤ B * x ^ (-(h + 2)) := mul_nonneg (by linarith) (Real.rpow_nonneg hx0.le _)
    have hx3 : 0 ≤ x ^ (-(h + 3)) := Real.rpow_nonneg hx0.le _
    have e1 : (n : ℝ) * (L₂.choose K : ℝ) * δ ^ K ≤ A * B * x ^ (-2 : ℝ) := by
      calc (n : ℝ) * (L₂.choose K : ℝ) * δ ^ K = n * ((L₂.choose K : ℝ) * δ ^ K) := by ring
        _ ≤ n * (B * x ^ (-(h + 2))) := mul_le_mul_of_nonneg_left hT1 hn0
        _ ≤ (A * x ^ h) * (B * x ^ (-(h + 2))) := mul_le_mul_of_nonneg_right hnA hBx
        _ = A * B * (x ^ h * x ^ (-(h + 2))) := by ring
        _ ≤ A * B * x ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left hd2 (mul_nonneg hApos.le (by linarith))
    have e2 : (n : ℝ) * (1 - markedLow δ r (Formalism.MainNotions.G.goodU δ)) ^ Formalism.MainNotions.G.orbitSmallMultiplicity r h x ≤ A * x ^ (-2 : ℝ) := by
      calc _ ≤ (n : ℝ) * x ^ (-(h + 3)) := mul_le_mul_of_nonneg_left hT2 hn0
        _ ≤ (A * x ^ h) * x ^ (-(h + 3)) := mul_le_mul_of_nonneg_right hnA hx3
        _ = A * (x ^ h * x ^ (-(h + 3))) := by ring
        _ ≤ A * x ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left hd3 hApos.le
    have e3 : (n : ℝ) * binUpper (Formalism.MainNotions.G.goodG' r δ h x) δ (Formalism.MainNotions.G.orbitWindowCount r δ h x - 1) ≤ A * x ^ (-2 : ℝ) := by
      calc _ ≤ (n : ℝ) * x ^ (-(h + 3)) := mul_le_mul_of_nonneg_left hT3 hn0
        _ ≤ (A * x ^ h) * x ^ (-(h + 3)) := mul_le_mul_of_nonneg_right hnA hx3
        _ = A * (x ^ h * x ^ (-(h + 3))) := by ring
        _ ≤ A * x ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left hd3 hApos.le
    nlinarith
end UpperTheory.BernoulliSumsFrobeniusOrbits
