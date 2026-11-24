-- Prove2me | solution 1 for TaoFivePrimes.theorem51_child3_restricted_log_repair
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-23T05:27:00.915241+00:00
-- url     : https://prove2.me/submissions/43a8b9b9-cf10-4e57-bbab-664a4353034a

import Definitions.Def_TaoFivePrimes_TypeIEnvelopeInterfaces

-- Source module: Theorems.Thm_TaoFivePrimes_vaughan_identity_elementary
section
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
open ArithmeticFunction
namespace TaoFivePrimes
@[simp] theorem arithmeticRestrictLE_apply_loc (B n : ℕ)
    (f : ArithmeticFunction ℝ) :
    arithmeticRestrictLE B f n = if n ≤ B then f n else 0 := rfl
@[simp] theorem arithmeticRestrictGT_apply (B n : ℕ)
    (f : ArithmeticFunction ℝ) :
    arithmeticRestrictGT B f n = if B < n then f n else 0 := rfl
@[simp] theorem vaughanTruncatedHalfLog_apply (V n : ℕ) :
    vaughanTruncatedHalfLog V n =
      if V < n then (1 / 2 : ℝ) * Real.log n else 0 := rfl
theorem eta0_eq_zero_of_le_one_fourth {y : ℝ} (hy : y ≤ 1 / 4) :
    eta0 y = 0 := by
  unfold eta0
  by_cases hypos : 0 < y
  · rw [if_pos hypos]
    have h2ypos : 0 < 2 * y := by positivity
    have h2yle : 2 * y ≤ (1 / 2 : ℝ) := by linarith
    have hlogle : Real.log (2 * y) ≤ Real.log (1 / 2 : ℝ) :=
      Real.log_le_log h2ypos h2yle
    have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    have habs : Real.log 2 ≤ |Real.log (2 * y)| := by
      calc
        Real.log 2 ≤ -Real.log (2 * y) := by rw [hloghalf] at hlogle; linarith
        _ ≤ |Real.log (2 * y)| := neg_le_abs _
    rw [max_eq_left (sub_nonpos.mpr habs), mul_zero]
  · rw [if_neg hypos]
theorem eta0_eq_zero_of_one_le {y : ℝ} (hy : 1 ≤ y) : eta0 y = 0 := by
  unfold eta0
  rw [if_pos (by linarith)]
  have hlog : Real.log 2 ≤ Real.log (2 * y) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hcut : Real.log 2 - |Real.log (2 * y)| ≤ 0 :=
    sub_nonpos.mpr (hlog.trans (le_abs_self (Real.log (2 * y))))
  rw [max_eq_left hcut, mul_zero]
end TaoFivePrimes
end
-- Source module: Theorems.Thm_TaoFivePrimes_vaughan_typeII_bilinear_reindex
section
open scoped BigOperators ArithmeticFunction.Moebius
namespace TaoFivePrimes
private lemma weighted_range_eq_Ioc (N : ℕ) (A : ArithmeticFunction ℝ)
    (F : ℕ → ℂ) :
    arithmeticWeightedSum (Finset.range (N + 1)) A F =
      arithmeticWeightedSum (Finset.Ioc 0 N) A F := by
  unfold arithmeticWeightedSum
  have hrange : Finset.range (N + 1) = insert 0 (Finset.Ioc 0 N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [hrange]
  rw [Finset.sum_insert (by simp)]
  simp
theorem arithmeticWeightedSum_mul_eq_bilinear
    (N : ℕ) (A B : ArithmeticFunction ℝ) (F : ℕ → ℂ) :
    arithmeticWeightedSum (Finset.range (N + 1)) (A * B) F =
      ∑ p ∈ (Finset.Ioc 0 N).product (Finset.Ioc 0 N) with
          p.1 * p.2 ≤ N,
        ((A p.1 * B p.2 : ℝ) : ℂ) * F (p.1 * p.2) := by
  rw [weighted_range_eq_Ioc]
  unfold arithmeticWeightedSum
  simp only [ArithmeticFunction.mul_apply]
  trans ∑ n ∈ Finset.Ioc 0 N,
      ∑ p ∈ (Finset.Ioc 0 N).product (Finset.Ioc 0 N) with
        p.1 * p.2 = n,
        ((A p.1 * B p.2 : ℝ) : ℂ) * F n
  · apply Finset.sum_congr rfl
    intro n hn
    have hnb := Finset.mem_Ioc.mp hn
    rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le hnb.1.ne' hnb.2]
    push_cast
    rw [Finset.sum_mul]
    rfl
  · simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hprod : p.1 * p.2 ≤ N
    · rw [if_pos hprod]
      rw [Finset.sum_eq_single (p.1 * p.2)]
      · simp
      · intro n hn hne
        simp [hne, Ne.symm hne]
      · intro hnot
        exfalso
        have hpI := Finset.mem_product.mp hp
        have hppos : 0 < p.1 * p.2 :=
          Nat.mul_pos (Finset.mem_Ioc.mp hpI.1).1
            (Finset.mem_Ioc.mp hpI.2).1
        exact hnot (Finset.mem_Ioc.mpr ⟨hppos, hprod⟩)
    · rw [if_neg hprod]
      apply Finset.sum_eq_zero
      intro n hn
      rw [if_neg]
      intro heq
      apply hprod
      rw [heq]
      exact (Finset.mem_Ioc.mp hn).2
end TaoFivePrimes
end
-- Source module: Theorems.Thm_TaoFivePrimes_vaughan_typeI_reindex_support
section
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open ArithmeticFunction
namespace TaoFivePrimes
noncomputable def eta0VaughanTypeISmoothPairSum
    (x alpha U : ℝ) : ℂ :=
  ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).product (Finset.Ioc 0 ⌊x⌋₊) with
      p.1 * p.2 ≤ ⌊x⌋₊,
    (((arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) p.1) *
        ArithmeticFunction.log p.2 : ℝ) : ℂ) *
      eta0VaughanTest x alpha (p.1 * p.2)
noncomputable def eta0VaughanTypeICorrectionPairSum
    (x alpha U V : ℝ) : ℂ :=
  ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).product (Finset.Ioc 0 ⌊x⌋₊) with
      p.1 * p.2 ≤ ⌊x⌋₊,
    (((arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) p.1) *
        (arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) p.2 : ℝ) : ℂ) *
      eta0VaughanTest x alpha (p.1 * p.2)
noncomputable def eta0VaughanTypeITransferredPairSum
    (x alpha U V : ℝ) : ℂ :=
  ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).product (Finset.Ioc 0 ⌊x⌋₊) with
      p.1 * p.2 ≤ ⌊x⌋₊,
    (((arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ) p.1) *
        vaughanTruncatedHalfLog ⌊V⌋₊ p.2 : ℝ) : ℂ) *
      eta0VaughanTest x alpha (p.1 * p.2)
private theorem arithmeticWeightedSum_add_sub_split
    (s : Finset ℕ) (A B C : ArithmeticFunction ℝ) (F : ℕ → ℂ) :
    arithmeticWeightedSum s (A - B + C) F =
      arithmeticWeightedSum s A F - arithmeticWeightedSum s B F +
        arithmeticWeightedSum s C F := by
  unfold arithmeticWeightedSum
  calc
    (∑ n ∈ s, ((A - B + C) n : ℂ) * F n) =
        ∑ n ∈ s, (((A n : ℂ) * F n - (B n : ℂ) * F n) +
          (C n : ℂ) * F n) := by
            apply Finset.sum_congr rfl
            intro n hn
            change (((A n - B n + C n : ℝ) : ℂ) * F n) = _
            push_cast
            ring
    _ = (∑ n ∈ s, (A n : ℂ) * F n) -
          (∑ n ∈ s, (B n : ℂ) * F n) +
          ∑ n ∈ s, (C n : ℂ) * F n := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
theorem eta0VaughanTypeISum_eq_three_pair_sums
    (x alpha U V : ℝ) :
    eta0VaughanTypeISum x alpha U V =
      eta0VaughanTypeISmoothPairSum x alpha U -
        eta0VaughanTypeICorrectionPairSum x alpha U V +
          eta0VaughanTypeITransferredPairSum x alpha U V := by
  unfold eta0VaughanTypeISum vaughanTypeIPart
  let ML : ArithmeticFunction ℝ :=
    arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ)
  let LL : ArithmeticFunction ℝ :=
    arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt
  let Z : ArithmeticFunction ℝ := (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  let MG : ArithmeticFunction ℝ :=
    arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ)
  let H : ArithmeticFunction ℝ := vaughanTruncatedHalfLog ⌊V⌋₊
  have hassoc : ML * LL * Z = ML * (LL * Z) := mul_assoc _ _ _
  rw [hassoc]
  rw [arithmeticWeightedSum_add_sub_split]
  rw [arithmeticWeightedSum_mul_eq_bilinear,
    arithmeticWeightedSum_mul_eq_bilinear,
    arithmeticWeightedSum_mul_eq_bilinear]
  rfl
theorem eta0VaughanTest_eq_explicit_of_mem_open_odd_pairs_loc
    (x alpha : ℝ) (p : ℕ × ℕ) (hp : p ∈ eta0VaughanOpenOddPairs x) :
    eta0VaughanTest x alpha (p.1 * p.2) =
      expCircle (alpha * (p.1 * p.2)) *
        (eta0 (((p.1 * p.2 : ℕ) : ℝ) / x) : ℂ) := by
  simp only [eta0VaughanOpenOddPairs, Finset.mem_filter] at hp
  have hprododd : (p.1 * p.2).Coprime 2 :=
    Nat.coprime_mul_iff_left.mpr ⟨hp.2.2.1, hp.2.2.2.1⟩
  unfold eta0VaughanTest
  rw [if_pos hprododd]
  simp only [Nat.cast_mul]
end TaoFivePrimes
end
-- Source module: Theorems.Thm_TaoFivePrimes_vaughan_typeI_correction_coefficient_bridge
section
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open ArithmeticFunction
namespace TaoFivePrimes
@[simp]
theorem vaughanTypeICorrectionCoefficient_apply_loc (U V d : ℕ) :
    vaughanTypeICorrectionCoefficient U V d =
      ∑ p ∈ d.divisorsAntidiagonal,
        arithmeticRestrictLE U (μ : ArithmeticFunction ℝ) p.1 *
          arithmeticRestrictLE V ArithmeticFunction.vonMangoldt p.2 := by
  rfl
theorem vaughanTypeICorrectionCoefficient_eq_zero_of_mul_lt
    (U V d : ℕ) (hd : U * V < d) :
    vaughanTypeICorrectionCoefficient U V d = 0 := by
  rw [vaughanTypeICorrectionCoefficient_apply_loc]
  apply Finset.sum_eq_zero
  intro p hp
  simp only [arithmeticRestrictLE_apply_loc]
  by_cases ha : p.1 ≤ U
  · have hb : ¬p.2 ≤ V := by
      intro hb
      have hprod : p.1 * p.2 ≤ U * V := Nat.mul_le_mul ha hb
      have heq : p.1 * p.2 = d :=
        (Nat.mem_divisorsAntidiagonal.mp hp).1
      omega
    simp [ha, hb]
  · simp [ha]
theorem abs_vaughanTypeICorrectionCoefficient_le_log_loc
    (U V d : ℕ) (_hd : 0 < d) :
    |vaughanTypeICorrectionCoefficient U V d| ≤ Real.log (d : ℝ) := by
  rw [vaughanTypeICorrectionCoefficient_apply_loc]
  calc
    |∑ p ∈ d.divisorsAntidiagonal,
        arithmeticRestrictLE U (μ : ArithmeticFunction ℝ) p.1 *
          arithmeticRestrictLE V ArithmeticFunction.vonMangoldt p.2| ≤
        ∑ p ∈ d.divisorsAntidiagonal,
          |arithmeticRestrictLE U (μ : ArithmeticFunction ℝ) p.1 *
            arithmeticRestrictLE V ArithmeticFunction.vonMangoldt p.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ d.divisorsAntidiagonal,
          ArithmeticFunction.vonMangoldt p.2 := by
      apply Finset.sum_le_sum
      intro p hp
      simp only [arithmeticRestrictLE_apply_loc]
      by_cases ha : p.1 ≤ U
      · by_cases hb : p.2 ≤ V
        · rw [if_pos ha, if_pos hb, abs_mul,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          have hmuZ : |μ p.1| ≤ (1 : ℤ) :=
            ArithmeticFunction.abs_moebius_le_one
          have hmuR : |(((μ p.1 : ℤ) : ℝ))| ≤ (1 : ℝ) := by
            exact_mod_cast hmuZ
          exact (mul_le_mul_of_nonneg_right hmuR
            ArithmeticFunction.vonMangoldt_nonneg).trans_eq (one_mul _)
        · simp [ha, hb, ArithmeticFunction.vonMangoldt_nonneg]
      · simp [ha, ArithmeticFunction.vonMangoldt_nonneg]
    _ = ∑ b ∈ d.divisors, ArithmeticFunction.vonMangoldt b := by
      simpa only using
        (Nat.sum_divisorsAntidiagonal'
          (f := fun _ b => ArithmeticFunction.vonMangoldt b) (n := d))
    _ = Real.log (d : ℝ) := ArithmeticFunction.vonMangoldt_sum
noncomputable def eta0VaughanTypeICorrectionOuterPairSum
    (x alpha U V : ℝ) : ℂ :=
  ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).product (Finset.Ioc 0 ⌊x⌋₊) with
      p.1 * p.2 ≤ ⌊x⌋₊,
    (((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ p.1 *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) p.2 : ℝ) : ℂ) *
      eta0VaughanTest x alpha (p.1 * p.2))
theorem eta0VaughanTypeICorrectionPairSum_eq_outer
    (x alpha U V : ℝ) :
    eta0VaughanTypeICorrectionPairSum x alpha U V =
      eta0VaughanTypeICorrectionOuterPairSum x alpha U V := by
  unfold eta0VaughanTypeICorrectionPairSum
    eta0VaughanTypeICorrectionOuterPairSum
  let ML : ArithmeticFunction ℝ :=
    arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ)
  let LL : ArithmeticFunction ℝ :=
    arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt
  let Z : ArithmeticFunction ℝ :=
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  calc
    (∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).product (Finset.Ioc 0 ⌊x⌋₊) with
        p.1 * p.2 ≤ ⌊x⌋₊,
      (((ML p.1 * (LL * Z) p.2 : ℝ) : ℂ) *
        eta0VaughanTest x alpha (p.1 * p.2))) =
        arithmeticWeightedSum (Finset.range (⌊x⌋₊ + 1))
          (ML * (LL * Z)) (eta0VaughanTest x alpha) :=
      (arithmeticWeightedSum_mul_eq_bilinear ⌊x⌋₊ ML (LL * Z)
        (eta0VaughanTest x alpha)).symm
    _ = arithmeticWeightedSum (Finset.range (⌊x⌋₊ + 1))
          ((ML * LL) * Z) (eta0VaughanTest x alpha) := by
      rw [mul_assoc]
    _ = ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).product (Finset.Ioc 0 ⌊x⌋₊) with
        p.1 * p.2 ≤ ⌊x⌋₊,
      ((((ML * LL) p.1 * Z p.2 : ℝ) : ℂ) *
        eta0VaughanTest x alpha (p.1 * p.2)) :=
      arithmeticWeightedSum_mul_eq_bilinear ⌊x⌋₊ (ML * LL) Z
        (eta0VaughanTest x alpha)
end TaoFivePrimes
end
-- Source module: Theorems.Thm_TaoFivePrimes_vaughan_typeI_eta0_odd_grid_assembly
section
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
namespace TaoFivePrimes
namespace TypeIOddGridFirstVariation
theorem eta0_nonneg_grid_loc (t : ℝ) : 0 ≤ eta0 t := by
  unfold eta0
  split_ifs <;> positivity
theorem norm_moebius_real_complex_le_one_loc (d : ℕ) :
    ‖(((μ d : ℝ) : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hmuZ : |μ d| ≤ (1 : ℤ) := ArithmeticFunction.abs_moebius_le_one
  exact_mod_cast hmuZ
end TypeIOddGridFirstVariation
end TaoFivePrimes
end
end
-- Source module: Theorems.Thm_TaoFivePrimes_eta0_layer_cake
section
namespace TaoFivePrimes
theorem eta0_eq_four_mul_max_min_log {t : ℝ} (ht : 0 < t) :
    eta0 t =
      4 * max 0 (min (Real.log (4 * t)) (Real.log (1 / t))) := by
  unfold eta0
  rw [if_pos ht]
  by_cases hhalf : t ≤ 1 / 2
  · have h2tpos : 0 < 2 * t := by positivity
    have h2tle : 2 * t ≤ 1 := by linarith
    have habs : |Real.log (2 * t)| = -Real.log (2 * t) :=
      abs_of_nonpos (Real.log_nonpos h2tpos.le h2tle)
    have hsquare : 4 * t * t ≤ 1 := by
      have hprod : 0 ≤ (1 - 2 * t) * (1 + 2 * t) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hratio : 4 * t ≤ 1 / t := by
      apply (le_div_iff₀ ht).2
      nlinarith
    have hlogle : Real.log (4 * t) ≤ Real.log (1 / t) :=
      Real.strictMonoOn_log.monotoneOn
        (show 4 * t ∈ Set.Ioi 0 by simp only [Set.mem_Ioi]; positivity)
        (show 1 / t ∈ Set.Ioi 0 by simp only [Set.mem_Ioi]; positivity) hratio
    have hlog4 : Real.log 2 + Real.log (2 * t) = Real.log (4 * t) := by
      rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) h2tpos.ne']
      congr 1
      ring
    rw [habs, min_eq_left hlogle]
    congr 2
    linarith
  · have hhalf' : 1 / 2 < t := lt_of_not_ge hhalf
    have h2tpos : 0 < 2 * t := by positivity
    have h2tone : 1 ≤ 2 * t := by linarith
    have habs : |Real.log (2 * t)| = Real.log (2 * t) :=
      abs_of_nonneg (Real.log_nonneg h2tone)
    have hsquare : 1 ≤ 4 * t * t := by nlinarith
    have hratio : 1 / t ≤ 4 * t := by
      apply (div_le_iff₀ ht).2
      nlinarith
    have hlogle : Real.log (1 / t) ≤ Real.log (4 * t) :=
      Real.strictMonoOn_log.monotoneOn
        (show 1 / t ∈ Set.Ioi 0 by simp only [Set.mem_Ioi]; positivity)
        (show 4 * t ∈ Set.Ioi 0 by simp only [Set.mem_Ioi]; positivity) hratio
    have hlog2t : Real.log (2 * t) = Real.log 2 + Real.log t :=
      Real.log_mul (by norm_num) ht.ne'
    have hlogdiv : Real.log (1 / t) = -Real.log t := by
      rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) ht.ne', Real.log_one]
      ring
    rw [habs, min_eq_right hlogle]
    congr 2
    linarith
theorem eta0_normalized_layer_integral_eq_min_log {t : ℝ} (ht : 0 < t) :
    (∫ z : ℝ in max (1 / (2 * t)) 1..min (1 / t) 2, 1 / z) =
      min (Real.log (4 * t)) (Real.log (1 / t)) := by
  by_cases hhalf : t ≤ 1 / 2
  · have h2tpos : 0 < 2 * t := by positivity
    have h2tle : 2 * t ≤ 1 := by linarith
    have hlower : 1 ≤ 1 / (2 * t) := by
      apply (le_div_iff₀ h2tpos).2
      simpa using h2tle
    have hupper : 2 ≤ 1 / t := by
      apply (le_div_iff₀ ht).2
      linarith
    have hratio : 4 * t ≤ 1 / t := by
      apply (le_div_iff₀ ht).2
      have hprod : 0 ≤ (1 - 2 * t) * (1 + 2 * t) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hlogle : Real.log (4 * t) ≤ Real.log (1 / t) :=
      Real.strictMonoOn_log.monotoneOn
        (show 4 * t ∈ Set.Ioi 0 by simp only [Set.mem_Ioi]; positivity)
        (show 1 / t ∈ Set.Ioi 0 by simp only [Set.mem_Ioi]; positivity) hratio
    rw [max_eq_left hlower, min_eq_right hupper,
      integral_one_div_of_pos (by positivity) (by positivity),
      min_eq_left hlogle]
    congr 1
    field_simp
    <;> ring
  · have hhalf' : 1 / 2 < t := lt_of_not_ge hhalf
    have h2tpos : 0 < 2 * t := by positivity
    have h2tone : 1 ≤ 2 * t := by linarith
    have hlower : 1 / (2 * t) ≤ 1 := by
      apply (div_le_iff₀ h2tpos).2
      simpa using h2tone
    have hupper : 1 / t ≤ 2 := by
      apply (div_le_iff₀ ht).2
      linarith
    have hratio : 1 / t ≤ 4 * t := by
      apply (div_le_iff₀ ht).2
      nlinarith
    have hlogle : Real.log (1 / t) ≤ Real.log (4 * t) :=
      Real.strictMonoOn_log.monotoneOn
        (show 1 / t ∈ Set.Ioi 0 by simp only [Set.mem_Ioi]; positivity)
        (show 4 * t ∈ Set.Ioi 0 by simp only [Set.mem_Ioi]; positivity) hratio
    rw [max_eq_right hlower, min_eq_left hupper,
      integral_one_div_of_pos (by positivity) (by positivity),
      min_eq_right hlogle]
    congr 1
    ring
theorem eta0_eq_normalized_layer_integral {t : ℝ} (ht : 0 < t) :
    eta0 t = 4 * max 0
      (∫ z : ℝ in max (1 / (2 * t)) 1..min (1 / t) 2, 1 / z) := by
  rw [eta0_eq_four_mul_max_min_log ht,
    eta0_normalized_layer_integral_eq_min_log ht]
theorem eta0_layer_interval_integral_scale
    {x d w : ℝ} (hx : 0 < x) (hd : 0 < d) (hw : 0 < w) :
    (∫ z : ℝ in
        max (1 / (2 * (d * w / x))) 1..
          min (1 / (d * w / x)) 2, 1 / z) =
      ∫ W : ℝ in max (x / (2 * d)) w..min (x / d) (2 * w), 1 / W := by
  have ht : 0 < d * w / x := by positivity
  have hlow : max (x / (2 * d)) w =
      w * max (1 / (2 * (d * w / x))) 1 := by
    rw [mul_max_of_nonneg _ _ hw.le, mul_one]
    congr 1
    field_simp
    <;> ring
  have hupp : min (x / d) (2 * w) =
      w * min (1 / (d * w / x)) 2 := by
    rw [mul_min_of_nonneg _ _ hw.le]
    congr 1
    · field_simp
      <;> ring
    · ring
  have hnlow : 0 < max (1 / (2 * (d * w / x))) 1 :=
    lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hnupp : 0 < min (1 / (d * w / x)) 2 := by
    rw [lt_min_iff]
    constructor <;> positivity
  have halow : 0 < max (x / (2 * d)) w := by
    rw [hlow]
    positivity
  have haupp : 0 < min (x / d) (2 * w) := by
    rw [hupp]
    positivity
  rw [integral_one_div_of_pos hnlow hnupp,
    integral_one_div_of_pos halow haupp, hlow, hupp]
  congr 1
  field_simp
  <;> ring
theorem eta0_eq_layer_interval_integral
    {x d w : ℝ} (hx : 0 < x) (hd : 0 < d) (hw : 0 < w) :
    eta0 (d * w / x) =
      4 * max 0
        (∫ W : ℝ in max (x / (2 * d)) w..min (x / d) (2 * w), 1 / W) := by
  rw [eta0_eq_normalized_layer_integral (by positivity),
    eta0_layer_interval_integral_scale hx hd hw]
theorem eta0_eq_layer_setIntegral
    {x d w : ℝ} (hx : 0 < x) (hd : 0 < d) (hw : 0 < w)
    (hlower : x / 4 < d * w) (hupper : d * w < x) :
    eta0 (d * w / x) =
      4 * ∫ W : ℝ in Set.Icc (max (x / (2 * d)) w)
        (min (x / d) (2 * w)), 1 / W := by
  have hx0 : 0 ≤ x := hx.le
  have hxd : x / (2 * d) ≤ x / d := by
    exact div_le_div_of_nonneg_left hx0 hd (by linarith)
  have hx4 : x ≤ 4 * (d * w) := by linarith
  have hxdw : x / (2 * d) ≤ 2 * w := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * d)).2
    nlinarith
  have hwd : w ≤ x / d := by
    apply (le_div_iff₀ hd).2
    linarith
  have hw2 : w ≤ 2 * w := by linarith
  have hinter : max (x / (2 * d)) w ≤ min (x / d) (2 * w) :=
    max_le (le_min hxd hxdw) (le_min hwd hw2)
  have hleftpos : 0 < max (x / (2 * d)) w :=
    lt_of_lt_of_le hw (le_max_right _ _)
  have hintegral : 0 ≤
      ∫ W : ℝ in max (x / (2 * d)) w..min (x / d) (2 * w), 1 / W := by
    apply intervalIntegral.integral_nonneg hinter
    intro W hW
    have hWpos : 0 < W := hleftpos.trans_le hW.1
    positivity
  rw [eta0_eq_layer_interval_integral hx hd hw, max_eq_right hintegral,
    intervalIntegral.integral_of_le hinter,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
end TaoFivePrimes
end
-- Source module: Theorems.Thm_TaoFivePrimes_odd_interval_count
section
namespace TaoFivePrimes
theorem card_odd_finset_between_nat_le
    (s : Finset ℕ) (c b : ℕ)
    (hlo : ∀ n ∈ s, c ≤ n) (hhi : ∀ n ∈ s, n ≤ b)
    (hodd : ∀ n ∈ s, Odd n) :
    s.card ≤ (b - c) / 2 + 1 := by
  let f : ℕ → ℕ := fun n => (n - c) / 2
  have hcard : s.card ≤ (Finset.range ((b - c) / 2 + 1)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro n hn
      change f n ∈ Finset.range ((b - c) / 2 + 1)
      rw [Finset.mem_range]
      dsimp [f]
      have hsub : n - c ≤ b - c := Nat.sub_le_sub_right (hhi n hn) c
      have hdiv : (n - c) / 2 ≤ (b - c) / 2 := Nat.div_le_div_right hsub
      exact Nat.lt_succ_of_le hdiv
    · intro n hn m hm heq
      rcases hodd n hn with ⟨kn, hkn⟩
      rcases hodd m hm with ⟨km, hkm⟩
      have hcn := hlo n hn
      have hcm := hlo m hm
      dsimp [f] at heq
      omega
  simpa using hcard
theorem card_odd_finset_between_real_le
    (s : Finset ℕ) (A B : ℝ) (hA : 0 ≤ A) (hAB : A ≤ B)
    (hlo : ∀ n ∈ s, A ≤ (n : ℝ))
    (hhi : ∀ n ∈ s, (n : ℝ) ≤ B)
    (hodd : ∀ n ∈ s, n.Coprime 2) :
    (s.card : ℝ) ≤ (B - A) / 2 + 1 := by
  let c : ℕ := ⌈A⌉₊
  let b : ℕ := ⌊B⌋₊
  have hB : 0 ≤ B := hA.trans hAB
  have hc : ∀ n ∈ s, c ≤ n := by
    intro n hn
    exact Nat.ceil_le.mpr (hlo n hn)
  have hb : ∀ n ∈ s, n ≤ b := by
    intro n hn
    exact Nat.le_floor (hhi n hn)
  have hcardN : s.card ≤ (b - c) / 2 + 1 :=
    card_odd_finset_between_nat_le s c b hc hb fun n hn =>
      (Nat.coprime_two_right.mp (hodd n hn))
  have hcardR : (s.card : ℝ) ≤ (((b - c) / 2 + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcardN
  have hdiff : ((b - c : ℕ) : ℝ) ≤ B - A := by
    by_cases hcb : c ≤ b
    · rw [Nat.cast_sub hcb]
      have hfloor : (b : ℝ) ≤ B := Nat.floor_le hB
      have hceil : A ≤ (c : ℝ) := Nat.le_ceil A
      linarith
    · have hbc : b ≤ c := Nat.le_of_not_ge hcb
      rw [Nat.sub_eq_zero_of_le hbc, Nat.cast_zero]
      linarith
  calc
    (s.card : ℝ) ≤ (((b - c) / 2 + 1 : ℕ) : ℝ) := hcardR
    _ = ((((b - c) / 2 : ℕ) : ℝ) + 1) := by
      rw [Nat.cast_add, Nat.cast_one]
    _ ≤ (((b - c : ℕ) : ℝ) / 2 + 1) := by
      gcongr
      exact Nat.cast_div_le
    _ ≤ (B - A) / 2 + 1 := by linarith
end TaoFivePrimes
end
-- Source module: Theorems.Thm_TaoFivePrimes_vaughan_typeI_odd_grid_eta0_mass
section
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TaoFivePrimes
namespace TypeIOddGridFirstVariation
noncomputable def eta0FixedDLayer
    (x : ℝ) (d w : ℕ) (W : ℝ) : ℝ :=
  (Set.Icc
    (max (x / (2 * (d : ℝ))) (w : ℝ))
    (min (x / (d : ℝ)) (2 * (w : ℝ)))).indicator
      (fun W => 1 / W) W
theorem eta0FixedDLayer_integrable
    (x : ℝ) (d w : ℕ) (hw : 0 < w) :
    Integrable (eta0FixedDLayer x d w) := by
  have hwR : 0 < (w : ℝ) := by exact_mod_cast hw
  have hleft : 0 < max (x / (2 * (d : ℝ))) (w : ℝ) :=
    hwR.trans_le (le_max_right _ _)
  have hcont : ContinuousOn (fun W : ℝ => 1 / W)
      (Set.Icc
        (max (x / (2 * (d : ℝ))) (w : ℝ))
        (min (x / (d : ℝ)) (2 * (w : ℝ)))) := by
    intro W hW
    have hW : 0 < W := hleft.trans_le hW.1
    exact (continuousAt_const.div continuousAt_id hW.ne').continuousWithinAt
  exact (hcont.integrableOn_Icc.integrable_indicator measurableSet_Icc)
theorem eta0_sample_eq_fixedDLayer_integral
    (x : ℝ) (d w : ℕ) (hx : 0 < x) (hd : 0 < d) (hw : 0 < w)
    (hlower : x / 4 < ((d * w : ℕ) : ℝ))
    (hupper : ((d * w : ℕ) : ℝ) < x) :
    eta0 (((d * w : ℕ) : ℝ) / x) =
      4 * ∫ W : ℝ, eta0FixedDLayer x d w W := by
  have h := eta0_eq_layer_setIntegral
    (x := x) (d := (d : ℝ)) (w := (w : ℝ)) hx
    (by exact_mod_cast hd) (by exact_mod_cast hw)
    (by simpa only [Nat.cast_mul] using hlower)
    (by simpa only [Nat.cast_mul] using hupper)
  calc
    eta0 (((d * w : ℕ) : ℝ) / x) =
        4 * ∫ W : ℝ in Set.Icc
          (max (x / (2 * (d : ℝ))) (w : ℝ))
          (min (x / (d : ℝ)) (2 * (w : ℝ))), 1 / W := by
      simpa only [Nat.cast_mul] using h
    _ = 4 * ∫ W : ℝ, eta0FixedDLayer x d w W := by
      unfold eta0FixedDLayer
      rw [integral_indicator measurableSet_Icc]
noncomputable def eta0FixedDLayerFinset
    (x : ℝ) (d : ℕ) (s : Finset ℕ) (W : ℝ) : Finset ℕ :=
  s.filter fun w => W ∈ Set.Icc
    (max (x / (2 * (d : ℝ))) (w : ℝ))
    (min (x / (d : ℝ)) (2 * (w : ℝ)))
theorem sum_eta0FixedDLayer_eq_card_div
    (x : ℝ) (d : ℕ) (s : Finset ℕ) (W : ℝ) :
    (∑ w ∈ s, eta0FixedDLayer x d w W) =
      ((eta0FixedDLayerFinset x d s W).card : ℝ) * (1 / W) := by
  classical
  unfold eta0FixedDLayer eta0FixedDLayerFinset
  simp only [Set.indicator_apply]
  rw [← Finset.sum_filter]
  simp
theorem eta0FixedDLayerFinset_card_le
    (x : ℝ) (d : ℕ) (s : Finset ℕ) (W : ℝ)
    (hW0 : 0 ≤ W)
    (hodd : ∀ w ∈ s, w.Coprime 2) :
    ((eta0FixedDLayerFinset x d s W).card : ℝ) ≤ W / 4 + 1 := by
  have hcard := card_odd_finset_between_real_le
    (eta0FixedDLayerFinset x d s W) (W / 2) W
    (by positivity) (by linarith)
    (fun n hn => by
      have hm := (Finset.mem_filter.mp hn).2
      have hW2n : W ≤ 2 * (n : ℝ) := hm.2.trans (min_le_right _ _)
      linarith)
    (fun n hn => by
      have hm := (Finset.mem_filter.mp hn).2
      exact (le_max_right _ _).trans hm.1)
    (fun n hn => hodd n (Finset.mem_filter.mp hn).1)
  linarith
theorem eta0FixedDLayer_sum_le_indicator
    (x : ℝ) (d : ℕ) (s : Finset ℕ) (W : ℝ)
    (hx : 0 < x) (hd : 0 < d)
    (hodd : ∀ w ∈ s, w.Coprime 2) :
    (∑ w ∈ s, eta0FixedDLayer x d w W) ≤
      (Set.Icc (x / (2 * (d : ℝ))) (x / (d : ℝ))).indicator
        (fun W => (1 / 4 : ℝ) + 1 / W) W := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [sum_eta0FixedDLayer_eq_card_div]
  by_cases hband : W ∈ Set.Icc (x / (2 * (d : ℝ))) (x / (d : ℝ))
  · simp only [Set.indicator_of_mem hband]
    have hW : 0 < W := (div_pos hx (by positivity : 0 < 2 * (d : ℝ))).trans_le hband.1
    have hcard := eta0FixedDLayerFinset_card_le x d s W hW.le hodd
    have hmul := mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ (1 / W : ℝ))
    calc
      ((eta0FixedDLayerFinset x d s W).card : ℝ) * (1 / W)
          ≤ (W / 4 + 1) * (1 / W) := hmul
      _ = (1 / 4 : ℝ) + 1 / W := by field_simp
  · simp only [Set.indicator_apply, if_neg hband]
    have hzero : eta0FixedDLayerFinset x d s W = ∅ := by
      unfold eta0FixedDLayerFinset
      apply Finset.filter_eq_empty_iff.mpr
      intro w hw hm
      apply hband
      exact ⟨(le_max_left _ _).trans hm.1,
        hm.2.trans (min_le_left _ _)⟩
    simp [hzero]
theorem eta0FixedDLayer_band_integrable
    (x : ℝ) (d : ℕ) (hx : 0 < x) (hd : 0 < d) :
    Integrable
      ((Set.Icc (x / (2 * (d : ℝ))) (x / (d : ℝ))).indicator
        (fun W => (1 / 4 : ℝ) + 1 / W)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hleft : 0 < x / (2 * (d : ℝ)) := by positivity
  have hcont : ContinuousOn (fun W : ℝ => (1 / 4 : ℝ) + 1 / W)
      (Set.Icc (x / (2 * (d : ℝ))) (x / (d : ℝ))) := by
    intro W hW
    have hW : 0 < W := hleft.trans_le hW.1
    exact (continuousAt_const.add
      (continuousAt_const.div continuousAt_id hW.ne')).continuousWithinAt
  exact hcont.integrableOn_Icc.integrable_indicator measurableSet_Icc
theorem integral_eta0FixedDLayer_band
    (x : ℝ) (d : ℕ) (hx : 0 < x) (hd : 0 < d) :
    (∫ W : ℝ,
      (Set.Icc (x / (2 * (d : ℝ))) (x / (d : ℝ))).indicator
        (fun W => (1 / 4 : ℝ) + 1 / W) W) =
      x / (8 * (d : ℝ)) + Real.log 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hA : 0 < x / (2 * (d : ℝ)) := by positivity
  have hB : 0 < x / (d : ℝ) := by positivity
  have hAB : x / (2 * (d : ℝ)) ≤ x / (d : ℝ) :=
    div_le_div_of_nonneg_left hx.le hdR (by nlinarith)
  rw [integral_indicator measurableSet_Icc]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hAB]
  have hinv : IntervalIntegrable (fun W : ℝ => 1 / W) volume
      (x / (2 * (d : ℝ))) (x / (d : ℝ)) := by
    apply intervalIntegral.intervalIntegrable_one_div (f := fun W : ℝ => W)
    · intro W hW
      rw [Set.uIcc_of_le hAB] at hW
      exact (hA.trans_le hW.1).ne'
    · exact continuous_id.continuousOn
  rw [intervalIntegral.integral_add intervalIntegrable_const
    hinv]
  rw [intervalIntegral.integral_const, integral_one_div_of_pos hA hB]
  simp only [smul_eq_mul]
  have hratio :
      (x / (d : ℝ)) / (x / (2 * (d : ℝ))) = 2 := by
    field_simp
  rw [hratio]
  field_simp
  ring
theorem sum_eta0_samples_le_half_density
    (x : ℝ) (d : ℕ) (s : Finset ℕ)
    (hx : 0 < x) (hd : 0 < d)
    (hwpos : ∀ w ∈ s, 0 < w)
    (hodd : ∀ w ∈ s, w.Coprime 2)
    (hlower : ∀ w ∈ s, x / 4 < ((d * w : ℕ) : ℝ))
    (hupper : ∀ w ∈ s, ((d * w : ℕ) : ℝ) < x) :
    (∑ w ∈ s, eta0 (((d * w : ℕ) : ℝ) / x)) ≤
      x / (2 * (d : ℝ)) + 4 * Real.log 2 := by
  calc
    (∑ w ∈ s, eta0 (((d * w : ℕ) : ℝ) / x)) =
        ∑ w ∈ s, 4 * ∫ W : ℝ, eta0FixedDLayer x d w W := by
      apply Finset.sum_congr rfl
      intro w hw
      exact eta0_sample_eq_fixedDLayer_integral x d w hx hd
        (hwpos w hw) (hlower w hw) (hupper w hw)
    _ = 4 * (∑ w ∈ s, ∫ W : ℝ, eta0FixedDLayer x d w W) := by
      rw [Finset.mul_sum]
    _ = 4 * ∫ W : ℝ, ∑ w ∈ s, eta0FixedDLayer x d w W := by
      congr 1
      rw [integral_finsetSum]
      intro w hw
      exact eta0FixedDLayer_integrable x d w (hwpos w hw)
    _ ≤ 4 * ∫ W : ℝ,
        (Set.Icc (x / (2 * (d : ℝ))) (x / (d : ℝ))).indicator
          (fun W => (1 / 4 : ℝ) + 1 / W) W := by
      gcongr
      · exact integrable_finsetSum s fun w hw =>
          eta0FixedDLayer_integrable x d w (hwpos w hw)
      · exact eta0FixedDLayer_band_integrable x d hx hd
      · intro W
        exact eta0FixedDLayer_sum_le_indicator x d s W hx hd hodd
    _ = x / (2 * (d : ℝ)) + 4 * Real.log 2 := by
      rw [integral_eta0FixedDLayer_band x d hx hd]
      ring
end TypeIOddGridFirstVariation
end TaoFivePrimes
end
end
-- Source module: Theorems.Thm_TaoFivePrimes_vaughan_typeI_outer_d_assembly
section
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open ArithmeticFunction
set_option autoImplicit false
noncomputable section
namespace TaoFivePrimes
namespace TypeIOuterDAssembly
noncomputable def supportedFullCombinedCoefficient
    (U V : ℝ) (d w : ℕ) : ℝ :=
  (if d ≤ ⌊U⌋₊ then
      (μ d : ℝ) * Real.log (w : ℝ)
    else 0) -
    if d ≤ ⌊U⌋₊ * ⌊V⌋₊ then
      vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d
    else 0
noncomputable def totalFullSupportCoefficient
    (U V : ℝ) (d w : ℕ) : ℝ :=
  fullCombinedCoefficient U V d w +
    if ⌊V⌋₊ < w then transferredCoefficient U d w else 0
noncomputable def supportedOuterSlice
    (x alpha U V : ℝ) (d : ℕ) : ℂ :=
  (∑ w ∈ fullInnerSupport x d,
      ((supportedFullCombinedCoefficient U V d w : ℝ) : ℂ) *
        eta0VaughanTest x alpha (d * w)) +
    ∑ w ∈ transferredInnerSupport x V d,
      ((transferredCoefficient U d w : ℝ) : ℂ) *
        eta0VaughanTest x alpha (d * w)
theorem supportedFullCombinedCoefficient_eq
    (U V : ℝ) (d w : ℕ) :
    supportedFullCombinedCoefficient U V d w =
      fullCombinedCoefficient U V d w := by
  by_cases hd : d ≤ ⌊U⌋₊ * ⌊V⌋₊
  · simp [supportedFullCombinedCoefficient, fullCombinedCoefficient, hd]
  · have hzero :
        vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d = 0 :=
      vaughanTypeICorrectionCoefficient_eq_zero_of_mul_lt
        ⌊U⌋₊ ⌊V⌋₊ d (lt_of_not_ge hd)
    simp [supportedFullCombinedCoefficient, fullCombinedCoefficient, hd, hzero]
theorem supportedOuterSlice_eq
    (x alpha U V : ℝ) (d : ℕ) :
    supportedOuterSlice x alpha U V d = outerSlice x alpha U V d := by
  unfold supportedOuterSlice outerSlice
  simp_rw [supportedFullCombinedCoefficient_eq]
theorem outerSlice_eq_single_full_support_sum
    (x alpha U V : ℝ) (d : ℕ) :
    outerSlice x alpha U V d =
      ∑ w ∈ fullInnerSupport x d,
        ((totalFullSupportCoefficient U V d w : ℝ) : ℂ) *
          eta0VaughanTest x alpha (d * w) := by
  unfold outerSlice transferredInnerSupport totalFullSupportCoefficient
  rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hwV : ⌊V⌋₊ < w
  · simp [hwV]
    ring
  · simp [hwV]
theorem fullInnerSupport_mem_open_loc
    {x : ℝ} {d w : ℕ} (hw : w ∈ fullInnerSupport x d) :
    (d, w) ∈ eta0VaughanOpenOddPairs x := by
  exact (Finset.mem_filter.mp hw).2
theorem transferredInnerSupport_mem_full
    {x V : ℝ} {d w : ℕ} (hw : w ∈ transferredInnerSupport x V d) :
    w ∈ fullInnerSupport x d ∧ ⌊V⌋₊ < w := by
  exact Finset.mem_filter.mp hw
theorem eta0VaughanTest_eq_explicit_of_mem_fullInnerSupport_loc
    {x alpha : ℝ} {d w : ℕ} (hw : w ∈ fullInnerSupport x d) :
    eta0VaughanTest x alpha (d * w) =
      expCircle (alpha * (d * w)) *
        (eta0 (((d * w : ℕ) : ℝ) / x) : ℂ) := by
  exact eta0VaughanTest_eq_explicit_of_mem_open_odd_pairs_loc
    x alpha (d, w) (fullInnerSupport_mem_open_loc hw)
theorem fullInnerSupport_spec_loc
    {x : ℝ} {d w : ℕ} (hw : w ∈ fullInnerSupport x d) :
    0 < d ∧ 0 < w ∧ d * w ≤ ⌊x⌋₊ ∧
      d.Coprime 2 ∧ w.Coprime 2 ∧
      x / 4 < ((d * w : ℕ) : ℝ) ∧ ((d * w : ℕ) : ℝ) < x := by
  have hopen := fullInnerSupport_mem_open_loc hw
  simp only [eta0VaughanOpenOddPairs, Finset.mem_filter] at hopen
  rcases hopen with ⟨hbase, hprod, hdodd, hwodd, hlo, hhi⟩
  have hmem := Finset.mem_product.mp hbase
  exact ⟨(Finset.mem_Ioc.mp hmem.1).1,
    (Finset.mem_Ioc.mp hmem.2).1, hprod, hdodd, hwodd, hlo, hhi⟩
theorem pairSum_eq_openOddPairs
    (x alpha : ℝ) (A B : ArithmeticFunction ℝ) (hx : 0 < x) :
    (∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).product (Finset.Ioc 0 ⌊x⌋₊) with
        p.1 * p.2 ≤ ⌊x⌋₊,
      (((A p.1 * B p.2 : ℝ) : ℂ) *
        eta0VaughanTest x alpha (p.1 * p.2))) =
    ∑ p ∈ eta0VaughanOpenOddPairs x,
      (((A p.1 * B p.2 : ℝ) : ℂ) *
        eta0VaughanTest x alpha (p.1 * p.2)) := by
  unfold eta0VaughanOpenOddPairs
  symm
  apply Finset.sum_subset
  · intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  · intro p hp hpnot
    simp only [Finset.mem_filter] at hp
    have hnot : ¬(p.1 * p.2 ≤ ⌊x⌋₊ ∧
        p.1.Coprime 2 ∧ p.2.Coprime 2 ∧
        x / 4 < ((p.1 * p.2 : ℕ) : ℝ) ∧
        ((p.1 * p.2 : ℕ) : ℝ) < x) := by
      intro h
      exact hpnot (Finset.mem_filter.mpr ⟨hp.1, h⟩)
    by_cases hdodd : p.1.Coprime 2
    · by_cases hwodd : p.2.Coprime 2
      · by_cases hlower : x / 4 < ((p.1 * p.2 : ℕ) : ℝ)
        · by_cases hupper : ((p.1 * p.2 : ℕ) : ℝ) < x
          · exact False.elim (hnot ⟨hp.2, hdodd, hwodd, hlower, hupper⟩)
          · have hnx : x ≤ ((p.1 * p.2 : ℕ) : ℝ) := le_of_not_gt hupper
            have hratio : 1 ≤ ((p.1 * p.2 : ℕ) : ℝ) / x := by
              apply (le_div_iff₀ hx).2
              simpa using hnx
            have hprododd : (p.1 * p.2).Coprime 2 :=
              Nat.coprime_mul_iff_left.mpr ⟨hdodd, hwodd⟩
            have heta : eta0 (((p.1 * p.2 : ℕ) : ℝ) / x) = 0 :=
              eta0_eq_zero_of_one_le hratio
            unfold eta0VaughanTest
            rw [if_pos hprododd, heta]
            simp
        · have hnquarter : ((p.1 * p.2 : ℕ) : ℝ) ≤ x / 4 :=
            le_of_not_gt hlower
          have hratio : ((p.1 * p.2 : ℕ) : ℝ) / x ≤ 1 / 4 := by
            apply (div_le_iff₀ hx).2
            nlinarith
          have hprododd : (p.1 * p.2).Coprime 2 :=
            Nat.coprime_mul_iff_left.mpr ⟨hdodd, hwodd⟩
          have heta : eta0 (((p.1 * p.2 : ℕ) : ℝ) / x) = 0 :=
            eta0_eq_zero_of_le_one_fourth hratio
          unfold eta0VaughanTest
          rw [if_pos hprododd, heta]
          simp
      · have hprododd : ¬(p.1 * p.2).Coprime 2 := by
          intro h
          exact hwodd (Nat.coprime_mul_iff_left.mp h).2
        simp [eta0VaughanTest, hprododd]
    · have hprododd : ¬(p.1 * p.2).Coprime 2 := by
        intro h
        exact hdodd (Nat.coprime_mul_iff_left.mp h).1
      simp [eta0VaughanTest, hprododd]
theorem sum_openOddPairs_eq_nested
    (x : ℝ) (F : ℕ × ℕ → ℂ) :
    (∑ p ∈ eta0VaughanOpenOddPairs x, F p) =
      ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊,
        ∑ w ∈ fullInnerSupport x d, F (d, w) := by
  classical
  let I := Finset.Ioc 0 ⌊x⌋₊
  have hopen : eta0VaughanOpenOddPairs x =
      (I.product I).filter fun p => p ∈ eta0VaughanOpenOddPairs x := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · intro hp
      have hp' := hp
      simp only [eta0VaughanOpenOddPairs, Finset.mem_filter] at hp'
      exact ⟨hp'.1, hp⟩
    · exact fun hp => hp.2
  rw [hopen, Finset.sum_filter]
  calc
    (∑ p ∈ I.product I,
        if p ∈ eta0VaughanOpenOddPairs x then F p else 0) =
        ∑ d ∈ I, ∑ w ∈ I,
          if (d, w) ∈ eta0VaughanOpenOddPairs x then F (d, w) else 0 := by
      exact Finset.sum_product I I (fun p =>
        if p ∈ eta0VaughanOpenOddPairs x then F p else 0)
    _ = ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊,
        ∑ w ∈ fullInnerSupport x d, F (d, w) := by
      dsimp only [I]
      apply Finset.sum_congr rfl
      intro d hd
      unfold fullInnerSupport
      rw [Finset.sum_filter]
theorem pairSum_eq_nested_fullInnerSupport
    (x alpha : ℝ) (A B : ArithmeticFunction ℝ) (hx : 0 < x) :
    (∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).product (Finset.Ioc 0 ⌊x⌋₊) with
        p.1 * p.2 ≤ ⌊x⌋₊,
      (((A p.1 * B p.2 : ℝ) : ℂ) *
        eta0VaughanTest x alpha (p.1 * p.2))) =
      ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊,
        ∑ w ∈ fullInnerSupport x d,
          (((A d * B w : ℝ) : ℂ) *
            eta0VaughanTest x alpha (d * w)) := by
  rw [pairSum_eq_openOddPairs x alpha A B hx]
  exact sum_openOddPairs_eq_nested x (fun p =>
    (((A p.1 * B p.2 : ℝ) : ℂ) *
      eta0VaughanTest x alpha (p.1 * p.2)))
theorem eta0VaughanTypeISmoothPairSum_eq_nested_full
    (x alpha U : ℝ) (hx : 0 < x) :
    eta0VaughanTypeISmoothPairSum x alpha U =
      ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊,
        ∑ w ∈ fullInnerSupport x d,
          (((if d ≤ ⌊U⌋₊ then
              (μ d : ℝ) * Real.log (w : ℝ)
            else 0 : ℝ) : ℂ) *
            eta0VaughanTest x alpha (d * w)) := by
  unfold eta0VaughanTypeISmoothPairSum
  rw [pairSum_eq_nested_fullInnerSupport x alpha
    (arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ))
    ArithmeticFunction.log hx]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro w hw
  simp only [arithmeticRestrictLE_apply_loc]
  by_cases hdU : d ≤ ⌊U⌋₊
  · simp [hdU]
  · simp [hdU]
theorem eta0VaughanTypeICorrectionPairSum_eq_nested_full
    (x alpha U V : ℝ) (hx : 0 < x) :
    eta0VaughanTypeICorrectionPairSum x alpha U V =
      ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊,
        ∑ w ∈ fullInnerSupport x d,
          ((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ) *
            eta0VaughanTest x alpha (d * w) := by
  rw [eta0VaughanTypeICorrectionPairSum_eq_outer]
  unfold eta0VaughanTypeICorrectionOuterPairSum
  rw [pairSum_eq_nested_fullInnerSupport x alpha
    (vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊)
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ) hx]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro w hw
  have hwpos : 0 < w := (fullInnerSupport_spec_loc hw).2.1
  have hw0 : w ≠ 0 := hwpos.ne'
  simp [ArithmeticFunction.zeta_apply_ne hw0]
theorem eta0VaughanTypeITransferredPairSum_eq_nested_cutoff
    (x alpha U V : ℝ) (hx : 0 < x) :
    eta0VaughanTypeITransferredPairSum x alpha U V =
      ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊,
        ∑ w ∈ transferredInnerSupport x V d,
          (((if ⌊U⌋₊ < d then
              (μ d : ℝ) * ((1 / 2 : ℝ) * Real.log (w : ℝ))
            else 0 : ℝ) : ℂ) *
            eta0VaughanTest x alpha (d * w)) := by
  unfold eta0VaughanTypeITransferredPairSum
  rw [pairSum_eq_nested_fullInnerSupport x alpha
    (arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ))
    (vaughanTruncatedHalfLog ⌊V⌋₊) hx]
  apply Finset.sum_congr rfl
  intro d hd
  unfold transferredInnerSupport
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hdU : ⌊U⌋₊ < d
  · by_cases hwV : ⌊V⌋₊ < w
    · simp [arithmeticRestrictGT_apply, vaughanTruncatedHalfLog_apply,
        hdU, hwV]
    · simp [arithmeticRestrictGT_apply, vaughanTruncatedHalfLog_apply,
        hdU, hwV]
  · simp [arithmeticRestrictGT_apply, vaughanTruncatedHalfLog_apply, hdU]
theorem eta0VaughanTypeISum_eq_sum_outerSlice_full_range
    (x alpha U V : ℝ) (hx : 0 < x) :
    eta0VaughanTypeISum x alpha U V =
      ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, outerSlice x alpha U V d := by
  have hfull :
      (∑ d ∈ Finset.Ioc 0 ⌊x⌋₊,
          ∑ w ∈ fullInnerSupport x d,
            (((if d ≤ ⌊U⌋₊ then
                (μ d : ℝ) * Real.log (w : ℝ)
              else 0 : ℝ) : ℂ) *
              eta0VaughanTest x alpha (d * w))) -
        (∑ d ∈ Finset.Ioc 0 ⌊x⌋₊,
          ∑ w ∈ fullInnerSupport x d,
            ((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ) *
              eta0VaughanTest x alpha (d * w)) =
        ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊,
          ∑ w ∈ fullInnerSupport x d,
            ((fullCombinedCoefficient U V d w : ℝ) : ℂ) *
              eta0VaughanTest x alpha (d * w) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    unfold fullCombinedCoefficient
    push_cast
    ring
  rw [eta0VaughanTypeISum_eq_three_pair_sums,
    eta0VaughanTypeISmoothPairSum_eq_nested_full x alpha U hx,
    eta0VaughanTypeICorrectionPairSum_eq_nested_full x alpha U V hx,
    eta0VaughanTypeITransferredPairSum_eq_nested_cutoff x alpha U V hx,
    hfull]
  unfold outerSlice transferredCoefficient
  rw [Finset.sum_add_distrib]
theorem floor_mul_factors_le_floor_mul
    (U V : ℝ) (hU0 : 0 ≤ U) (hV0 : 0 ≤ V) :
    ⌊U⌋₊ * ⌊V⌋₊ ≤ ⌊U * V⌋₊ := by
  apply Nat.le_floor
  show (((⌊U⌋₊ * ⌊V⌋₊ : ℕ) : ℝ)) ≤ U * V
  rw [Nat.cast_mul]
  exact mul_le_mul (Nat.floor_le hU0) (Nat.floor_le hV0)
    (Nat.cast_nonneg _) hU0
theorem floor_left_le_floor_mul
    (U V : ℝ) (hU0 : 0 ≤ U) (hV1 : 1 ≤ V) :
    ⌊U⌋₊ ≤ ⌊U * V⌋₊ := by
  apply Nat.floor_mono
  have h := mul_le_mul_of_nonneg_left hV1 hU0
  simpa only [mul_one] using h
theorem outerSlice_eq_zero_of_floor_mul_lt
    (x alpha U V : ℝ) (hU0 : 0 ≤ U) (hV1 : 1 ≤ V)
    (hUV2 : x ≤ U * V ^ 2) (d : ℕ) (hd : ⌊U * V⌋₊ < d) :
    outerSlice x alpha U V d = 0 := by
  have hV0 : 0 ≤ V := le_trans (by norm_num) hV1
  have hUV0 : 0 ≤ U * V := mul_nonneg hU0 hV0
  have hfloorU : ⌊U⌋₊ ≤ ⌊U * V⌋₊ :=
    floor_left_le_floor_mul U V hU0 hV1
  have hdU : ¬d ≤ ⌊U⌋₊ := by omega
  have hfloorProd : ⌊U⌋₊ * ⌊V⌋₊ ≤ ⌊U * V⌋₊ :=
    floor_mul_factors_le_floor_mul U V hU0 hV0
  have hfzero :
      vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d = 0 := by
    apply vaughanTypeICorrectionCoefficient_eq_zero_of_mul_lt
    omega
  have hcoeff : ∀ w : ℕ, fullCombinedCoefficient U V d w = 0 := by
    intro w
    simp [fullCombinedCoefficient, hdU, hfzero]
  have htransEmpty : transferredInnerSupport x V d = ∅ := by
    ext w
    constructor
    · intro hw
      exfalso
      have hwparts := transferredInnerSupport_mem_full hw
      have hs := fullInnerSupport_spec_loc hwparts.1
      have hVw : V < (w : ℝ) :=
        (Nat.floor_lt hV0).mp hwparts.2
      have hUVd : U * V < (d : ℝ) :=
        (Nat.floor_lt hUV0).mp hd
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hs.1
      have hprodgt : U * V ^ 2 < (d : ℝ) * (w : ℝ) := by
        calc
          U * V ^ 2 = (U * V) * V := by ring
          _ < (d : ℝ) * V := mul_lt_mul_of_pos_right hUVd (lt_of_lt_of_le zero_lt_one hV1)
          _ < (d : ℝ) * (w : ℝ) := mul_lt_mul_of_pos_left hVw hdpos
      have hprodlt : (d : ℝ) * (w : ℝ) < U * V ^ 2 := by
        have hactive : (((d * w : ℕ) : ℝ)) < x := hs.2.2.2.2.2.2
        rw [Nat.cast_mul] at hactive
        exact hactive.trans_le hUV2
      exact (not_lt_of_ge hprodgt.le) hprodlt
    · intro hw
      simp at hw
  unfold outerSlice
  rw [htransEmpty]
  simp [hcoeff]
theorem eta0VaughanTypeISum_eq_supported_outer_assembly
    (x alpha U V : ℝ) (hx : 0 < x) (hU0 : 0 ≤ U) (hV1 : 1 ≤ V)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    eta0VaughanTypeISum x alpha U V =
      ∑ d ∈ Finset.Ioc 0 ⌊U * V⌋₊,
        supportedOuterSlice x alpha U V d := by
  rw [eta0VaughanTypeISum_eq_sum_outerSlice_full_range x alpha U V hx]
  have hUVx : U * V ≤ x := by
    exact hUV.trans (by linarith [hx])
  have hfloor : ⌊U * V⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono hUVx
  have hsubset : Finset.Ioc 0 ⌊U * V⌋₊ ⊆ Finset.Ioc 0 ⌊x⌋₊ := by
    intro d hd
    simp only [Finset.mem_Ioc] at hd ⊢
    exact ⟨hd.1, hd.2.trans hfloor⟩
  have htruncate :
      (∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, outerSlice x alpha U V d) =
        ∑ d ∈ Finset.Ioc 0 ⌊U * V⌋₊, outerSlice x alpha U V d := by
    symm
    apply Finset.sum_subset hsubset
    intro d hdBig hdSmall
    have hdgt : ⌊U * V⌋₊ < d := by
      simp only [Finset.mem_Ioc] at hdBig hdSmall
      omega
    exact outerSlice_eq_zero_of_floor_mul_lt
      x alpha U V hU0 hV1 hUV2 d hdgt
  rw [htruncate]
  apply Finset.sum_congr rfl
  intro d hd
  rw [supportedOuterSlice_eq]
end TypeIOuterDAssembly
end TaoFivePrimes
end
end

section
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace TaoFivePrimes.TypeIOrdinaryFinalAssembly
open TaoFivePrimes.TypeIOuterDAssembly
theorem outerSlice_eq_zero_of_not_coprime_two
    (x alpha U V : ℝ) (d : ℕ) (hdodd : ¬d.Coprime 2) :
    outerSlice x alpha U V d = 0 := by
  have hfull : fullInnerSupport x d = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hne
    obtain ⟨w, hw⟩ := hne
    exact hdodd (fullInnerSupport_spec_loc hw).2.2.2.1
  have htrans : transferredInnerSupport x V d = ∅ := by
    unfold transferredInnerSupport
    rw [hfull]
    simp
  simp [outerSlice, hfull, htrans]
end TaoFivePrimes.TypeIOrdinaryFinalAssembly
end
end

section
open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction Finset
set_option autoImplicit false

namespace TaoFivePrimes

open TypeIOuterDAssembly

private theorem norm_moebius_loc (d : ℕ) :
    ‖(((ArithmeticFunction.moebius d : ℝ) : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs]
  exact_mod_cast abs_moebius_le_one (n := d)

private noncomputable def repAlign (S1 S0 : ℂ) : ℂ :=
  if S1 = 0 ∨ S0 = 0 then 1 else (S1 / (‖S1‖ : ℂ)) * ((‖S0‖ : ℂ) / S0)

private theorem norm_repAlign (S1 S0 : ℂ) : ‖repAlign S1 S0‖ = 1 := by
  unfold repAlign
  split_ifs with h
  · simp
  · have h1 : S1 ≠ 0 := fun hc => h (Or.inl hc)
    have h0 : S0 ≠ 0 := fun hc => h (Or.inr hc)
    rw [norm_mul, norm_div, norm_div]
    simp [Complex.norm_real, h1, h0]

private theorem repAlign_spec (S1 S0 : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    ‖S1‖ + t * ‖S0‖ = ‖S1 + repAlign S1 S0 * (t : ℂ) * S0‖ := by
  unfold repAlign
  by_cases h1 : S1 = 0
  · rw [if_pos (Or.inl h1), h1]
    simp [abs_of_nonneg ht]
  · by_cases h0 : S0 = 0
    · rw [if_pos (Or.inr h0), h0]
      simp
    · rw [if_neg (by tauto)]
      have hn1 : (‖S1‖ : ℂ) ≠ 0 := by simpa using h1
      have hn0 : (‖S0‖ : ℂ) ≠ 0 := by simpa using h0
      have hkey : S1 / (‖S1‖ : ℂ) * ((‖S0‖ : ℂ) / S0) * (t : ℂ) * S0
          = S1 * ((t * ‖S0‖ / ‖S1‖ : ℝ) : ℂ) := by
        field_simp
        push_cast
        field_simp
      rw [hkey]
      have hfac : S1 + S1 * ((t * ‖S0‖ / ‖S1‖ : ℝ) : ℂ)
          = S1 * (((1 + t * ‖S0‖ / ‖S1‖ : ℝ)) : ℂ) := by push_cast; ring
      rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 + t * ‖S0‖ / ‖S1‖)]
      have : ‖S1‖ ≠ 0 := by simpa using h1
      field_simp

private noncomputable def slabS1 (x alpha : ℝ) (d : ℕ) : ℂ :=
  ∑ w ∈ fullInnerSupport x d,
    ((Real.log (w : ℝ) : ℂ) * eta0VaughanTest x alpha (d * w))

private noncomputable def slabS0 (x alpha : ℝ) (d : ℕ) : ℂ :=
  ∑ w ∈ fullInnerSupport x d, eta0VaughanTest x alpha (d * w)

private noncomputable def slabK (x alpha V : ℝ) (d : ℕ) : ℂ :=
  ∑ w ∈ transferredInnerSupport x V d,
    ((Real.log (w : ℝ) : ℂ) * eta0VaughanTest x alpha (d * w))

private theorem outerSlice_eq_low (x alpha U V : ℝ) (d : ℕ) (hdU : d ≤ ⌊U⌋₊) :
    outerSlice x alpha U V d =
      (((ArithmeticFunction.moebius d : ℝ) : ℂ) * slabS1 x alpha d)
        - (((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ) * slabS0 x alpha d) := by
  have hnot : ¬ ⌊U⌋₊ < d := not_lt.mpr hdU
  have hterm : ∀ w : ℕ,
      (((if d ≤ ⌊U⌋₊ then (ArithmeticFunction.moebius d : ℝ) * Real.log (w : ℝ) else 0)
            - vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ)
          * eta0VaughanTest x alpha (d * w)
        = (((ArithmeticFunction.moebius d : ℝ) : ℂ) *
              ((Real.log (w : ℝ) : ℂ) * eta0VaughanTest x alpha (d * w)))
          - (((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ)
              * eta0VaughanTest x alpha (d * w)) := by
    intro w
    rw [if_pos hdU]
    push_cast
    ring
  have hzero : (∑ w ∈ transferredInnerSupport x V d,
      ((transferredCoefficient U d w : ℝ) : ℂ) * eta0VaughanTest x alpha (d * w)) = 0 := by
    refine Finset.sum_eq_zero (fun w _ => ?_)
    unfold transferredCoefficient
    rw [if_neg hnot]
    simp
  unfold outerSlice fullCombinedCoefficient
  rw [hzero, add_zero]
  rw [Finset.sum_congr rfl (fun w _ => hterm w)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  unfold slabS1 slabS0
  rfl

private theorem outerSlice_eq_high (x alpha U V : ℝ) (d : ℕ) (hdlt : ⌊U⌋₊ < d) :
    outerSlice x alpha U V d =
      - (((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ) * slabS0 x alpha d)
        + ((((ArithmeticFunction.moebius d : ℝ) : ℂ) * (1 / 2 : ℂ)) * slabK x alpha V d) := by
  have hdU : ¬ d ≤ ⌊U⌋₊ := not_le.mpr hdlt
  have htermF : ∀ w : ℕ,
      (((0 : ℝ) - vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ)
          * eta0VaughanTest x alpha (d * w)
        = -(((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ)
              * eta0VaughanTest x alpha (d * w)) := by
    intro w
    push_cast
    ring
  have htermT : ∀ w : ℕ,
      ((transferredCoefficient U d w : ℝ) : ℂ) * eta0VaughanTest x alpha (d * w)
        = ((((ArithmeticFunction.moebius d : ℝ) : ℂ) * (1 / 2 : ℂ))
              * ((Real.log (w : ℝ) : ℂ) * eta0VaughanTest x alpha (d * w))) := by
    intro w
    unfold transferredCoefficient
    rw [if_pos hdlt]
    push_cast
    ring
  unfold outerSlice fullCombinedCoefficient
  simp only [hdU, if_false]
  rw [Finset.sum_congr rfl (fun w _ => htermF w)]
  rw [Finset.sum_congr rfl (fun w _ => htermT w)]
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  rw [← Finset.mul_sum]
  unfold slabS0 slabK
  rfl

private theorem norm_outerSlice_le_branch_low (x alpha U V : ℝ) (d : ℕ) (hd1 : 1 ≤ d)
    (hdU : d ≤ ⌊U⌋₊) :
    ‖outerSlice x alpha U V d‖ ≤
      ‖slabS1 x alpha d + repAlign (slabS1 x alpha d) (slabS0 x alpha d)
        * (Real.log d : ℂ) * slabS0 x alpha d‖ := by
  have hlog : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd1)
  have hmu := norm_moebius_loc d
  have hf : |(vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ)| ≤ Real.log (d : ℝ) :=
    abs_vaughanTypeICorrectionCoefficient_le_log_loc ⌊U⌋₊ ⌊V⌋₊ d (by exact_mod_cast hd1)
  rw [outerSlice_eq_low x alpha U V d hdU]
  calc ‖(((ArithmeticFunction.moebius d : ℝ) : ℂ) * slabS1 x alpha d)
        - (((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ) * slabS0 x alpha d)‖
      ≤ ‖(((ArithmeticFunction.moebius d : ℝ) : ℂ) * slabS1 x alpha d)‖
        + ‖(((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ)
            * slabS0 x alpha d)‖ := norm_sub_le _ _
    _ = ‖(((ArithmeticFunction.moebius d : ℝ) : ℂ))‖ * ‖slabS1 x alpha d‖
        + |(vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ)| * ‖slabS0 x alpha d‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 1 * ‖slabS1 x alpha d‖ + Real.log d * ‖slabS0 x alpha d‖ := by
        have h1 := norm_nonneg (slabS1 x alpha d)
        have h2 := norm_nonneg (slabS0 x alpha d)
        exact add_le_add (mul_le_mul_of_nonneg_right hmu h1)
          (mul_le_mul_of_nonneg_right hf h2)
    _ = ‖slabS1 x alpha d‖ + Real.log d * ‖slabS0 x alpha d‖ := by ring
    _ = ‖slabS1 x alpha d + repAlign (slabS1 x alpha d) (slabS0 x alpha d)
          * (Real.log d : ℂ) * slabS0 x alpha d‖ :=
        repAlign_spec (slabS1 x alpha d) (slabS0 x alpha d) (Real.log d) hlog

private theorem norm_outerSlice_le_branch_high (x alpha U V : ℝ) (d : ℕ) (hd1 : 1 ≤ d)
    (hdU : ¬ d ≤ ⌊U⌋₊) :
    ‖outerSlice x alpha U V d‖ ≤
      ‖slabK x alpha V d + repAlign (slabK x alpha V d) (slabS0 x alpha d)
        * (Real.log d : ℂ) * slabS0 x alpha d‖ := by
  have hlog : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd1)
  have hdlt : ⌊U⌋₊ < d := Nat.lt_of_not_le hdU
  have hmu := norm_moebius_loc d
  have hf : |(vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ)| ≤ Real.log (d : ℝ) :=
    abs_vaughanTypeICorrectionCoefficient_le_log_loc ⌊U⌋₊ ⌊V⌋₊ d (by exact_mod_cast hd1)
  rw [outerSlice_eq_high x alpha U V d hdlt]
  calc ‖- (((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ) * slabS0 x alpha d)
        + ((((ArithmeticFunction.moebius d : ℝ) : ℂ) * (1 / 2 : ℂ)) * slabK x alpha V d)‖
      ≤ ‖(((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ) * slabS0 x alpha d)‖
        + ‖((((ArithmeticFunction.moebius d : ℝ) : ℂ) * (1 / 2 : ℂ))
            * slabK x alpha V d)‖ := by
        simpa only [norm_neg] using norm_add_le
          (-(((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ) * slabS0 x alpha d))
          ((((ArithmeticFunction.moebius d : ℝ) : ℂ) * (1 / 2 : ℂ)) * slabK x alpha V d)
    _ = |(vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ)| * ‖slabS0 x alpha d‖
        + ‖(((ArithmeticFunction.moebius d : ℝ) : ℂ))‖ * (1 / 2 : ℝ) * ‖slabK x alpha V d‖ := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_real, Real.norm_eq_abs]
        norm_num
    _ ≤ Real.log d * ‖slabS0 x alpha d‖ + 1 * (1 / 2 : ℝ) * ‖slabK x alpha V d‖ := by
        have h1 := norm_nonneg (slabS0 x alpha d)
        have h2 : (0 : ℝ) ≤ (1 / 2 : ℝ) := by norm_num
        have h3 := norm_nonneg (slabK x alpha V d)
        exact add_le_add (mul_le_mul_of_nonneg_right hf h1)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmu h2) h3)
    _ = Real.log d * ‖slabS0 x alpha d‖ + (1 / 2 : ℝ) * ‖slabK x alpha V d‖ := by ring
    _ ≤ Real.log d * ‖slabS0 x alpha d‖ + ‖slabK x alpha V d‖ := by
        have h2 := norm_nonneg (slabK x alpha V d)
        linarith
    _ = ‖slabK x alpha V d‖ + Real.log d * ‖slabS0 x alpha d‖ := by ring
    _ = ‖slabK x alpha V d + repAlign (slabK x alpha V d) (slabS0 x alpha d)
          * (Real.log d : ℂ) * slabS0 x alpha d‖ :=
        repAlign_spec (slabK x alpha V d) (slabS0 x alpha d) (Real.log d) hlog

/-- **Child3 repair (restricted-log Type I envelope).**  With the logarithmic weight of the
Type I envelope restricted to the transferred support `n > V` for `d > ⌊U⌋₊` (the constant
weight staying unrestricted), the centred Vaughan Type I part `eta0VaughanTypeISum` is
bounded, per outer divisor `d`, by the aligned slab norm
`‖S1(d) + c(d)·log d·S0(d)‖` (resp. `‖K(d) + c(d)·log d·S0(d)‖`), with no Möbius
cancellation input. -/
theorem theorem51_child3_restricted_log_repair
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (_hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ∃ c : ℕ → ℂ, (∀ d ∈ theorem51Divisors U V, ‖c d‖ ≤ 1) ∧
      ‖eta0VaughanTypeISum x alpha U V‖ ≤
        ∑ d ∈ theorem51Divisors U V, ‖
          (if d ≤ ⌊U⌋₊
            then ∑ w ∈ fullInnerSupport x d,
                   ((Real.log (w : ℝ) : ℂ) * eta0VaughanTest x alpha (d * w))
            else ∑ w ∈ transferredInnerSupport x V d,
                   ((Real.log (w : ℝ) : ℂ) * eta0VaughanTest x alpha (d * w)))
          + c d * (Real.log d : ℂ) *
              (∑ w ∈ fullInnerSupport x d, eta0VaughanTest x alpha (d * w))‖ := by
  classical
  have hx : 0 < x := by linarith
  have hU0 : (0 : ℝ) ≤ U := by linarith
  have hV1 : (1 : ℝ) ≤ V := by linarith
  refine ⟨fun d =>
      if d ≤ ⌊U⌋₊ then repAlign (slabS1 x alpha d) (slabS0 x alpha d)
      else repAlign (slabK x alpha V d) (slabS0 x alpha d), ?_, ?_⟩
  · intro d hdD
    rw [theorem51Divisors, Finset.mem_filter, Finset.mem_Icc] at hdD
    by_cases hdU : d ≤ ⌊U⌋₊
    · simp only [hdU, if_true]
      exact le_of_eq (norm_repAlign _ _)
    · simp only [hdU, if_false]
      exact le_of_eq (norm_repAlign _ _)
  · have hEV := TypeIOuterDAssembly.eta0VaughanTypeISum_eq_supported_outer_assembly
      x alpha U V hx hU0 hV1 hUVx hUV2
    rw [hEV]
    have hsupp : (∑ d ∈ Finset.Ioc 0 ⌊U * V⌋₊,
          TypeIOuterDAssembly.supportedOuterSlice x alpha U V d)
        = ∑ d ∈ Finset.Ioc 0 ⌊U * V⌋₊, outerSlice x alpha U V d := by
      apply Finset.sum_congr rfl
      intro d _
      rw [TypeIOuterDAssembly.supportedOuterSlice_eq]
    rw [hsupp]
    refine le_trans (norm_sum_le _ _) ?_
    have hsubset : theorem51Divisors U V ⊆ Finset.Ioc 0 ⌊U * V⌋₊ := by
      intro d hdD
      rw [theorem51Divisors, Finset.mem_filter, Finset.mem_Icc] at hdD
      rw [Finset.mem_Ioc]
      exact ⟨by omega, hdD.1.2⟩
    have hzero : ∀ d ∈ Finset.Ioc 0 ⌊U * V⌋₊, d ∉ theorem51Divisors U V →
        ‖outerSlice x alpha U V d‖ = 0 := by
      intro d hdBig hdNot
      have hdodd : ¬ d.Coprime 2 := by
        intro hc
        apply hdNot
        rw [theorem51Divisors, Finset.mem_filter, Finset.mem_Icc]
        rw [Finset.mem_Ioc] at hdBig
        exact ⟨⟨by omega, hdBig.2⟩, hc⟩
      rw [TypeIOrdinaryFinalAssembly.outerSlice_eq_zero_of_not_coprime_two x alpha U V d hdodd,
        norm_zero]
    have hrestrict : (∑ d ∈ Finset.Ioc 0 ⌊U * V⌋₊, ‖outerSlice x alpha U V d‖)
        = ∑ d ∈ theorem51Divisors U V, ‖outerSlice x alpha U V d‖ := by
      symm
      exact Finset.sum_subset hsubset hzero
    rw [hrestrict]
    apply Finset.sum_le_sum
    intro d hdD
    rw [theorem51Divisors, Finset.mem_filter, Finset.mem_Icc] at hdD
    obtain ⟨⟨hd1, _⟩, _⟩ := hdD
    by_cases hdU : d ≤ ⌊U⌋₊
    · simp only [hdU, if_true]
      exact norm_outerSlice_le_branch_low x alpha U V d hd1 hdU
    · simp only [hdU, if_false]
      exact norm_outerSlice_le_branch_high x alpha U V d hd1 hdU

end TaoFivePrimes

open TaoFivePrimes

theorem solution
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ∃ c : ℕ → ℂ, (∀ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖c d‖ ≤ 1) ∧
      ‖TaoFivePrimes.eta0VaughanTypeISum x alpha U V‖ ≤
        ∑ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖
          (if d ≤ ⌊U⌋₊
            then ∑ w ∈ TaoFivePrimes.TypeIOuterDAssembly.fullInnerSupport x d,
                   ((Real.log (w : ℝ) : ℂ) * TaoFivePrimes.eta0VaughanTest x alpha (d * w))
            else ∑ w ∈ TaoFivePrimes.TypeIOuterDAssembly.transferredInnerSupport x V d,
                   ((Real.log (w : ℝ) : ℂ) * TaoFivePrimes.eta0VaughanTest x alpha (d * w)))
          + c d * (Real.log d : ℂ) *
              (∑ w ∈ TaoFivePrimes.TypeIOuterDAssembly.fullInnerSupport x d,
                TaoFivePrimes.eta0VaughanTest x alpha (d * w))‖ :=
  TaoFivePrimes.theorem51_child3_restricted_log_repair x alpha U V hU hV hUx hVx hUVx hUV2

end
