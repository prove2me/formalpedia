-- Prove2me | solution 1 for TaoFivePrimes.eta0VaughanTypeISum_le_theorem51TypeI
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-22T15:04:50.780328+00:00
-- url     : https://prove2.me/submissions/d8c6aed3-76ee-45b7-8848-ec3e44a13051
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Definitions.Def_TaoFivePrimes_VaughanTruncation
import Definitions.Def_TaoFivePrimes_TypeIEnvelopeInterfaces
import Definitions.Def_TaoFivePrimes_TypeISlabSums
import Theorems.Thm_TaoFivePrimes_theorem51_sharp_transfer_gap

open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction

set_option autoImplicit false
set_option maxRecDepth 10000

section
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
open ArithmeticFunction
namespace TaoFivePrimes
@[simp] theorem arithmeticRestrictLE_apply (B n : ℕ)
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
theorem eta0VaughanTest_eq_explicit_of_mem_open_odd_pairs
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
theorem vaughanTypeICorrectionCoefficient_apply (U V d : ℕ) :
    vaughanTypeICorrectionCoefficient U V d =
      ∑ p ∈ d.divisorsAntidiagonal,
        arithmeticRestrictLE U (μ : ArithmeticFunction ℝ) p.1 *
          arithmeticRestrictLE V ArithmeticFunction.vonMangoldt p.2 := by
  rfl
theorem vaughanTypeICorrectionCoefficient_eq_zero_of_mul_lt
    (U V d : ℕ) (hd : U * V < d) :
    vaughanTypeICorrectionCoefficient U V d = 0 := by
  rw [vaughanTypeICorrectionCoefficient_apply]
  apply Finset.sum_eq_zero
  intro p hp
  simp only [arithmeticRestrictLE_apply]
  by_cases ha : p.1 ≤ U
  · have hb : ¬p.2 ≤ V := by
      intro hb
      have hprod : p.1 * p.2 ≤ U * V := Nat.mul_le_mul ha hb
      have heq : p.1 * p.2 = d :=
        (Nat.mem_divisorsAntidiagonal.mp hp).1
      omega
    simp [ha, hb]
  · simp [ha]
theorem abs_vaughanTypeICorrectionCoefficient_le_log
    (U V d : ℕ) (_hd : 0 < d) :
    |vaughanTypeICorrectionCoefficient U V d| ≤ Real.log (d : ℝ) := by
  rw [vaughanTypeICorrectionCoefficient_apply]
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
      simp only [arithmeticRestrictLE_apply]
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
theorem eta0_nonneg_grid (t : ℝ) : 0 ≤ eta0 t := by
  unfold eta0
  split_ifs <;> positivity
theorem norm_moebius_real_complex_le_one (d : ℕ) :
    ‖(((μ d : ℝ) : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hmuZ : |μ d| ≤ (1 : ℤ) := ArithmeticFunction.abs_moebius_le_one
  exact_mod_cast hmuZ
end TypeIOddGridFirstVariation
end TaoFivePrimes
end
end

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
theorem fullInnerSupport_mem_open
    {x : ℝ} {d w : ℕ} (hw : w ∈ fullInnerSupport x d) :
    (d, w) ∈ eta0VaughanOpenOddPairs x := by
  exact (Finset.mem_filter.mp hw).2
theorem transferredInnerSupport_mem_full
    {x V : ℝ} {d w : ℕ} (hw : w ∈ transferredInnerSupport x V d) :
    w ∈ fullInnerSupport x d ∧ ⌊V⌋₊ < w := by
  exact Finset.mem_filter.mp hw
theorem eta0VaughanTest_eq_explicit_of_mem_fullInnerSupport
    {x alpha : ℝ} {d w : ℕ} (hw : w ∈ fullInnerSupport x d) :
    eta0VaughanTest x alpha (d * w) =
      expCircle (alpha * (d * w)) *
        (eta0 (((d * w : ℕ) : ℝ) / x) : ℂ) := by
  exact eta0VaughanTest_eq_explicit_of_mem_open_odd_pairs
    x alpha (d, w) (fullInnerSupport_mem_open hw)
theorem fullInnerSupport_spec
    {x : ℝ} {d w : ℕ} (hw : w ∈ fullInnerSupport x d) :
    0 < d ∧ 0 < w ∧ d * w ≤ ⌊x⌋₊ ∧
      d.Coprime 2 ∧ w.Coprime 2 ∧
      x / 4 < ((d * w : ℕ) : ℝ) ∧ ((d * w : ℕ) : ℝ) < x := by
  have hopen := fullInnerSupport_mem_open hw
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
  simp only [arithmeticRestrictLE_apply]
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
  have hwpos : 0 < w := (fullInnerSupport_spec hw).2.1
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
      have hs := fullInnerSupport_spec hwparts.1
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

open Finset

section PartV51
open Finset
namespace TaoV51

open TaoFivePrimes

theorem eta0_eq_zero_of_le {t : ℝ} (h : t ≤ 1/4) : eta0 t = 0 := by
  unfold eta0
  split_ifs with h0
  · have h1 : Real.log (2 * t) ≤ Real.log 2 + Real.log (1/4) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      apply Real.log_le_log (by linarith)
      linarith
    have h2 : Real.log (1/4) = -(2 * Real.log 2) := by
      rw [show (1:ℝ)/4 = (2:ℝ)⁻¹ ^ 2 by norm_num, Real.log_pow, Real.log_inv]
      ring
    have h3 : Real.log (2 * t) ≤ -Real.log 2 := by rw [h2] at h1; linarith
    have h4 : Real.log 2 ≤ |Real.log (2 * t)| := by
      have : Real.log 2 ≤ -Real.log (2*t) := by linarith
      calc Real.log 2 ≤ -Real.log (2*t) := this
        _ ≤ |Real.log (2*t)| := neg_le_abs _
    rw [max_eq_left (by linarith)]
    ring
  · rfl

theorem eta0_eq_zero_of_ge {t : ℝ} (h : 1 ≤ t) : eta0 t = 0 := by
  unfold eta0
  split_ifs with h0
  · have h1 : Real.log 2 ≤ Real.log (2 * t) := by
      apply Real.log_le_log (by norm_num); linarith
    have h4 : Real.log 2 ≤ |Real.log (2 * t)| := le_trans h1 (le_abs_self _)
    rw [max_eq_left (by linarith)]
    ring
  · rfl

theorem eta0_eq_zero_of_nonpos {t : ℝ} (h : t ≤ 0) : eta0 t = 0 := by
  unfold eta0
  rw [if_neg (by linarith)]

/-- The test function attached to `S_{eta0,2}(x, alpha)`. -/
noncomputable def FF (x alpha : ℝ) (n : ℕ) : ℂ :=
  if n.Coprime 2 then expCircle (alpha * n) * (eta0 ((n : ℝ) / x) : ℂ) else 0

theorem FF_even {x alpha : ℝ} {n : ℕ} (h : ¬ n.Coprime 2) : FF x alpha n = 0 := by
  unfold FF; rw [if_neg h]

theorem smoothedExpSum_eq_sum (x alpha : ℝ) (hx : 0 < x) (N : ℕ) (hN : x < N) :
    smoothedExpSum eta0 2 x alpha
      = ∑ n ∈ Finset.range N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * FF x alpha n := by
  unfold smoothedExpSum
  have hz : ∀ n : ℕ, n ∉ Finset.range N →
      (if Nat.Coprime n 2 then
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * expCircle (alpha * n) *
          ((eta0 ((n : ℝ) / x) : ℝ) : ℂ) else 0) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have h1 : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : (1 : ℝ) ≤ (n : ℝ) / x := by
      rw [le_div_iff₀ hx]; linarith
    rw [eta0_eq_zero_of_ge h2]
    simp
  rw [tsum_eq_sum hz]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  unfold FF
  split_ifs with h
  · push_cast; ring
  · ring


theorem FF_zero_of_small {x alpha : ℝ} (hx : 0 < x) {n : ℕ} (h : 4 * (n : ℝ) < x) :
    FF x alpha n = 0 := by
  unfold FF
  have : (n : ℝ) / x ≤ 1/4 := by
    rw [div_le_iff₀ hx]; linarith
  rw [eta0_eq_zero_of_le this]
  split_ifs <;> simp

theorem FF_zero_of_big {x alpha : ℝ} (hx : 0 < x) {n : ℕ} (h : x < (n : ℝ)) :
    FF x alpha n = 0 := by
  unfold FF
  have : (1 : ℝ) ≤ (n : ℝ) / x := by
    rw [le_div_iff₀ hx]; linarith
  rw [eta0_eq_zero_of_ge this]
  split_ifs <;> simp

/-- The Type I inner sum, in the odd parametrization used by `theorem51TypeI`. -/
theorem typeI_inner (x alpha : ℝ) (hx : 0 < x) (N : ℕ) (hN : x < N)
    (d : ℕ) (hd : 0 < d) (hdodd : d.Coprime 2) (cd : ℂ) :
    (∑ m ∈ Finset.range N, ((ArithmeticFunction.log m : ℝ) : ℂ) * FF x alpha (d * m))
        + cd * (Real.log d : ℂ) *
          (∑ m ∈ Finset.range N, ((zetaR m : ℝ) : ℂ) * FF x alpha (d * m))
      = ∑' n : ℤ, (((Real.log ((2 * n + 1 : ℤ) : ℝ) : ℂ) + cd * (Real.log d : ℂ)) *
          ((eta0 ((d : ℝ) * ((2 * n + 1 : ℤ) : ℝ) / x) : ℝ) : ℂ)) *
          expCircle (alpha * d * ((2 * n + 1 : ℤ) : ℝ)) := by
  classical
  set ψ : ℕ → ℂ := fun m =>
    ((Real.log m : ℝ) : ℂ) * FF x alpha (d * m)
      + cd * (Real.log d : ℂ) * (((zetaR m : ℝ) : ℂ) * FF x alpha (d * m)) with hψ
  set φ : ℤ → ℂ := fun n =>
    (((Real.log ((2 * n + 1 : ℤ) : ℝ) : ℂ) + cd * (Real.log d : ℂ)) *
      ((eta0 ((d : ℝ) * ((2 * n + 1 : ℤ) : ℝ) / x) : ℝ) : ℂ)) *
      expCircle (alpha * d * ((2 * n + 1 : ℤ) : ℝ)) with hφ
  have hlhs : (∑ m ∈ Finset.range N, ((ArithmeticFunction.log m : ℝ) : ℂ) * FF x alpha (d * m))
        + cd * (Real.log d : ℂ) *
          (∑ m ∈ Finset.range N, ((zetaR m : ℝ) : ℂ) * FF x alpha (d * m))
      = ∑ m ∈ Finset.range N, ψ m := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [hψ]
    simp only [ArithmeticFunction.log_apply]
  rw [hlhs]
  -- the `ℤ`-sum is finitely supported
  have hsupp : ∀ n : ℤ, n ∉ (Finset.range N).image (fun k : ℕ => (k : ℤ)) → φ n = 0 := by
    intro n hn
    have hcase : n < 0 ∨ (N : ℤ) ≤ n := by
      by_contra hcon
      push_neg at hcon
      exact hn (Finset.mem_image.mpr ⟨n.toNat, Finset.mem_range.mpr (by omega),
        Int.toNat_of_nonneg hcon.1⟩)
    have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    rcases hcase with h | h
    · have h1 : ((2 * n + 1 : ℤ) : ℝ) ≤ -1 := by
        have : (2 * n + 1 : ℤ) ≤ -1 := by omega
        exact_mod_cast this
      have : (d : ℝ) * ((2 * n + 1 : ℤ) : ℝ) / x ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg _ hx.le
        nlinarith
      rw [hφ]
      simp only
      rw [eta0_eq_zero_of_nonpos this]
      simp
    · have h1 : (N : ℝ) ≤ ((2 * n + 1 : ℤ) : ℝ) := by
        have : (N : ℤ) ≤ 2 * n + 1 := by omega
        exact_mod_cast this
      have h2 : (1 : ℝ) ≤ (d : ℝ) * ((2 * n + 1 : ℤ) : ℝ) / x := by
        rw [le_div_iff₀ hx]
        nlinarith
      rw [hφ]
      simp only
      rw [eta0_eq_zero_of_ge h2]
      simp
  rw [tsum_eq_sum hsupp, Finset.sum_image (fun a _ b _ h => by exact_mod_cast h)]
  -- both sides are supported on the odd residues
  set O : Finset ℕ := (Finset.range N).filter (fun m => m % 2 = 1) with hO
  set Z : Finset ℕ := (Finset.range N).filter (fun k => 2 * k + 1 < N) with hZ
  have hLo : (∑ m ∈ Finset.range N, ψ m) = ∑ m ∈ O, ψ m := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro m hm hmO
    have hme : ¬ m % 2 = 1 := by
      intro hcon; exact hmO (Finset.mem_filter.mpr ⟨hm, hcon⟩)
    have : ¬ (d * m).Coprime 2 := by
      have h2 : 2 ∣ m := by omega
      intro hcop
      have : (2 : ℕ) ∣ d * m := Dvd.dvd.mul_left h2 d
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hcop) this
      omega
    simp only [hψ, FF_even this, mul_zero, zero_add, add_zero]
  have hRo : (∑ k ∈ Finset.range N, φ (k : ℤ)) = ∑ k ∈ Z, φ (k : ℤ) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro k hk hkZ
    have hbig : N ≤ 2 * k + 1 := by
      by_contra hcon
      exact hkZ (Finset.mem_filter.mpr ⟨hk, by omega⟩)
    have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have h1 : (N : ℝ) ≤ ((2 * (k : ℤ) + 1 : ℤ) : ℝ) := by
      have : (N : ℤ) ≤ 2 * (k : ℤ) + 1 := by exact_mod_cast hbig
      exact_mod_cast this
    have h2 : (1 : ℝ) ≤ (d : ℝ) * ((2 * (k : ℤ) + 1 : ℤ) : ℝ) / x := by
      rw [le_div_iff₀ hx]
      nlinarith
    rw [hφ]
    simp only
    rw [eta0_eq_zero_of_ge h2]
    simp
  rw [hLo, hRo]
  refine (Finset.sum_nbij' (fun k => 2 * k + 1) (fun m => m / 2) ?_ ?_ ?_ ?_ ?_).symm
  · intro k hk
    rw [hZ, Finset.mem_filter, Finset.mem_range] at hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk.2, by omega⟩
  · intro m hm
    rw [hO, Finset.mem_filter, Finset.mem_range] at hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩
  · intro k hk; omega
  · intro m hm
    rw [hO, Finset.mem_filter] at hm
    omega
  · intro k hk
    rw [hZ, Finset.mem_filter, Finset.mem_range] at hk
    have hodd : (d * (2 * k + 1)).Coprime 2 := by
      refine Nat.Coprime.mul hdodd ?_
      exact Nat.coprime_two_right.mpr ⟨k, by ring⟩
    simp only [hψ, hφ, FF]
    rw [if_pos hodd]
    have hcast : (((d * (2 * k + 1) : ℕ)) : ℝ) = (d : ℝ) * ((2 * (k : ℤ) + 1 : ℤ) : ℝ) := by
      push_cast; ring
    have hzeta : ((zetaR (2 * k + 1) : ℝ) : ℂ) = 1 := by
      simp [zetaR]
    have hlogm : ((Real.log ((2 * k + 1 : ℕ) : ℝ) : ℝ) : ℂ)
        = ((Real.log ((2 * (k : ℤ) + 1 : ℤ) : ℝ) : ℝ) : ℂ) := by
      norm_num
    rw [hzeta, hcast, hlogm]
    push_cast
    ring

theorem truncGt_mul_zeta (V : ℝ) (w : ℕ) :
    (TaoFivePrimes.truncGt V ArithmeticFunction.vonMangoldt * zetaR) w
      = theorem51Centered V w + Real.log w / 2 := by
  rw [zetaR, ArithmeticFunction.coe_mul_zeta_apply, theorem51Centered]
  have : ∑ i ∈ w.divisors, TaoFivePrimes.truncGt V ArithmeticFunction.vonMangoldt i
      = ∑ b ∈ w.divisors.filter (fun b : ℕ => V < (b : ℝ)), ArithmeticFunction.vonMangoldt b := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun i _ => by rw [TaoFivePrimes.truncGt_apply])
  rw [this]
  ring

theorem truncGt_mul_zeta_eq_zero {V : ℝ} {w : ℕ} (h : (w : ℝ) ≤ V) :
    (TaoFivePrimes.truncGt V ArithmeticFunction.vonMangoldt * zetaR) w = 0 := by
  rw [zetaR, ArithmeticFunction.coe_mul_zeta_apply]
  refine Finset.sum_eq_zero (fun i hi => ?_)
  rw [TaoFivePrimes.truncGt_apply, if_neg]
  intro hlt
  have hdvd : i ∣ w := (Nat.mem_divisors.mp hi).1
  have hw0 : w ≠ 0 := (Nat.mem_divisors.mp hi).2
  have : i ≤ w := Nat.le_of_dvd (Nat.pos_of_ne_zero hw0) hdvd
  have : (i : ℝ) ≤ (w : ℝ) := by exact_mod_cast this
  linarith

theorem coprime_two_mul {d w : ℕ} : (d * w).Coprime 2 ↔ d.Coprime 2 ∧ w.Coprime 2 := by
  constructor
  · intro h
    exact ⟨Nat.Coprime.coprime_dvd_left ⟨w, rfl⟩ h,
      Nat.Coprime.coprime_dvd_left ⟨d, by ring⟩ h⟩
  · rintro ⟨h1, h2⟩
    exact Nat.Coprime.mul h1 h2

/-- The Type II sum, in the doubly-indexed form used by `theorem51TypeII`. -/
theorem typeII_eq (x alpha U V : ℝ) (hx : 0 < x) (hU : 1 ≤ U) (N : ℕ) (hN : x < N) :
    (∑ d ∈ Finset.range N, ∑ w ∈ Finset.range N,
        ((TaoFivePrimes.truncGt U moebiusR d : ℝ) : ℂ) *
          (((TaoFivePrimes.truncGt V ArithmeticFunction.vonMangoldt * zetaR) w : ℝ) : ℂ) *
          FF x alpha (d * w))
      = ∑' d : ℕ, ∑' w : ℕ,
          (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
            ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
              (((theorem51Centered V w + Real.log w / 2 : ℝ)) : ℂ) *
              expCircle (alpha * d * w) * ((eta0 ((d : ℝ) * (w : ℝ) / x) : ℝ) : ℂ)
          else 0) := by
  classical
  set G : ℕ → ℕ → ℂ := fun d w =>
    (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
      ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (((theorem51Centered V w + Real.log w / 2 : ℝ)) : ℂ) *
        expCircle (alpha * d * w) * ((eta0 ((d : ℝ) * (w : ℝ) / x) : ℝ) : ℂ)
    else 0) with hG
  -- the two summands agree
  have hterm : ∀ d w : ℕ,
      ((TaoFivePrimes.truncGt U moebiusR d : ℝ) : ℂ) *
        (((TaoFivePrimes.truncGt V ArithmeticFunction.vonMangoldt * zetaR) w : ℝ) : ℂ) *
        FF x alpha (d * w) = G d w := by
    intro d w
    rw [hG]
    simp only
    by_cases hd : U < (d : ℝ)
    · by_cases hw : V < (w : ℝ)
      · by_cases hc : d.Coprime 2 ∧ w.Coprime 2
        · rw [if_pos ⟨hd, hw, hc.1, hc.2⟩, TaoFivePrimes.truncGt_apply, if_pos hd,
            truncGt_mul_zeta, FF, if_pos (coprime_two_mul.mpr hc)]
          have hcast : (((d * w : ℕ)) : ℝ) = (d : ℝ) * (w : ℝ) := by push_cast; ring
          rw [hcast]
          simp only [moebiusR, ArithmeticFunction.intCoe_apply]
          push_cast
          ring
        · rw [if_neg (by tauto), FF, if_neg (fun hcon => hc (coprime_two_mul.mp hcon))]
          ring
      · rw [if_neg (by tauto), truncGt_mul_zeta_eq_zero (not_lt.mp hw)]
        simp
    · rw [if_neg (by tauto), TaoFivePrimes.truncGt_apply, if_neg hd]
      simp
  simp only [hterm]
  -- the sums are finite
  have hGzero : ∀ d w : ℕ, N ≤ d ∨ N ≤ w → G d w = 0 := by
    intro d w h
    rw [hG]
    simp only
    by_cases hcond : U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
    · rw [if_pos hcond]
      have hd1 : 1 ≤ d := by
        by_contra hcon
        have hd0 : d = 0 := by omega
        have h0 := hcond.1
        rw [hd0] at h0
        norm_num at h0
        linarith
      have hw1 : 1 ≤ w := by
        by_contra hcon
        have hw0 : w = 0 := by omega
        rw [hw0] at hcond
        have := hcond.2.2.2
        simp [Nat.Coprime] at this
      have hbig : (N : ℝ) ≤ (d : ℝ) * (w : ℝ) := by
        rcases h with h | h
        · have h1 : (N : ℝ) ≤ (d : ℝ) := by exact_mod_cast h
          have h2 : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw1
          nlinarith [Nat.cast_nonneg (α := ℝ) d]
        · have h1 : (N : ℝ) ≤ (w : ℝ) := by exact_mod_cast h
          have h2 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
          nlinarith [Nat.cast_nonneg (α := ℝ) w]
      have : (1 : ℝ) ≤ (d : ℝ) * (w : ℝ) / x := by
        rw [le_div_iff₀ hx]; linarith
      rw [eta0_eq_zero_of_ge this]
      simp
    · rw [if_neg hcond]
  have hinner : ∀ d : ℕ, (∑' w : ℕ, G d w) = ∑ w ∈ Finset.range N, G d w := by
    intro d
    refine tsum_eq_sum (fun w hw => hGzero d w (Or.inr ?_))
    rw [Finset.mem_range, not_lt] at hw; exact hw
  rw [tsum_congr hinner]
  refine (tsum_eq_sum (fun d hd => ?_)).symm
  rw [Finset.mem_range, not_lt] at hd
  exact Finset.sum_eq_zero (fun w _ => hGzero d w (Or.inl hd))

/-- The unit-modulus factor aligning two complex numbers. -/
noncomputable def align (S1 S0 : ℂ) : ℂ :=
  if S1 = 0 ∨ S0 = 0 then 1 else (S1 / (‖S1‖ : ℂ)) * ((‖S0‖ : ℂ) / S0)

theorem norm_align (S1 S0 : ℂ) : ‖align S1 S0‖ = 1 := by
  unfold align
  split_ifs with h
  · simp
  · push_neg at h
    rw [norm_mul, norm_div, norm_div]
    simp [Complex.norm_real, h.1, h.2]

theorem align_spec (S1 S0 : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    ‖S1‖ + t * ‖S0‖ = ‖S1 + align S1 S0 * (t : ℂ) * S0‖ := by
  unfold align
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

theorem abs_moebiusR_le_one (d : ℕ) : |(moebiusR d : ℝ)| ≤ 1 := by
  simp only [moebiusR, ArithmeticFunction.intCoe_apply]
  by_cases h : Squarefree d
  · have h1 : (ArithmeticFunction.moebius d) ^ 2 = 1 :=
      ArithmeticFunction.moebius_sq_eq_one_of_squarefree h
    have h2 : ((ArithmeticFunction.moebius d : ℝ)) ^ 2 = 1 := by exact_mod_cast h1
    nlinarith [abs_nonneg ((ArithmeticFunction.moebius d : ℝ)), sq_abs ((ArithmeticFunction.moebius d : ℝ))]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
    simp

theorem truncLe_mul_eq_zero {U V : ℝ} {d : ℕ} (h : U * V < (d : ℝ)) (hU : 0 < U) (hV : 0 < V) :
    (TaoFivePrimes.truncLe U moebiusR * TaoFivePrimes.truncLe V ArithmeticFunction.vonMangoldt) d
      = 0 := by
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero (fun z hz => ?_)
  rw [Nat.mem_divisorsAntidiagonal] at hz
  rw [TaoFivePrimes.truncLe_apply, TaoFivePrimes.truncLe_apply]
  by_cases ha : (z.1 : ℝ) ≤ U
  · by_cases hb : (z.2 : ℝ) ≤ V
    · exfalso
      have hz1 : (0:ℝ) ≤ (z.1 : ℝ) := Nat.cast_nonneg _
      have hz2 : (0:ℝ) ≤ (z.2 : ℝ) := Nat.cast_nonneg _
      have : ((d : ℕ) : ℝ) = (z.1 : ℝ) * (z.2 : ℝ) := by
        rw [← hz.1]; push_cast; ring
      nlinarith
    · rw [if_neg hb]; ring
  · rw [if_neg ha]; ring

end TaoV51
end PartV51

section
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
open ArithmeticFunction
set_option autoImplicit false
noncomputable section
namespace TaoFivePrimes
namespace TypeIOddGridFirstVariation
noncomputable def eta0TypeIInnerSupport (x : ℝ) (d : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 ⌊x⌋₊).filter fun w =>
    d * w ≤ ⌊x⌋₊ ∧ w.Coprime 2 ∧
      x / 4 < ((d * w : ℕ) : ℝ) ∧ ((d * w : ℕ) : ℝ) < x
end TypeIOddGridFirstVariation
namespace TypeIOuterDSupportBridge
open TaoFivePrimes.TypeIOuterDAssembly
open TaoFivePrimes.TypeIOddGridFirstVariation
theorem fullInnerSupport_eq_eta0TypeIInnerSupport
    (x : ℝ) (d : ℕ) (hd : 0 < d) (hdx : d ≤ ⌊x⌋₊)
    (hdodd : d.Coprime 2) :
    fullInnerSupport x d = eta0TypeIInnerSupport x d := by
  have hdo : Odd d := Nat.coprime_two_right.mp hdodd
  ext w
  simp [fullInnerSupport, eta0TypeIInnerSupport,
    eta0VaughanOpenOddPairs, hd, hdx, hdo]
end TypeIOuterDSupportBridge
end TaoFivePrimes
end
end

namespace TaoFivePrimes

open TypeIOuterDAssembly TypeIOddGridFirstVariation TypeIOuterDSupportBridge

/-- The outer slice, rewritten as a single sum over the full inner support with the
combined coefficient `fullCombinedCoefficient + 1_{(⌊V⌋ < w)} transferredCoefficient`. -/
theorem outerSlice_eq_single_full_support_sum
    (x alpha U V : ℝ) (d : ℕ) :
    outerSlice x alpha U V d =
      ∑ w ∈ fullInnerSupport x d,
        (((fullCombinedCoefficient U V d w +
            if ⌊V⌋₊ < w then transferredCoefficient U d w else 0 : ℝ) : ℂ)) *
          eta0VaughanTest x alpha (d * w) := by
  unfold outerSlice transferredInnerSupport
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases hwV : ⌊V⌋₊ < w
  · simp [hwV]
    ring
  · simp [hwV]

/-- **First slab regime (`d ≤ ⌊U⌋`)**. The outer slice is exactly
`μ d · S1 d − f d · S0 d` with `f = μ_{≤⌊U⌋} * Λ_{≤⌊V⌋}`. -/
theorem outerSlice_eq_mu_mul_S1_sub_f_mul_S0
    (x alpha U V : ℝ) (d : ℕ) (hd : d ≤ ⌊U⌋₊) :
    outerSlice x alpha U V d =
      (μ d : ℂ) * typeISlabS1 x alpha d -
        ((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ) *
          typeISlabS0 x alpha d := by
  rw [outerSlice_eq_single_full_support_sum]
  have hUd : ¬ ⌊U⌋₊ < d := not_lt.mpr hd
  have hcoeff : ∀ w : ℕ,
      ((fullCombinedCoefficient U V d w +
          if ⌊V⌋₊ < w then transferredCoefficient U d w else 0 : ℝ)) =
        (μ d : ℝ) * Real.log (w : ℝ) -
          vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d := by
    intro w
    by_cases hwV : ⌊V⌋₊ < w
    · simp only [fullCombinedCoefficient, transferredCoefficient, if_pos hd,
        if_neg hUd, if_pos hwV, add_zero]
    · simp only [fullCombinedCoefficient, transferredCoefficient, if_pos hd,
        if_neg hUd, if_neg hwV, add_zero]
  simp_rw [hcoeff]
  rw [typeISlabS1, typeISlabS0, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  push_cast
  ring

/-- **Second slab regime (`⌊U⌋ < d`)**. The outer slice is exactly
`(μ d / 2) · K d − f d · S0 d`. -/
theorem outerSlice_eq_half_mu_mul_K_sub_f_mul_S0
    (x alpha U V : ℝ) (d : ℕ) (hd : ⌊U⌋₊ < d) :
    outerSlice x alpha U V d =
      (μ d : ℂ) * (1 / 2 : ℂ) * typeISlabK x alpha V d -
        ((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ) *
          typeISlabS0 x alpha d := by
  have hcoeff : ∀ w : ℕ,
      ((fullCombinedCoefficient U V d w +
          if ⌊V⌋₊ < w then transferredCoefficient U d w else 0 : ℝ)) =
        (if ⌊V⌋₊ < w then (μ d : ℝ) * ((1 / 2 : ℝ) * Real.log (w : ℝ)) else 0) -
          vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d := by
    intro w
    by_cases hwV : ⌊V⌋₊ < w
    · simp only [fullCombinedCoefficient, transferredCoefficient,
        if_neg (not_le.mpr hd), if_pos hd, if_pos hwV]
      ring
    · simp only [fullCombinedCoefficient, transferredCoefficient,
        if_neg (not_le.mpr hd), if_pos hd, if_neg hwV, add_zero]
  have hpt : ∀ w : ℕ,
      (((if ⌊V⌋₊ < w then
            (μ d : ℝ) * ((1 / 2 : ℝ) * Real.log (w : ℝ)) else 0) -
          vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ) *
          eta0VaughanTest x alpha (d * w) =
      (if ⌊V⌋₊ < w then
          (μ d : ℂ) * (1 / 2 : ℂ) *
            ((Real.log (w : ℝ) : ℂ) * eta0VaughanTest x alpha (d * w))
        else 0) -
        (((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ) *
          eta0VaughanTest x alpha (d * w)) := by
    intro w
    by_cases hwV : ⌊V⌋₊ < w
    · rw [if_pos hwV, if_pos hwV]
      push_cast
      ring
    · rw [if_neg hwV, if_neg hwV]
      push_cast
      ring
  rw [outerSlice_eq_single_full_support_sum]
  simp_rw [hcoeff, hpt]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [← Finset.sum_filter, typeISlabK, Finset.mul_sum]
    rfl
  · rw [typeISlabS0, Finset.mul_sum]

/-- For even `d` the Vaughan test vanishes at every multiple. -/
theorem eta0VaughanTest_eq_zero_of_not_coprime_two
    (x alpha : ℝ) (d w : ℕ) (hd : ¬ d.Coprime 2) :
    eta0VaughanTest x alpha (d * w) = 0 := by
  have hnot : ¬ (d * w).Coprime 2 := fun hc =>
    hd (hc.coprime_dvd_left (Nat.dvd_mul_right d w))
  simp [eta0VaughanTest, hnot]

/-- For even `d` the outer slice vanishes. -/
theorem outerSlice_eq_zero_of_even
    (x alpha U V : ℝ) (d : ℕ) (hd : ¬ d.Coprime 2) :
    outerSlice x alpha U V d = 0 := by
  unfold outerSlice
  have h1 : (∑ w ∈ fullInnerSupport x d,
      ((fullCombinedCoefficient U V d w : ℝ) : ℂ) *
        eta0VaughanTest x alpha (d * w)) = 0 :=
    Finset.sum_eq_zero (fun w _ => by
      rw [eta0VaughanTest_eq_zero_of_not_coprime_two x alpha d w hd]
      ring)
  have h2 : (∑ w ∈ transferredInnerSupport x V d,
      ((transferredCoefficient U d w : ℝ) : ℂ) *
        eta0VaughanTest x alpha (d * w)) = 0 :=
    Finset.sum_eq_zero (fun w _ => by
      rw [eta0VaughanTest_eq_zero_of_not_coprime_two x alpha d w hd]
      ring)
  rw [h1, h2, zero_add]

/-- **Master decomposition (align route).** With `e_d = 1_{d ≤ ⌊U⌋} · μ d`, `f = μ_{≤⌊U⌋} * Λ_{≤⌊V⌋}`,
`D = theorem51Divisors U V`, the smoothed Vaughan Type I sum equals the uncentred part
`A = Σ_{d∈D} (e_d · S1_d − f_d · S0_d)` plus the transferred half-log part
`S3' = Σ_{d∈D, ⌊U⌋ < d} (μ d / 2) · K_d`. -/
theorem eta0VaughanTypeISum_eq_A_add_S3
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (_hVx : V < x) (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    eta0VaughanTypeISum x alpha U V =
      (∑ d ∈ theorem51Divisors U V,
          ((if d ≤ ⌊U⌋₊ then (μ d : ℂ) else 0) * typeISlabS1 x alpha d -
            ((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ) *
              typeISlabS0 x alpha d))
        + ∑ d ∈ (theorem51Divisors U V).filter (fun d => ⌊U⌋₊ < d),
            ((μ d : ℂ) * (1 / 2 : ℂ)) * typeISlabK x alpha V d := by
  have hx0 : 0 < x := by linarith
  rw [eta0VaughanTypeISum_eq_sum_outerSlice_full_range x alpha U V hx0]
  have hsub : theorem51Divisors U V ⊆ Finset.Ioc 0 ⌊x⌋₊ := by
    intro d hd
    rw [Finset.mem_Ioc]
    have hdIcc := (Finset.mem_filter.mp hd).1
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
    have hdUV : d ≤ ⌊U * V⌋₊ := (Finset.mem_Icc.mp hdIcc).2
    have h1 : ⌊U * V⌋₊ ≤ ⌊x / 4⌋₊ := Nat.floor_mono hUVx
    have h2 : ⌊x / 4⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono (by linarith)
    omega
  have hzero : ∀ d ∈ Finset.Ioc 0 ⌊x⌋₊, d ∉ theorem51Divisors U V →
      outerSlice x alpha U V d = 0 := by
    intro d hdIoc hdD
    rw [Finset.mem_Ioc] at hdIoc
    by_cases hcop : d.Coprime 2
    · apply outerSlice_eq_zero_of_floor_mul_lt x alpha U V (by linarith) (by linarith) hUV2
      by_contra hle
      have hle' : d ≤ ⌊U * V⌋₊ := le_of_not_gt hle
      exact hdD (by
        unfold theorem51Divisors
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hdIoc.1, hle'⟩, hcop⟩)
    · exact outerSlice_eq_zero_of_even x alpha U V d hcop
  rw [← Finset.sum_subset hsub hzero]
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  by_cases hdU : d ≤ ⌊U⌋₊
  · rw [if_pos hdU, if_neg (not_lt.mpr hdU)]
    rw [outerSlice_eq_mu_mul_S1_sub_f_mul_S0 x alpha U V d hdU]
    ring
  · rw [if_neg hdU, if_pos (not_le.mp hdU)]
    rw [outerSlice_eq_half_mu_mul_K_sub_f_mul_S0 x alpha U V d (not_le.mp hdU)]
    ring

/-- **Triangle assembly.** Combining the master decomposition with the per-coefficient budgets
`|e_d| ≤ 1` and `|f_d| ≤ log d` gives
`‖η0VTS‖ ≤ Σ_{d∈D} (‖S1_d‖ + log d · ‖S0_d‖) + ½ Σ_{d∈D, ⌊U⌋ < d} ‖K_d‖`. -/
theorem norm_eta0VaughanTypeISum_le_slab_assembly
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x) (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ‖eta0VaughanTypeISum x alpha U V‖ ≤
      (∑ d ∈ theorem51Divisors U V,
          (‖typeISlabS1 x alpha d‖ + Real.log d * ‖typeISlabS0 x alpha d‖))
        + (1 / 2) * ∑ d ∈ (theorem51Divisors U V).filter (fun d => ⌊U⌋₊ < d),
            ‖typeISlabK x alpha V d‖ := by
  rw [eta0VaughanTypeISum_eq_A_add_S3 x alpha U V hU hV hUx hVx hUVx hUV2]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · refine le_trans (norm_sum_le _ _) ?_
    apply Finset.sum_le_sum
    intro d hd
    have hd1 : 0 < d := by
      have hdIcc := (Finset.mem_filter.mp hd).1
      have := (Finset.mem_Icc.mp hdIcc).1
      omega
    refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
    · rw [norm_mul]
      have he : ‖(if d ≤ ⌊U⌋₊ then (μ d : ℂ) else 0)‖ ≤ 1 := by
        by_cases hdU : d ≤ ⌊U⌋₊
        · rw [if_pos hdU, Complex.norm_intCast]
          exact_mod_cast abs_moebius_le_one (n := d)
        · rw [if_neg hdU]
          simp
      have hb := mul_le_mul_of_nonneg_right he (norm_nonneg (typeISlabS1 x alpha d))
      simpa using hb
    · rw [norm_mul]
      have hf : ‖(((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖ ≤
          Real.log d := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_vaughanTypeICorrectionCoefficient_le_log ⌊U⌋₊ ⌊V⌋₊ d hd1
      have hb := mul_le_mul_of_nonneg_right hf (norm_nonneg (typeISlabS0 x alpha d))
      simpa using hb
  · refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d _
    rw [norm_mul]
    have hμ : ‖(μ d : ℂ) * (1 / 2 : ℂ)‖ ≤ 1 / 2 := by
      rw [norm_mul, Complex.norm_intCast]
      have hhalf : ‖((1 : ℂ) / 2)‖ = 1 / 2 := by norm_num
      rw [hhalf]
      have hμabs : |((μ d : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast abs_moebius_le_one (n := d)
      refine le_trans (mul_le_mul_of_nonneg_right hμabs (by norm_num : (0 : ℝ) ≤ 1 / 2)) ?_
      norm_num
    have hb := mul_le_mul_of_nonneg_right hμ (norm_nonneg (typeISlabK x alpha V d))
    simpa using hb

/-- **Triangle assembly (budget form).** The outer slice decomposition bounds the smoothed
Vaughan sum by the per-`d` coefficient budgets plus half the transferred large-`w` block. -/
theorem norm_eta0VaughanTypeISum_le_slab_budget
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x) (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ‖eta0VaughanTypeISum x alpha U V‖ ≤
      (∑ d ∈ theorem51Divisors U V,
          (‖(if d ≤ ⌊U⌋₊ then (μ d : ℂ) else 0)‖ * ‖typeISlabS1 x alpha d‖
            + ‖(((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖ *
                ‖typeISlabS0 x alpha d‖))
        + (1 / 2) * ∑ d ∈ (theorem51Divisors U V).filter (fun d => ⌊U⌋₊ < d),
            ‖typeISlabK x alpha V d‖ := by
  rw [eta0VaughanTypeISum_eq_A_add_S3 x alpha U V hU hV hUx hVx hUVx hUV2]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · refine le_trans (norm_sum_le _ _) ?_
    apply Finset.sum_le_sum
    intro d _
    refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
    · exact le_of_eq (by rw [norm_mul])
    · exact le_of_eq (by rw [norm_mul])
  · refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d _
    rw [norm_mul]
    have hμ : ‖(μ d : ℂ) * (1 / 2 : ℂ)‖ ≤ 1 / 2 := by
      rw [norm_mul, Complex.norm_intCast]
      have hhalf : ‖((1 : ℂ) / 2)‖ = 1 / 2 := by norm_num
      rw [hhalf]
      have hμabs : |((μ d : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast abs_moebius_le_one (n := d)
      refine le_trans (mul_le_mul_of_nonneg_right hμabs (by norm_num : (0 : ℝ) ≤ 1 / 2)) ?_
      norm_num
    have hb := mul_le_mul_of_nonneg_right hμ (norm_nonneg (typeISlabK x alpha V d))
    simpa using hb

/-- **Conditional child3 reduction.** If the scalar gap `(★)` holds — the coefficient budget
plus half the transferred large-`w` block fits inside `Σ_d (‖S1_d‖ + log d ‖S0_d‖)` — and the
Type I identification `T_I(c) = Σ_d (‖S1_d‖ + log d ‖S0_d‖)` holds for the aligning coefficients
`c_d = align (S1_d) (S0_d)`, then child3 follows.  The first hypothesis is the open scalar
inequality; the second is the (mechanical) support/tsum transfer. -/
theorem child3_of_scalar_gap_and_TI_identification
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x) (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (hgap : (∑ d ∈ theorem51Divisors U V,
          (‖(if d ≤ ⌊U⌋₊ then (μ d : ℂ) else 0)‖ * ‖typeISlabS1 x alpha d‖
            + ‖(((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖ *
                ‖typeISlabS0 x alpha d‖))
        + (1 / 2) * ∑ d ∈ (theorem51Divisors U V).filter (fun d => ⌊U⌋₊ < d),
            ‖typeISlabK x alpha V d‖
      ≤ ∑ d ∈ theorem51Divisors U V,
          (‖typeISlabS1 x alpha d‖ + Real.log d * ‖typeISlabS0 x alpha d‖))
    (hTI : ∑ d ∈ theorem51Divisors U V,
          (‖typeISlabS1 x alpha d‖ + Real.log d * ‖typeISlabS0 x alpha d‖)
        = theorem51TypeI x alpha U V
            (fun d => if d ∈ theorem51Divisors U V then
              TaoV51.align (typeISlabS1 x alpha d) (typeISlabS0 x alpha d) else 1)) :
    ∃ c : ℕ → ℂ,
      (∀ d ∈ theorem51Divisors U V, ‖c d‖ ≤ 1) ∧
      ‖eta0VaughanTypeISum x alpha U V‖ ≤ theorem51TypeI x alpha U V c := by
  refine ⟨fun d => if d ∈ theorem51Divisors U V then
      TaoV51.align (typeISlabS1 x alpha d) (typeISlabS0 x alpha d) else 1, ?_, ?_⟩
  · intro d hd
    change ‖(if d ∈ theorem51Divisors U V then
      TaoV51.align (typeISlabS1 x alpha d) (typeISlabS0 x alpha d) else 1)‖ ≤ 1
    rw [if_pos hd]
    exact le_of_eq (TaoV51.norm_align _ _)
  · rw [← hTI]
    exact le_trans (norm_eta0VaughanTypeISum_le_slab_budget x alpha U V hU hV hUx hVx hUVx hUV2) hgap

/-- The platform Vaughan test is definitionally the split-file test. -/
theorem eta0VaughanTest_eq_FF (x alpha : ℝ) (n : ℕ) :
    eta0VaughanTest x alpha n = TaoV51.FF x alpha n := rfl

/-- **Support identification for `S1`.** For odd `d ≤ ⌊x⌋`, the slab sum over the full inner
support equals the `range (⌊x⌋+1)` sum with the `log m` weight. -/
theorem typeISlabS1_eq_range_sum
    (x alpha : ℝ) (hx : 0 < x) (d : ℕ) (hd0 : 0 < d) (hdx : d ≤ ⌊x⌋₊)
    (hdodd : d.Coprime 2) :
    typeISlabS1 x alpha d =
      ∑ m ∈ Finset.range (⌊x⌋₊ + 1),
        ((ArithmeticFunction.log m : ℝ) : ℂ) * TaoV51.FF x alpha (d * m) := by
  have hsupp := fullInnerSupport_eq_eta0TypeIInnerSupport x d hd0 hdx hdodd
  rw [typeISlabS1]
  simp_rw [eta0VaughanTest_eq_FF]
  refine Finset.sum_subset ?_ ?_
  · intro w hw
    rw [Finset.mem_range]
    have hspec := fullInnerSupport_spec hw
    have hwd : w ≤ d * w := by
      calc w = 1 * w := (one_mul w).symm
        _ ≤ d * w := Nat.mul_le_mul_right w (by omega : 1 ≤ d)
    omega
  · intro m hm hmn
    rw [Finset.mem_range] at hm
    by_cases hFF : TaoV51.FF x alpha (d * m) = 0
    · simp [hFF]
    · exfalso
      have hcop : (d * m).Coprime 2 := by
        by_contra hc
        exact hFF (TaoV51.FF_even hc)
      have heta : eta0 (((d * m : ℕ) : ℝ) / x) ≠ 0 := by
        intro h0
        apply hFF
        rw [TaoV51.FF, if_pos hcop, h0]
        simp
      have hy1 : ¬(((d * m : ℕ) : ℝ) / x ≤ 1 / 4) := fun h =>
        heta (eta0_eq_zero_of_le_one_fourth h)
      have hy2 : ¬(1 ≤ ((d * m : ℕ) : ℝ) / x) := fun h =>
        heta (eta0_eq_zero_of_one_le h)
      push Not at hy1 hy2
      have hlo : x / 4 < ((d * m : ℕ) : ℝ) := by
        have h := (lt_div_iff₀ hx).mp hy1
        linarith
      have hhi : ((d * m : ℕ) : ℝ) < x := (div_lt_one hx).mp hy2
      have hmodd : m.Coprime 2 := hcop.coprime_dvd_left (Nat.dvd_mul_left m d)
      have hmpos : 0 < m := by
        rw [Nat.pos_iff_ne_zero]
        intro hm0
        rw [hm0, Nat.coprime_zero_left] at hmodd
        omega
      have hprod : d * m ≤ ⌊x⌋₊ := Nat.le_floor hhi.le
      have hmlt : (m : ℝ) < x := by
        have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
        have hmle : (m : ℝ) ≤ (d : ℝ) * (m : ℝ) := by
          nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]
        have hcast : ((d * m : ℕ) : ℝ) = (d : ℝ) * (m : ℝ) := by push_cast; ring
        linarith [hhi, hmle, hcast]
      have hmem : m ∈ eta0TypeIInnerSupport x d := by
        rw [eta0TypeIInnerSupport, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨hmpos, Nat.le_floor hmlt.le⟩, hprod, hmodd, hlo, hhi⟩
      exact hmn (by rw [hsupp]; exact hmem)

/-- **Support identification for `S0`.** Same as `typeISlabS1_eq_range_sum` but with the
`ζ_R` weight (which is `1` on positive arguments). -/
theorem typeISlabS0_eq_range_sum
    (x alpha : ℝ) (hx : 0 < x) (d : ℕ) (hd0 : 0 < d) (hdx : d ≤ ⌊x⌋₊)
    (hdodd : d.Coprime 2) :
    typeISlabS0 x alpha d =
      ∑ m ∈ Finset.range (⌊x⌋₊ + 1),
        ((zetaR m : ℝ) : ℂ) * TaoV51.FF x alpha (d * m) := by
  have hsupp := fullInnerSupport_eq_eta0TypeIInnerSupport x d hd0 hdx hdodd
  have hzeta :
      (∑ m ∈ Finset.range (⌊x⌋₊ + 1),
          ((zetaR m : ℝ) : ℂ) * TaoV51.FF x alpha (d * m))
        = ∑ m ∈ Finset.range (⌊x⌋₊ + 1), TaoV51.FF x alpha (d * m) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    by_cases hm : m = 0
    · subst hm
      rw [show ((zetaR 0 : ℝ) : ℂ) = 0 from by simp [TaoFivePrimes.zetaR]]
      have hFF0 : TaoV51.FF x alpha (d * 0) = 0 := by
        rw [Nat.mul_zero]
        exact TaoV51.FF_even (by rw [Nat.coprime_zero_left]; norm_num)
      rw [hFF0, mul_zero]
    · rw [show ((zetaR m : ℝ) : ℂ) = 1 from by
        simp [TaoFivePrimes.zetaR, ArithmeticFunction.zeta_apply, hm]]
      simp
  rw [typeISlabS0, hzeta]
  simp_rw [eta0VaughanTest_eq_FF]
  refine Finset.sum_subset ?_ ?_
  · intro w hw
    rw [Finset.mem_range]
    have hspec := fullInnerSupport_spec hw
    have hwd : w ≤ d * w := by
      calc w = 1 * w := (one_mul w).symm
        _ ≤ d * w := Nat.mul_le_mul_right w (by omega : 1 ≤ d)
    omega
  · intro m hm hmn
    rw [Finset.mem_range] at hm
    by_cases hFF : TaoV51.FF x alpha (d * m) = 0
    · simp [hFF]
    · exfalso
      have hcop : (d * m).Coprime 2 := by
        by_contra hc
        exact hFF (TaoV51.FF_even hc)
      have heta : eta0 (((d * m : ℕ) : ℝ) / x) ≠ 0 := by
        intro h0
        apply hFF
        rw [TaoV51.FF, if_pos hcop, h0]
        simp
      have hy1 : ¬(((d * m : ℕ) : ℝ) / x ≤ 1 / 4) := fun h =>
        heta (eta0_eq_zero_of_le_one_fourth h)
      have hy2 : ¬(1 ≤ ((d * m : ℕ) : ℝ) / x) := fun h =>
        heta (eta0_eq_zero_of_one_le h)
      push Not at hy1 hy2
      have hlo : x / 4 < ((d * m : ℕ) : ℝ) := by
        have h := (lt_div_iff₀ hx).mp hy1
        linarith
      have hhi : ((d * m : ℕ) : ℝ) < x := (div_lt_one hx).mp hy2
      have hmodd : m.Coprime 2 := hcop.coprime_dvd_left (Nat.dvd_mul_left m d)
      have hmpos : 0 < m := by
        rw [Nat.pos_iff_ne_zero]
        intro hm0
        rw [hm0, Nat.coprime_zero_left] at hmodd
        omega
      have hprod : d * m ≤ ⌊x⌋₊ := Nat.le_floor hhi.le
      have hmlt : (m : ℝ) < x := by
        have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
        have hmle : (m : ℝ) ≤ (d : ℝ) * (m : ℝ) := by
          nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]
        have hcast : ((d * m : ℕ) : ℝ) = (d : ℝ) * (m : ℝ) := by push_cast; ring
        linarith [hhi, hmle, hcast]
      have hmem : m ∈ eta0TypeIInnerSupport x d := by
        rw [eta0TypeIInnerSupport, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨hmpos, Nat.le_floor hmlt.le⟩, hprod, hmodd, hlo, hhi⟩
      exact hmn (by rw [hsupp]; exact hmem)

/-- **Type I identification.** The platform `theorem51TypeI` with the aligning coefficients
`c_d = align (S1_d) (S0_d)` equals the sum of slab-slot lengths
`Σ_{d∈D} (‖S1_d‖ + log d · ‖S0_d‖)`.  Proof: `TaoV51.typeI_inner` converts the platform
`ℤ`-tsum into the split-file `range` sums, the support identifications replace those by the
slab sums, and `TaoV51.align_spec` evaluates each slot. -/
theorem sum_slab_eq_theorem51TypeI
    (x alpha U V : ℝ) (hU : 40 ≤ U) (_hV : 40 ≤ V)
    (_hUx : U < x) (_hVx : V < x) (hUVx : U * V ≤ x / 4) (_hUV2 : x ≤ U * V ^ 2) :
    (∑ d ∈ theorem51Divisors U V,
        (‖typeISlabS1 x alpha d‖ + Real.log d * ‖typeISlabS0 x alpha d‖))
      = theorem51TypeI x alpha U V
          (fun d => if d ∈ theorem51Divisors U V then
            TaoV51.align (typeISlabS1 x alpha d) (typeISlabS0 x alpha d) else 1) := by
  have hx : 0 < x := by linarith
  rw [theorem51TypeI]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdmem := (Finset.mem_filter.mp hd).1
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdmem).1
  have hd0 : 0 < d := hd1
  have hdodd : d.Coprime 2 := (Finset.mem_filter.mp hd).2
  have hdUV : d ≤ ⌊U * V⌋₊ := (Finset.mem_Icc.mp hdmem).2
  have hdx : d ≤ ⌊x⌋₊ := by
    have h1 : ⌊U * V⌋₊ ≤ ⌊x / 4⌋₊ := Nat.floor_mono hUVx
    have h2 : ⌊x / 4⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono (by linarith)
    omega
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd1)
  rw [if_pos hd]
  rw [← TaoV51.typeI_inner x alpha hx (⌊x⌋₊ + 1) (by push_cast; exact Nat.lt_floor_add_one x) d hd0 hdodd
    (TaoV51.align (typeISlabS1 x alpha d) (typeISlabS0 x alpha d))]
  rw [← typeISlabS1_eq_range_sum x alpha hx d hd0 hdx hdodd,
    ← typeISlabS0_eq_range_sum x alpha hx d hd0 hdx hdodd]
  exact TaoV51.align_spec (typeISlabS1 x alpha d) (typeISlabS0 x alpha d)
    (Real.log d) hlogd

/-- **Conditional child3 (scalar gap only).** Given the scalar gap `(★)`, child3 follows. -/
theorem child3_of_scalar_gap
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x) (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (hgap : (∑ d ∈ theorem51Divisors U V,
          (‖(if d ≤ ⌊U⌋₊ then (μ d : ℂ) else 0)‖ * ‖typeISlabS1 x alpha d‖
            + ‖(((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖ *
                ‖typeISlabS0 x alpha d‖))
        + (1 / 2) * ∑ d ∈ (theorem51Divisors U V).filter (fun d => ⌊U⌋₊ < d),
            ‖typeISlabK x alpha V d‖
      ≤ ∑ d ∈ theorem51Divisors U V,
          (‖typeISlabS1 x alpha d‖ + Real.log d * ‖typeISlabS0 x alpha d‖)) :
    ∃ c : ℕ → ℂ,
      (∀ d ∈ theorem51Divisors U V, ‖c d‖ ≤ 1) ∧
      ‖eta0VaughanTypeISum x alpha U V‖ ≤ theorem51TypeI x alpha U V c :=
  child3_of_scalar_gap_and_TI_identification x alpha U V hU hV hUx hVx hUVx hUV2 hgap
    (sum_slab_eq_theorem51TypeI x alpha U V hU hV hUx hVx hUVx hUV2)


/-- **Sharp assembly.** `‖η0VTS‖ ≤ A_bound + ‖S3'‖`, keeping the global `S3'` norm instead of
replacing it by `½ Σ ‖K_d‖`.  The triangle version (`norm_eta0VaughanTypeISum_le_slab_budget`)
is numerically too lossy: at `U = V = 40`, `x = 64000`, `α = 1/4` its left side is `1.226 × T_I`,
while the sharp left side here stays `≤ 0.62 × T_I` (and child3 itself holds at `≤ 0.12 × T_I`). -/
theorem norm_eta0VaughanTypeISum_le_sharp_budget
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x) (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ‖eta0VaughanTypeISum x alpha U V‖ ≤
      (∑ d ∈ theorem51Divisors U V,
          (‖(if d ≤ ⌊U⌋₊ then (μ d : ℂ) else 0)‖ * ‖typeISlabS1 x alpha d‖
            + ‖(((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖ *
                ‖typeISlabS0 x alpha d‖))
        + ‖typeISlabS3 x alpha U V‖ := by
  have hS3 : (∑ d ∈ (theorem51Divisors U V).filter (fun d => ⌊U⌋₊ < d),
        ((μ d : ℂ) * (1 / 2 : ℂ)) * typeISlabK x alpha V d)
      = typeISlabS3 x alpha U V := rfl
  rw [eta0VaughanTypeISum_eq_A_add_S3 x alpha U V hU hV hUx hVx hUVx hUV2, hS3]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · refine le_trans (norm_sum_le _ _) ?_
    apply Finset.sum_le_sum
    intro d _
    refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
    · exact le_of_eq (by rw [norm_mul])
    · exact le_of_eq (by rw [norm_mul])
  · exact le_rfl

/-- **Conditional child3 (sharp gap only).** Child3 follows from the sharp scalar gap keeping
`‖S3'‖` global.  This strictly strengthens `child3_of_scalar_gap`: its budget hypothesis implies
this one (`‖S3'‖ ≤ ½ Σ ‖K_d‖` by the triangle inequality), and is numerically false in general
(`U = V = 40`, `x = 64000`, `α = 1/4`), while the sharp gap holds with margin everywhere tested. -/
theorem child3_of_sharp_gap
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x) (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (hgap : (∑ d ∈ theorem51Divisors U V,
          (‖(if d ≤ ⌊U⌋₊ then (μ d : ℂ) else 0)‖ * ‖typeISlabS1 x alpha d‖
            + ‖(((vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖ *
                ‖typeISlabS0 x alpha d‖))
        + ‖typeISlabS3 x alpha U V‖
      ≤ ∑ d ∈ theorem51Divisors U V,
          (‖typeISlabS1 x alpha d‖ + Real.log d * ‖typeISlabS0 x alpha d‖)) :
    ∃ c : ℕ → ℂ,
      (∀ d ∈ theorem51Divisors U V, ‖c d‖ ≤ 1) ∧
      ‖eta0VaughanTypeISum x alpha U V‖ ≤ theorem51TypeI x alpha U V c := by
  refine ⟨fun d => if d ∈ theorem51Divisors U V then
      TaoV51.align (typeISlabS1 x alpha d) (typeISlabS0 x alpha d) else 1, ?_, ?_⟩
  · intro d hd
    change ‖(if d ∈ theorem51Divisors U V then
      TaoV51.align (typeISlabS1 x alpha d) (typeISlabS0 x alpha d) else 1)‖ ≤ 1
    rw [if_pos hd]
    exact le_of_eq (TaoV51.norm_align _ _)
  · rw [← sum_slab_eq_theorem51TypeI x alpha U V hU hV hUx hVx hUVx hUV2]
    exact le_trans (norm_eta0VaughanTypeISum_le_sharp_budget x alpha U V hU hV hUx hVx hUVx hUV2) hgap

end TaoFivePrimes


open TaoFivePrimes

/-- The Type I envelope comparison (child3), reduced to the sharp scalar transfer gap
`TaoFivePrimes.theorem51_sharp_transfer_gap`. -/
theorem solution
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ∃ c : ℕ → ℂ,
      (∀ d ∈ theorem51Divisors U V, ‖c d‖ ≤ 1) ∧
      ‖eta0VaughanTypeISum x alpha U V‖ ≤ theorem51TypeI x alpha U V c :=
  child3_of_sharp_gap x alpha U V hU hV hUx hVx hUVx hUV2
    (theorem51_sharp_transfer_gap x alpha U V hU hV hUx hVx hUVx hUV2)
