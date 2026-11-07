-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.jacobiTripleProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:42:31.158688+00:00
-- url     : https://prove2.me/submissions/4371417c-96b2-4a38-b661-42d4e9e8ec43

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_euler_second_identity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammerInf_X_mul_qPochhammerInf_neg
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_hasSum_pow_choose_two_nonneg
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_hasSum_pow_choose_two_neg
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_Nat_lt_choose_two_of_add_two_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_succ_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_right
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_succ_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_right
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_succ
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qPochhammer_zero


section
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
section Euler2
end Euler2
section KeyIdentity
end KeyIdentity
section Cauchy
end Cauchy
section JTP
private theorem jacobiProd_eq_tsum_mul_tsum :
    @jacobiProd = (∑' n : ℕ, X ^ n.choose 2 * laurentZ ^ n * qPochhammerInf (X * X ^ n)) *
              (∑' m : ℕ, X ^ (m.choose 2 + m) * laurentZInv ^ m * qPochhammerInv m) := by
  convert congr_arg₂ (· * ·) (qPochhammerInf_X_mul_qPochhammerInf_neg laurentZ) _ using 1
  all_goals try rfl
  convert euler_second_identity (X * laurentZInv) using 1
  · exact tprod_congr fun _ => by ring
  · simp +decide [pow_add, mul_pow, mul_assoc, mul_comm, mul_left_comm]
open LaurentPolynomial in
/-- `z * zinv = 1` in `A⟦X⟧`. -/
private theorem laurentZ_mul_laurentZInv : laurentZ * laurentZInv = 1 := by
  rw [← map_mul, ← T_add]
  simp
open LaurentPolynomial in
/-- `z ^ n * zinv ^ n = 1` for all `n`. -/
private theorem laurentZ_pow_mul_laurentZInv_pow (n : ℕ) : laurentZ ^ n * laurentZInv ^ n = 1 := by
  rw [← mul_pow, laurentZ_mul_laurentZInv, one_pow]
open LaurentPolynomial in
/-- `z ^ n = PS (T n)` for natural `n`. -/
private theorem laurentZ_pow (n : ℕ) :
    laurentZ ^ n = (PowerSeries.C : LaurentPolynomial ℚ →+* _) (T (n : ℤ)) := by
  rw [← map_pow]
  congr 1
  simp
open LaurentPolynomial in
/-- `zinv ^ (m + 1) = PS (T (-(↑m + 1)))`. -/
private theorem laurentZInv_pow (m : ℕ) :
    laurentZInv ^ (m + 1) = (PowerSeries.C : LaurentPolynomial ℚ →+* _) (T (-(↑m + 1))) := by
  rw [← map_pow]
  congr 1
  rw [T_pow]
  push_cast
  ring_nf
open LaurentPolynomial in
/-- Cancelling `zinv ^ m` against the first `m` factors of `z ^ (m + k)`. -/
private theorem laurentZ_pow_add_mul_laurentZInv_pow (m k : ℕ) :
    laurentZ ^ (m + k) * laurentZInv ^ m = laurentZ ^ k := by
  rw [pow_add, mul_right_comm, laurentZ_pow_mul_laurentZInv_pow, one_mul]
open LaurentPolynomial in
/-- Cancelling `z ^ n` against the first `n` factors of `zinv ^ (n + l)`. -/
private theorem laurentZInv_pow_add_mul_laurentZ_pow (n l : ℕ) :
    laurentZInv ^ (n + l) * laurentZ ^ n = laurentZInv ^ l := by
  rw [pow_add, mul_right_comm, mul_comm (laurentZInv ^ n) (laurentZ ^ n),
    laurentZ_pow_mul_laurentZInv_pow, one_mul]
open LaurentPolynomial in
/-- Non-negative diagonal of the Cauchy product: HasSum giving `z^k * X^{C(k,2)}`. -/
private theorem hasSum_diagonal_nonneg (k : ℕ) :
    HasSum (fun m : ℕ =>
      (X ^ (m + k).choose 2 * laurentZ ^ (m + k) * qPochhammerInf (X * X ^ (m + k))) *
      (X ^ (m.choose 2 + m) * laurentZInv ^ m * qPochhammerInv m))
      (laurentZ ^ k * X ^ k.choose 2) := by
  have key : ∀ m : ℕ,
      (X ^ (m + k).choose 2 * laurentZ ^ (m + k) * qPochhammerInf (X * X ^ (m + k))) *
      (X ^ (m.choose 2 + m) * laurentZInv ^ m * qPochhammerInv (R := LaurentPolynomial ℚ) m) =
      laurentZ ^ k * (X ^ (m + k).choose 2 * qPochhammerInf (X * X ^ (m + k)) *
      (X ^ m.choose 2 * X ^ m * qPochhammerInv m)) := fun m => by
    rw [← laurentZ_pow_add_mul_laurentZInv_pow m k]
    ring
  simp_rw [key]
  exact HasSum.mul_left _ (hasSum_pow_choose_two_nonneg k)
open LaurentPolynomial in
/-- Negative diagonal of the Cauchy product: HasSum giving `zinv^{l+1} * X^{C(l+2,2)}`. -/
private theorem hasSum_diagonal_neg (l : ℕ) :
    HasSum (fun n : ℕ =>
      (X ^ n.choose 2 * laurentZ ^ n * qPochhammerInf (X * X ^ n)) *
      (X ^ ((n + (l + 1)).choose 2 + (n + (l + 1))) * laurentZInv ^ (n + (l + 1)) *
      qPochhammerInv (n + (l + 1))))
      (laurentZInv ^ (l + 1) * X ^ (l + 2).choose 2) := by
  have key : ∀ n : ℕ, (X ^ n.choose 2 * laurentZ ^ n * qPochhammerInf (X * X ^ n)) *
      (X ^ ((n + (l + 1)).choose 2 + (n + (l + 1))) * laurentZInv ^ (n + (l + 1)) *
      qPochhammerInv (R := LaurentPolynomial ℚ) (n + (l + 1))) =
      laurentZInv ^ (l + 1) * (X ^ n.choose 2 * qPochhammerInf (X * X ^ n) *
      (X ^ (n + (l + 1)).choose 2 * X ^ (n + (l + 1)) *
        qPochhammerInv (n + (l + 1)))) := fun n => by
    rw [← laurentZInv_pow_add_mul_laurentZ_pow n (l + 1)]
    ring
  simp_rw [key]
  exact HasSum.mul_left _ (hasSum_pow_choose_two_neg l)
open LaurentPolynomial in
/-- `leftSummand n` is divisible by `X ^ C(n, 2)`, so its lower coefficients vanish. -/
private theorem coeff_leftSummand_eq_zero {d n : ℕ} (h : d < n.choose 2) :
    PowerSeries.coeff d (leftSummand n) = 0 := by
  have hrw : leftSummand n = X ^ n.choose 2 * (laurentZ ^ n * qPochhammerInf (X * X ^ n)) := by
    unfold leftSummand; ring
  rw [hrw, PowerSeries.coeff_X_pow_mul', if_neg h.not_ge]
open LaurentPolynomial in
/-- `rightSummand m` is divisible by `X ^ (C(m, 2) + m)`, so its lower coefficients vanish. -/
private theorem coeff_rightSummand_eq_zero {d m : ℕ} (h : d < m.choose 2 + m) :
    PowerSeries.coeff d (rightSummand m) = 0 := by
  have hrw : rightSummand m = X ^ (m.choose 2 + m) * (laurentZInv ^ m * qPochhammerInv m) := by
    unfold rightSummand; ring
  rw [hrw, PowerSeries.coeff_X_pow_mul', if_neg h.not_ge]
open LaurentPolynomial in
/-- `leftSummand i * rightSummand j` is divisible by `X ^ (C(i, 2) + (C(j, 2) + j))`. -/
private theorem coeff_leftSummand_mul_rightSummand_eq_zero {d i j : ℕ}
    (h : d < i.choose 2 + (j.choose 2 + j)) :
    PowerSeries.coeff d (leftSummand i * rightSummand j) = 0 := by
  have hrw : leftSummand i * rightSummand j = X ^ (i.choose 2 + (j.choose 2 + j)) *
      (laurentZ ^ i * qPochhammerInf (X * X ^ i) * (laurentZInv ^ j * qPochhammerInv j)) := by
    unfold leftSummand rightSummand; ring
  rw [hrw, PowerSeries.coeff_X_pow_mul', if_neg h.not_ge]
open LaurentPolynomial in
/-- The leftSummand sequence is summable. -/
private theorem summable_leftSummand : Summable leftSummand := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff (LaurentPolynomial ℚ)).mpr
    fun d => summable_of_ne_finset_zero (s := Finset.range (d + 2)) fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  exact coeff_leftSummand_eq_zero (Nat.lt_choose_two_of_add_two_le hn)
open LaurentPolynomial in
/-- The rightSummand sequence is summable. -/
private theorem summable_rightSummand : Summable rightSummand := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff (LaurentPolynomial ℚ)).mpr
    fun d => summable_of_ne_finset_zero (s := Finset.range (d + 1)) fun m hm => ?_
  rw [Finset.mem_range, not_lt] at hm
  exact coeff_rightSummand_eq_zero (by omega)
open LaurentPolynomial in
/-- The double product sequence is summable. -/
private theorem summable_leftSummand_mul_rightSummand :
    Summable (fun p : ℕ × ℕ => leftSummand p.1 * rightSummand p.2) := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff (LaurentPolynomial ℚ)).mpr
    fun d => summable_of_ne_finset_zero
      (s := Finset.range (d + 2) ×ˢ Finset.range (d + 1)) fun p hp => ?_
  simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hp
  refine coeff_leftSummand_mul_rightSummand_eq_zero ?_
  rcases hp with h | h
  · have := Nat.lt_choose_two_of_add_two_le h
    omega
  · omega
open LaurentPolynomial in
/-- HasSum for the double product giving jacobiProd. -/
private theorem hasSum_leftSummand_mul_rightSummand_jacobiProd :
    HasSum (fun p : ℕ × ℕ => leftSummand p.1 * rightSummand p.2) jacobiProd := by
  have h : jacobiProd = ∑' p : ℕ × ℕ, leftSummand p.1 * rightSummand p.2 := by
    rw [jacobiProd_eq_tsum_mul_tsum]
    exact summable_leftSummand.hasSum.mul_eq summable_rightSummand.hasSum
      summable_leftSummand_mul_rightSummand.hasSum
  rw [h]
  exact summable_leftSummand_mul_rightSummand.hasSum
open LaurentPolynomial in
/-- Summability of the non-negative diagonal rearrangement. -/
private theorem summable_diagonal_nonneg :
    Summable (fun p : ℕ × ℕ => leftSummand (p.2 + p.1) * rightSummand p.2) := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff (LaurentPolynomial ℚ)).mpr
    fun d => summable_of_ne_finset_zero
      (s := Finset.range (d + 2) ×ˢ Finset.range (d + 2)) fun p hp => ?_
  simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hp
  refine coeff_leftSummand_mul_rightSummand_eq_zero ?_
  rcases hp with h | h
  · have := Nat.lt_choose_two_of_add_two_le (show d + 2 ≤ p.2 + p.1 by omega)
    omega
  · omega
open LaurentPolynomial in
/-- Summability of the negative diagonal rearrangement. -/
private theorem summable_diagonal_neg :
    Summable (fun p : ℕ × ℕ => leftSummand p.2 * rightSummand (p.2 + p.1 + 1)) := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff (LaurentPolynomial ℚ)).mpr
    fun d => summable_of_ne_finset_zero
      (s := Finset.range (d + 1) ×ˢ Finset.range (d + 1)) fun p hp => ?_
  simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hp
  refine coeff_leftSummand_mul_rightSummand_eq_zero ?_
  rcases hp with h | h <;> omega
open LaurentPolynomial in
/-- Splitting a `HasSum` over `ℕ × ℕ` into the diagonals `(m + k, m)` and `(n, n + l + 1)`. -/
private theorem hasSum_split_diagonal (f : ℕ × ℕ → (LaurentPolynomial ℚ)⟦X⟧)
    {a b : (LaurentPolynomial ℚ)⟦X⟧}
    (h1 : HasSum (fun p : ℕ × ℕ => f (p.2 + p.1, p.2)) a)
    (h2 : HasSum (fun p : ℕ × ℕ => f (p.2, p.2 + p.1 + 1)) b) :
    HasSum f (a + b) :=
  diagonalEquiv.symm.hasSum_iff.mp (h1.sum h2)
open LaurentPolynomial in
/-- A family indexed by `ℕ × ℕ` sums to the sum of its row sums. -/
private theorem hasSum_of_hasSum_fiberwise {f : ℕ × ℕ → (LaurentPolynomial ℚ)⟦X⟧}
    {g : ℕ → (LaurentPolynomial ℚ)⟦X⟧} (hf : Summable f)
    (hrow : ∀ k : ℕ, HasSum (fun m : ℕ => f (k, m)) (g k)) :
    HasSum f (∑' k : ℕ, g k) := by
  rw [(hf.hasSum.prod_fiberwise hrow).tsum_eq]
  exact hf.hasSum
open LaurentPolynomial in
/-- HasSum for the non-negative diagonal (combined over all k). -/
private theorem hasSum_diagonal_nonneg_part :
    HasSum (fun p : ℕ × ℕ => leftSummand (p.2 + p.1) * rightSummand p.2)
      (∑' k : ℕ, laurentZ ^ k * X ^ k.choose 2) :=
  hasSum_of_hasSum_fiberwise summable_diagonal_nonneg hasSum_diagonal_nonneg
open LaurentPolynomial in
/-- HasSum for the negative diagonal (combined over all l). -/
private theorem hasSum_diagonal_neg_part :
    HasSum (fun p : ℕ × ℕ => leftSummand p.2 * rightSummand (p.2 + p.1 + 1))
      (∑' l : ℕ, laurentZInv ^ (l + 1) * X ^ (l + 2).choose 2) :=
  hasSum_of_hasSum_fiberwise summable_diagonal_neg hasSum_diagonal_neg
open LaurentPolynomial in
/-- HasSum for the double product giving jacobiBilateral. -/
private theorem hasSum_leftSummand_mul_rightSummand_jacobiBilateral :
    HasSum (fun p : ℕ × ℕ => leftSummand p.1 * rightSummand p.2) jacobiBilateral := by
  have h : jacobiBilateral = (∑' k : ℕ, laurentZ ^ k * X ^ k.choose 2) +
      ∑' l : ℕ, laurentZInv ^ (l + 1) * X ^ (l + 2).choose 2 := by
    unfold jacobiBilateral
    congr 1
    · exact tsum_congr fun n => by rw [laurentZ_pow]
    · exact tsum_congr fun m => by rw [laurentZInv_pow]
  rw [h]
  exact hasSum_split_diagonal _ hasSum_diagonal_nonneg_part hasSum_diagonal_neg_part
end JTP
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
end
end

set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
open LaurentPolynomial
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
theorem _root_.solution : @jacobiProd = @jacobiBilateral :=
  hasSum_leftSummand_mul_rightSummand_jacobiProd.unique
    hasSum_leftSummand_mul_rightSummand_jacobiBilateral
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
