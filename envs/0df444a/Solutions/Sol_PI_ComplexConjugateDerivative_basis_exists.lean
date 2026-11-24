-- Prove2me | solution 1 for PI.ComplexConjugateDerivative.basis_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:42:32.637805+00:00
-- url     : https://prove2.me/submissions/e8bdc531-9a49-4e00-8bc9-16c09c185b19

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_SmoothClassInFiniteOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.ComplexConjugateDerivative
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PI.ComplexConjugateDerivative
theorem _root_.solution (k r : ℕ) : ∃ (N : ℕ) (e : Fin N → B.Mat k r) (c : Fin N → B.Mat k r → ℝ) (K : ℝ),
    0 ≤ K ∧ (∀ i, B.unitLie k r (e i)) ∧ (∀ X, B.inLie k r X → X = ∑ i, c i X • e i) ∧
    (∀ X, B.unitLie k r X → ∀ i, |c i X| ≤ K) := by
  classical
  have : FiniteDimensional ℝ (B.Mat k r) :=
    inferInstanceAs (FiniteDimensional ℝ (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  let bs := Module.finBasis ℝ (lieSub k r)
  let N := Module.finrank ℝ (lieSub k r)
  let s : Fin N → ℝ := fun i => max 1 ‖((bs i : lieSub k r) : B.Mat k r)‖
  have hs1 : ∀ i, 1 ≤ s i := fun i => le_max_left _ _
  have hs0 : ∀ i, 0 < s i := fun i => lt_of_lt_of_le one_pos (hs1 i)
  have hb : ∀ i : Fin N, ∃ C, 0 < C ∧ ∀ x : lieSub k r, ‖bs.coord i x‖ ≤ C * ‖x‖ :=
    fun i => (LinearMap.toContinuousLinearMap (bs.coord i)).bound
  choose C hC0 hC using hb
  let K : ℝ := ∑ i, C i * s i
  refine ⟨N, fun i => (s i)⁻¹ • ((bs i : lieSub k r) : B.Mat k r),
    fun i X => if h : B.inLie k r X then bs.repr ⟨X, h⟩ i * s i else 0, K, ?_, ?_, ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hC0 i).le (hs0 i).le
  · intro i
    refine ⟨(lieSub k r).smul_mem (s i)⁻¹ (bs i).2, fun p q => ?_⟩
    show ‖((s i)⁻¹ • ((bs i : lieSub k r) : B.Mat k r)) p q‖ ≤ 1
    rw [Matrix.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hs0 i)),
      inv_mul_le_iff₀ (hs0 i), mul_one]
    exact le_trans (Matrix.norm_entry_le_entrywise_sup_norm _) (le_max_right _ _)
  · intro X hX
    have h1 := congrArg Subtype.val (bs.sum_repr ⟨X, hX⟩)
    rw [Submodule.coe_sum] at h1
    simp only [Submodule.coe_smul] at h1
    conv_lhs => rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    show _ = (if h : B.inLie k r X then bs.repr ⟨X, h⟩ i * s i else 0) • ((s i)⁻¹ • ((bs i : lieSub k r) : B.Mat k r))
    rw [dif_pos hX, smul_smul, mul_assoc, mul_inv_cancel₀ (hs0 i).ne', mul_one]
  · intro X hX i
    show |(if h : B.inLie k r X then bs.repr ⟨X, h⟩ i * s i else 0)| ≤ K
    rw [dif_pos hX.1, abs_mul, abs_of_pos (hs0 i)]
    have hXn : ‖(⟨X, hX.1⟩ : lieSub k r)‖ ≤ 1 := by
      show ‖X‖ ≤ 1
      exact (Matrix.norm_le_iff zero_le_one).2 hX.2
    have hrep : |bs.repr ⟨X, hX.1⟩ i| ≤ C i := by
      rw [← Module.Basis.coord_apply, ← Real.norm_eq_abs]
      calc ‖bs.coord i ⟨X, hX.1⟩‖ ≤ C i * ‖(⟨X, hX.1⟩ : lieSub k r)‖ := hC i _
        _ ≤ C i * 1 := mul_le_mul_of_nonneg_left hXn (hC0 i).le
        _ = C i := mul_one _
    calc |bs.repr ⟨X, hX.1⟩ i| * s i ≤ C i * s i := mul_le_mul_of_nonneg_right hrep (hs0 i).le
      _ ≤ K := Finset.single_le_sum (f := fun j => C j * s j)
          (fun j _ => mul_nonneg (hC0 j).le (hs0 j).le) (Finset.mem_univ i)
end PI.ComplexConjugateDerivative
