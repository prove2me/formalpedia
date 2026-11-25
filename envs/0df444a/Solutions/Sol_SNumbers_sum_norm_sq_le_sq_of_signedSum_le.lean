-- Prove2me | solution 1 for SNumbers.sum_norm_sq_le_sq_of_signedSum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:11:55.057081+00:00
-- url     : https://prove2.me/submissions/b5803933-f45a-458c-9d57-977768b89175

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Theorems.Thm_SNumbers_sum_powerset_norm_signedSum_sq

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers
variable {ι : Type*} [DecidableEq ι]
namespace SNumbers
theorem _root_.solution (𝕜 : Type*) [RCLike 𝕜] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {w : ι → H} {J : Finset ι} {M : ℝ}
    (hM : ∀ S ⊆ J, ‖signedSum w S J‖ ≤ M) :
    ∑ j ∈ J, ‖w j‖ ^ 2 ≤ M ^ 2 := by
  have hpow : (0 : ℝ) < 2 ^ J.card := by positivity
  have hle : 2 ^ J.card * ∑ j ∈ J, ‖w j‖ ^ 2 ≤ 2 ^ J.card * M ^ 2 := by
    rw [← sum_powerset_norm_signedSum_sq 𝕜 w J]
    calc ∑ S ∈ J.powerset, ‖signedSum w S J‖ ^ 2
        ≤ ∑ _S ∈ J.powerset, M ^ 2 :=
          Finset.sum_le_sum fun S hS =>
            pow_le_pow_left₀ (norm_nonneg _) (hM S (Finset.mem_powerset.mp hS)) 2
      _ = 2 ^ J.card * M ^ 2 := by
          rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
          push_cast
          ring
  exact le_of_mul_le_mul_left hle hpow
end SNumbers
