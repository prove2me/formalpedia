-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.shiftedTheta_half_eq_quarterShiftScale_mul_tsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:55:50.416026+00:00
-- url     : https://prove2.me/submissions/4678afc5-36ee-4799-a9bd-5d815a5036ac

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_shiftedTheta_summable

section
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
private theorem exp_neg_log_nat_eq_inv_pow {p m : ℕ} (hp : 1 ≤ p) :
    Real.exp (-Real.log (p : ℝ) * (m : ℝ)) = (p : ℝ)⁻¹ ^ m := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  rw [show -Real.log (p : ℝ) * (m : ℝ) =
      (m : ℕ) * (-Real.log (p : ℝ)) by norm_num; ring]
  rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log hpR]
end SharpIntermediateSubgroupBounds
end

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) :
    shiftedTheta (p : ℝ) (1 / 2) = quarterShiftScale (p : ℝ) *
      (2 * ∑' j : ℕ, (p : ℝ)⁻¹ ^ (j * (j + 1))) := by
  let F : ℤ → ℝ := fun z ↦
    Real.exp (-Real.log (p : ℝ) * ((z : ℝ) - (1 / 2 : ℝ)) ^ 2)
  let e : ℤ ≃ ℕ ⊕ ℕ := (Equiv.neg ℤ).trans Equiv.intEquivNatSumNat
  have hF : Summable F := by
    simpa only [F] using shiftedTheta_summable
      (p := (p : ℝ)) (x := (1 / 2 : ℝ)) (by exact_mod_cast (by omega : 1 < p))
  have hleft : Summable (fun j : ℕ ↦ F (e.symm (Sum.inl j))) := by
    change Summable (F ∘ (fun j : ℕ ↦ e.symm (Sum.inl j)))
    exact hF.comp_injective (e.symm.injective.comp Sum.inl_injective)
  have hright : Summable (fun j : ℕ ↦ F (e.symm (Sum.inr j))) := by
    change Summable (F ∘ (fun j : ℕ ↦ e.symm (Sum.inr j)))
    exact hF.comp_injective (e.symm.injective.comp Sum.inr_injective)
  have hsplit :
      (∑' s : ℕ ⊕ ℕ, F (e.symm s)) =
        (∑' j : ℕ, F (e.symm (Sum.inl j))) +
          ∑' j : ℕ, F (e.symm (Sum.inr j)) :=
    (hleft.hasSum.sum hright.hasSum).tsum_eq
  have hleftterm (j : ℕ) :
      F (e.symm (Sum.inl j)) =
        quarterShiftScale (p : ℝ) * (p : ℝ)⁻¹ ^ (j * (j + 1)) := by
    have he : e.symm (Sum.inl j) = -(j : ℤ) := rfl
    rw [he]
    dsimp only [F]
    rw [Int.cast_neg, Int.cast_natCast]
    rw [← exp_neg_log_nat_eq_inv_pow (p := p) (m := j * (j + 1)) (by omega)]
    rw [quarterShiftScale, ← Real.exp_add]
    congr 1
    norm_num
    ring
  have hrightterm (j : ℕ) :
      F (e.symm (Sum.inr j)) =
        quarterShiftScale (p : ℝ) * (p : ℝ)⁻¹ ^ (j * (j + 1)) := by
    have he : e.symm (Sum.inr j) = ((j + 1 : ℕ) : ℤ) := rfl
    rw [he]
    dsimp only [F]
    rw [Int.cast_natCast, Nat.cast_add, Nat.cast_one]
    rw [← exp_neg_log_nat_eq_inv_pow (p := p) (m := j * (j + 1)) (by omega)]
    rw [quarterShiftScale, ← Real.exp_add]
    congr 1
    norm_num
    ring
  unfold shiftedTheta
  change (∑' z : ℤ, F z) = _
  rw [← e.symm.tsum_eq F, hsplit]
  simp_rw [hleftterm, hrightterm]
  rw [tsum_mul_left]
  ring
end SharpIntermediateSubgroupBounds
