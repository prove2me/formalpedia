-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BoundedMonomials_chartNorm_scale_882ffc6428a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:17:26.922325+00:00
-- url     : https://prove2.me/submissions/dcf45259-bc9c-412a-961d-6c9b57f6681d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_scale_eb4d8d40fcab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.BoundedMonomials
namespace GroundTheory.Heights₂.Heights.BoundedMonomials
theorem _root_.solution (A : HermLine n) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ)
    {e : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (he : IsWeightedHomogeneous (coordDeg n) e δ)
    (hδ : ∀ k, (δ k : ℤ) = A.deg k + d k) {u : ι → ℂ} (hu : ∀ k, u k ≠ 0) {z : Cone n ℂ}
    (hz : BlockNonzero z) :
    chartNorm A c d e (fun k i ↦ u k * z k i) = chartNorm A c d e z := by
  unfold chartNorm
  rw [evalCone_scale u z he, evalCone_scale u z (isWeightedHomogeneous_chartMonomial c d),
    A.metric_smul u z hu hz, norm_mul, norm_mul, norm_prod, norm_prod]
  simp only [norm_pow]
  have hQ : ∏ k, ‖u k‖ ^ δ k = (∏ k, ‖u k‖ ^ d k) * ∏ k, ‖u k‖ ^ A.deg k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    have hk : ‖u k‖ ≠ 0 := norm_ne_zero_iff.mpr (hu k)
    rw [← zpow_natCast, ← zpow_natCast, hδ k, zpow_add₀ hk, mul_comm]
  have hD : (∏ k, ‖u k‖ ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (norm_ne_zero_iff.mpr (hu k))
  have hH : (∏ k, ‖u k‖ ^ A.deg k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (norm_ne_zero_iff.mpr (hu k))
  rw [hQ]
  have h : (∏ k, ‖u k‖ ^ d k) * ‖evalCone z (chartMonomial c d)‖ *
      ((∏ k, ‖u k‖ ^ A.deg k) * A.metric z) =
      ((∏ k, ‖u k‖ ^ d k) * ∏ k, ‖u k‖ ^ A.deg k) *
        (‖evalCone z (chartMonomial c d)‖ * A.metric z) := by ring
  rw [h, mul_div_mul_left _ _ (mul_ne_zero hD hH)]
end GroundTheory.Heights₂.Heights.BoundedMonomials
