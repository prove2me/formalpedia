-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_prod_pow_blockWeight_69a38f0cbb39
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:16:15.5278+00:00
-- url     : https://prove2.me/submissions/df82039d-c56c-4ba0-ac0d-e8a323a0d5c3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartDehomog
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {M : Type*}
    [CommMonoid M] (w : K → M) (e : (Σ k, ι k) →₀ ℕ) :
    ∏ k, w k ^ (Finsupp.weight (blockWeight ι) e k) = e.prod fun v n => w v.1 ^ n := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, ← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm, Finsupp.prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finset.prod_eq_single v.1]
  · simp [blockWeight]
  · intro k _ hk
    simp [blockWeight, Pi.single_eq_of_ne hk]
  · simp
end GroundTheory.Heights₂.Heights.FieldNumbers
