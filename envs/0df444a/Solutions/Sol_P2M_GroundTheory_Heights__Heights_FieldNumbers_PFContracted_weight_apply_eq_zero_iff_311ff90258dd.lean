-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_weight_apply_eq_zero_iff_311ff90258dd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:23:51.775618+00:00
-- url     : https://prove2.me/submissions/d1fc1d79-c7d8-4d5b-a6ae-11d95ad9e336

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim

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
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
theorem _root_.solution (d : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) d k = 0 ↔ ∀ v ∈ d.support, v.1 ≠ k := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finset.sum_eq_zero_iff]
  refine forall₂_congr fun v hv => ?_
  simp only [Pi.smul_apply, smul_eq_mul, blockWeight, Pi.single_apply, mul_ite, mul_one, mul_zero]
  have := Finsupp.mem_support_iff.mp hv
  constructor
  · intro h hk
    rw [if_pos hk.symm] at h
    exact this h
  · intro h
    rw [if_neg (fun hk => h hk.symm)]
end GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
