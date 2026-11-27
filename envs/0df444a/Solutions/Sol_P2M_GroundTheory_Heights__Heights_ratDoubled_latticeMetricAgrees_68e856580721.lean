-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ratDoubled_latticeMetricAgrees_68e856580721
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:11:46.572412+00:00
-- url     : https://prove2.me/submissions/75ede485-3b9a-4484-b7fb-a3f209c3f341

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_DualModel

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
open MvPolynomial NumberField Matrix
open scoped ComplexOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (r : ℕ) :
    LatticeMetricAgrees (fun j : Fin (r + 1) ↦ (Pi.single j (1 / 2 : ℚ) : Fin (r + 1) → ℚ))
      (ratDoubled r) ((HermLine.standard (fun _ : Unit ↦ r)).scale 2 two_pos) := by
  intro σ w _
  change 2 * ∏ _u : Unit, l2Norm (latticePoint _ σ w ()) =
    Real.sqrt (star w ⬝ᵥ ((1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) *ᵥ w)).re
  have h1 : latticePoint (fun j : Fin (r + 1) ↦ (Pi.single j (1 / 2 : ℚ) : Fin (r + 1) → ℚ)) σ w () =
      fun p ↦ (1 / 2 : ℂ) * w p := by
    funext p
    have h0 : σ (1 / 2) = 1 / 2 := by
      rw [eq_ratCast σ (1 / 2)]
      norm_num
    change ∑ j, σ ((Pi.single p (1 / 2 : ℚ) : Fin (r + 1) → ℚ) j) * w j = _
    rw [Finset.sum_eq_single p (fun j _ hj ↦ by simp [hj]) (by simp),
      Pi.single_eq_same, h0]
  rw [Fintype.prod_unique, h1, vectorL2Norm_const_mul, one_mulVec]
  have h2 : l2Norm w = Real.sqrt (star w ⬝ᵥ w).re := by
    rw [l2Norm]
    congr 1
    rw [dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
    norm_cast
  rw [← h2]
  simp
end GroundTheory.Heights₂.Heights
