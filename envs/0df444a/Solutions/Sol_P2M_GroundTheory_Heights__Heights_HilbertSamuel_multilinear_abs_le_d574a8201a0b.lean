-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_multilinear_abs_le_d574a8201a0b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:42.752267+00:00
-- url     : https://prove2.me/submissions/90bc6066-a849-4664-a7b8-34d867c94027

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K : Type*} [Fintype K] [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {n : ℕ} (f : MultilinearMap ℤ (fun _ : Fin n => K → ℤ) ℤ) :
    ∃ M : ℤ, 0 ≤ M ∧ ∀ m : Fin n → K → ℤ, |f m| ≤ M * ∏ i, ∑ k, |m i k| := by
  set E : K → K → ℤ := fun k j => if k = j then 1 else 0
  refine ⟨∑ r : Fin n → K, |f (fun i => E (r i))|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro m
  have hm : m = fun i => ∑ k, m i k • E k := by
    funext i
    exact pi_eq_sum_univ (m i)
  have hexp : f m = ∑ r : Fin n → K, (∏ i, m i (r i)) * f (fun i => E (r i)) := by
    conv_lhs => rw [hm]
    rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rw [hexp, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun r _ => ?_))
  rw [abs_mul, Finset.abs_prod]
  refine (mul_comm _ _).trans_le (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
  refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ?_)
  exact Finset.single_le_sum (f := fun k => |m i k|) (fun k _ => abs_nonneg _) (Finset.mem_univ _)
end GroundTheory.Heights₂.Heights.HilbertSamuel
