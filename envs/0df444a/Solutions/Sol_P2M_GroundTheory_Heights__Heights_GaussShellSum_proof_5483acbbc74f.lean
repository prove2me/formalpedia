-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussShellSum_proof_5483acbbc74f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:04.993885+00:00
-- url     : https://prove2.me/submissions/31916f09-b259-4856-b17b-5ce9d94c05a5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussShellSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussShellSum_inv_one_sub_exp_neg_one_le_two_90229429a320
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussShellSum_exp_neg_nat_4b21dec2f2be

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
open Real
noncomputable section
open PGaussShellSum
namespace GroundTheory.Heights₂.Heights
namespace GaussShellSum
theorem _root_.solution (hS : GaussShell.Statement) : GaussShellSum.Statement := by
  intro n hn Λ δ hδ hmin
  set K : ℝ := gaussShellConst n * (1 + 1 / δ) ^ n with hK
  let f : Λ → ℝ := fun μ => Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2)
  have hf : 0 ≤ f := fun μ => (Real.exp_pos _).le
  have hK0 : 0 ≤ K := by
    have hc : 0 ≤ gaussShellConst n := by unfold gaussShellConst; positivity
    have : 0 ≤ 1 + 1 / δ := by positivity
    positivity
  have hr0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hr1 : Real.exp (-1) < 1 := by
    exact Real.exp_lt_one_iff.2 (by norm_num)
  have hgeo : Summable fun j : ℕ => K * Real.exp (-1) ^ j :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left K
  have hbound : ∀ u : Finset Λ, ∑ μ ∈ u, f μ ≤ 2 * gaussShellConst n * (1 + 1 / δ) ^ n := by
    intro u
    let fl : Λ → ℕ := fun μ => ⌊‖(μ : EuclideanSpace ℝ (Fin n))‖⌋₊
    rw [← Finset.sum_fiberwise_of_maps_to (g := fl) (t := u.image fl)
      (fun μ hμ => Finset.mem_image_of_mem fl hμ) f]
    calc ∑ j ∈ u.image fl, ∑ μ ∈ u with fl μ = j, f μ
        ≤ ∑ j ∈ u.image fl, K * Real.exp (-1) ^ j := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← exp_neg_nat]
          exact hS n hn Λ δ hδ hmin u j
      _ ≤ ∑' j : ℕ, K * Real.exp (-1) ^ j :=
          hgeo.sum_le_tsum _ (fun j _ => by positivity)
      _ = K * (1 - Real.exp (-1))⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
      _ ≤ K * 2 := mul_le_mul_of_nonneg_left inv_one_sub_exp_neg_one_le_two hK0
      _ = 2 * gaussShellConst n * (1 + 1 / δ) ^ n := by rw [hK]; ring
  exact ⟨summable_of_sum_le hf hbound, Real.tsum_le_of_sum_le hf hbound⟩
end GaussShellSum
end GroundTheory.Heights₂.Heights
