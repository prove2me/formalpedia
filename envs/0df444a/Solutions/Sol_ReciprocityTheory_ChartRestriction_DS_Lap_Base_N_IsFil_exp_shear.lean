-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.IsFil.exp_shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:17:22.466547+00:00
-- url     : https://prove2.me/submissions/c6d41b8f-ae60-4814-813d-69fcc676e1a6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsFil_pow_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsFil_pow_sub_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsFil_exp_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable {F : ℕ → Submodule ℝ A} {L : ℕ} {f g : A → A}
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
namespace IsFil
theorem _root_.solution (hF : IsFil F L) : IsShear F (fun x => NormedSpace.exp x - 1) := by
  have hS : ∀ x ∈ F 0, NormedSpace.exp x - 1 =
      x + ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2) := by
    intro x hx
    rw [hF.exp_eq hx]
    abel
  refine ⟨fun x hx => ?_, fun j x hx y hy hxy => ?_⟩
  · show NormedSpace.exp x - 1 ∈ F 0
    rw [hS x hx]
    refine (F 0).add_mem hx (sum_mem fun k _ => (F 0).smul_mem _ ?_)
    exact hF.anti 0 (k + 1) (Nat.zero_le _) (hF.pow_mem hx (k + 1))
  · show NormedSpace.exp x - 1 - (NormedSpace.exp y - 1) - (x - y) ∈ F (j + 1)
    rw [hS x hx, hS y hy]
    have e : x + ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2) -
        (y + ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • y ^ (k + 2)) - (x - y) =
        ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • (x ^ (k + 2) - y ^ (k + 2)) := by
      simp only [smul_sub, Finset.sum_sub_distrib]
      abel
    rw [e]
    refine sum_mem fun k _ => (F (j + 1)).smul_mem _ ?_
    exact hF.anti (j + 1) (j + (k + 1)) (by omega) (hF.pow_sub_mem hx hy hxy (k + 1))
end IsFil
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
