-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartHessianComparison_norm_sub_proj_le_4cf1acb274c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:43.693282+00:00
-- url     : https://prove2.me/submissions/1bbbfa2f-a019-47b7-86d9-f3bd7b35963e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare

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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder InnerProductSpace
noncomputable section
open GroundTheory.Heights₂.Heights.ChartHessianComparison
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartHessianComparison
theorem _root_.solution (u D : F) (hu : u ≠ 0) (s : ℂ) :
    ‖D - (⟪u, D⟫_ℂ / ⟪u, u⟫_ℂ) • u‖ ^ 2 ≤ ‖D - s • u‖ ^ 2 := by
  have hN0 : ⟪u, u⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hu
  have hNr : (starRingEnd ℂ) ⟪u, u⟫_ℂ = ⟪u, u⟫_ℂ := inner_conj_symm u u
  have hq : ⟪D, u⟫_ℂ = (starRingEnd ℂ) ⟪u, D⟫_ℂ := (inner_conj_symm D u).symm
  set t := ⟪u, D⟫_ℂ / ⟪u, u⟫_ℂ with ht
  have horth : ⟪D - t • u, (t - s) • u⟫_ℂ = 0 := by
    simp only [inner_smul_right, inner_sub_left, inner_smul_left, ht, map_div₀, hNr, hq]
    field_simp
    ring
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  have hsum : D - t • u + (t - s) • u = D - s • u := by
    rw [sub_smul]; abel
  rw [hsum] at h
  nlinarith [mul_self_nonneg ‖(t - s) • u‖]
end GroundTheory.Heights₂.Heights.ChartHessianComparison
