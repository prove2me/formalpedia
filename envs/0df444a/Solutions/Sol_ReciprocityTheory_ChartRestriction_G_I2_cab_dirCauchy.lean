-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.cab_dirCauchy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:32:25.25472+00:00
-- url     : https://prove2.me/submissions/da94bf0d-6ed7-4ba3-8cc5-619ad1ac807b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_contDiff_of_differentiable_fd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_iter_step_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (F : V → ℂ) (hF : Differentiable ℂ F) (c : ℕ) (x : Fin c → V) (hx : ∀ k, ‖x k‖ ≤ 1)
    (ρ M : ℝ) (hρ : 0 < ρ) (hM : ∀ v, ‖v‖ ≤ c * ρ → ‖F v‖ ≤ M) :
    ‖iteratedFDeriv ℂ c F 0 x‖ ≤ M / ρ ^ c := by
  let T : (Fin c → ℂ) →L[ℂ] V := ∑ k, (ContinuousLinearMap.proj k).smulRight (x k)
  have hT : ∀ z, T z = ∑ k, z k • x k := by
    intro z; simp [T]
  have hG : Differentiable ℂ (F ∘ T) := hF.comp T.differentiable
  have h1 := iter_step_bound (F ∘ T) hG ρ M hρ c id 0 (by
    intro y hy
    simp only [Pi.zero_apply, sub_zero] at hy
    apply hM
    rw [hT]
    calc ‖∑ k, y k • x k‖ ≤ ∑ k, ‖y k • x k‖ := norm_sum_le _ _
      _ ≤ ∑ k, ‖y k‖ := by
          apply Finset.sum_le_sum; intro k _
          rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (hx k)
      _ ≤ c * ρ := hy)
  have hcd : ContDiff ℂ c F := contDiff_of_differentiable_fd hF c
  rw [T.iteratedFDeriv_comp_right hcd 0 le_rfl] at h1
  have hx' : (fun j : Fin c => T (Pi.single j 1)) = x := by
    funext j; rw [hT]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero, hx'] using h1
end ReciprocityTheory.ChartRestriction.G.I2
