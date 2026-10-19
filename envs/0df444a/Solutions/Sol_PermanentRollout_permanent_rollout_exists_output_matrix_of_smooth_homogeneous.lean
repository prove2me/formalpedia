-- Prove2me | solution 1 for PermanentRollout.permanent_rollout_exists_output_matrix_of_smooth_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/f9f53bfc-6c64-4759-81f0-259b58be5952

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_permanent_rollout_exists_avoiding_finite_smooth_chart_images
import Theorems.Thm_PermanentRollout_permanent_rollout_output_chart_contDiffAt
import Theorems.Thm_PermanentRollout_permanent_rollout_uniform_output_chart_real_finrank_lt
import Theorems.Thm_PermanentRollout_permanent_rollout_output_chart_eq_of_mulVec_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {k m e : ℕ}
    (g : (Fin k → ℂ) → (Fin m → ℂ))
    (hg : ContDiff ℝ 1 g)
    (hnonzero : ∀ u : Fin k → ℂ, u ≠ 0 → g u ≠ 0)
    (hscale : ∀ (a : ℂ) (u : Fin k → ℂ),
      g (a • u) = a ^ e • g u) :
    ∃ A : Matrix (Fin k) (Fin m) ℂ,
      ∀ u : Fin k → ℂ, u ≠ 0 → Matrix.mulVec A (g u) ≠ 0 := by
  classical
  cases k with
  | zero =>
      refine ⟨0, ?_⟩
      intro u hu
      exact (hu (Subsingleton.elim u 0)).elim
  | succ k =>
      cases m with
      | zero =>
          have hu : (fun _ : Fin (k + 1) => (1 : ℂ)) ≠ 0 := by
            intro h
            have := congrFun h (0 : Fin (k + 1))
            simp at this
          exact (hnonzero _ hu (Subsingleton.elim _ _)).elim
      | succ m =>
          let charts :
              Fin (k + 1) × Fin (m + 1) →
                permanentRolloutUniformOutputChartDomain k m →
                  (Fin (k + 1) → Fin (m + 1) → ℂ) :=
            fun i => permanentRolloutOutputChart g i.1 i.2
          let chartDomains :
              Fin (k + 1) × Fin (m + 1) →
                Set (permanentRolloutUniformOutputChartDomain k m) :=
            fun i =>
              {z | g (permanentRolloutNormalizedInput i.1 z.1) i.2 ≠ 0}
          obtain ⟨A, hA⟩ :=
            permanent_rollout_exists_avoiding_finite_smooth_chart_images
              charts chartDomains
              (fun i z hz =>
                permanent_rollout_output_chart_contDiffAt
                  g hg i.1 i.2 z hz)
              (permanent_rollout_uniform_output_chart_real_finrank_lt k m)
          refine ⟨A, ?_⟩
          intro u hu hzero
          obtain ⟨j, hj⟩ : ∃ j : Fin (k + 1), u j ≠ 0 := by
            simpa [funext_iff] using hu
          let w : Fin (k + 1) → ℂ := (u j)⁻¹ • u
          have hwj : w j = 1 := by
            simp [w, hj]
          have hw : w ≠ 0 := by
            intro h
            have := congrFun h j
            simp [hwj] at this
          obtain ⟨ell, hell⟩ : ∃ ell : Fin (m + 1), g w ell ≠ 0 := by
            simpa [funext_iff] using hnonzero w hw
          have hAzero : Matrix.mulVec A (g w) = 0 := by
            rw [show w = (u j)⁻¹ • u from rfl, hscale]
            apply funext
            intro r
            change
              (∑ q, A r q * (((u j)⁻¹ ^ e • g u) q)) = 0
            simp only [Pi.smul_apply, smul_eq_mul]
            calc
              (∑ q, A r q * ((u j)⁻¹ ^ e * g u q)) =
                  (u j)⁻¹ ^ e * (∑ q, A r q * g u q) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro q _
                    ring
              _ = 0 := by
                have hr := congrFun hzero r
                change (∑ q, A r q * g u q) = 0 at hr
                rw [hr, mul_zero]
          have hchart := permanent_rollout_output_chart_eq_of_mulVec_zero
            g j ell w hwj hell A hAzero
          apply hA (j, ell)
          refine ⟨(j.removeNth w,
            fun r q => A r (ell.succAbove q)), ?_, hchart⟩
          change
            g (permanentRolloutNormalizedInput j
              (j.removeNth w)) ell ≠ 0
          have hnormalize :
              permanentRolloutNormalizedInput j (j.removeNth w) = w := by
            simpa only [permanentRolloutNormalizedInput, hwj] using
              Fin.insertNth_self_removeNth j w
          rwa [hnormalize]
end PermanentRollout
