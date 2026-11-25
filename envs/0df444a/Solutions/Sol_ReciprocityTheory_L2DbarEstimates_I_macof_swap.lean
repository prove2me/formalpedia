-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.macof_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:18:09.646654+00:00
-- url     : https://prove2.me/submissions/30c86f8b-b697-40e6-b0f2-4663e94e6dbc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_MacofFderivApplyContDiffOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {i j : Fin n} (h : i ≠ j)
    (e c : Fin n → ℂ) :
    ((M.updateRow i e).updateRow j c).det = -((M.updateRow j e).updateRow i c).det := by
  have hB : (M.updateRow j e).updateRow i c =
      ((M.updateRow i e).updateRow j c).submatrix (Equiv.swap i j) id := by
    ext a b
    simp only [Matrix.submatrix_apply, id]
    rcases eq_or_ne a i with rfl | ha
    · simp [Matrix.updateRow_apply, h]
    rcases eq_or_ne a j with rfl | hb
    · simp [Matrix.updateRow_apply, h, ha, Ne.symm h]
    · simp [Matrix.updateRow_apply, ha, hb, Equiv.swap_apply_of_ne_of_ne ha hb]
  rw [hB, Matrix.det_permute, Equiv.Perm.sign_swap h]
  simp
end ReciprocityTheory.L2DbarEstimates.I
