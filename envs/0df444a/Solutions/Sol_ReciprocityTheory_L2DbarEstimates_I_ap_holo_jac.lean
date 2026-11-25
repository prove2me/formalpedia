-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.ap_holo_jac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:27:02.817584+00:00
-- url     : https://prove2.me/submissions/f5e1b9e7-7981-411e-91f6-7f860dcfde1c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_holo_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : Fin n → M → ℂ)
    (hg : ∀ i, Holo n z (g i)) : Holo n z (jac n z g) := by
  intro e he
  have hA : ∀ i k, DifferentiableOn ℂ ((d n z k (g i)) ∘ e.symm) e.target :=
    fun i k => ap_holo_d n z (g i) (hg i) k e he
  have h1 : (jac n z g ∘ e.symm) = fun y => ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, d n z i (g (σ i)) (e.symm y) := by
    funext y
    simp only [Function.comp_apply, jac, Matrix.det_apply, Matrix.of_apply, Units.smul_def,
      zsmul_eq_mul]
  rw [h1]
  apply DifferentiableOn.fun_sum
  intro σ _
  apply DifferentiableOn.const_mul
  intro y hy
  exact (HasFDerivWithinAt.finsetProd (fun i _ => ((hA (σ i) i) y hy).hasFDerivWithinAt)).differentiableWithinAt
end ReciprocityTheory.L2DbarEstimates.I
