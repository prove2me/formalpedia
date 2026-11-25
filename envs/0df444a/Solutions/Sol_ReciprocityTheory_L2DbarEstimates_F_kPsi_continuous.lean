-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.kPsi_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:16:41.362555+00:00
-- url     : https://prove2.me/submissions/21da2cc1-f491-4ca4-be3f-83bb9ee54c8c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_KPsiHasCompactSupport
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (ph : M → ℝ) (hph : Continuous ph) (φ : M → ℂ)
    (hφ : IsTest n z φ) (j k : Fin n) : Continuous (kPsi n z ph φ j k) := by
  have hj := Smooth.continuous n z hz _ (Smooth.db n z j φ hφ.1)
  have hk := Smooth.continuous n z hz _ (Smooth.db n z k φ hφ.1)
  unfold kPsi
  refine (Complex.continuous_ofReal.comp (Real.continuous_exp.comp hph)).smul ?_
  exact ((Complex.continuous_conj.comp hj).smul continuous_const).sub
    ((Complex.continuous_conj.comp hk).smul continuous_const)
end ReciprocityTheory.L2DbarEstimates.F
