-- Prove2me | solution 1 for P2M_GlobalTheory_T_fderiv_integral_mul_kernel_apply__4434511597b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:58:01.914705+00:00
-- url     : https://prove2.me/submissions/eacb7d12-566a-47b2-a330-5f43d9cb5e51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FderivIntegralMulKernelApply
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FderivIntegralMulKernelApplyStatement
import Theorems.Thm_GlobalTheory_fderiv_integral_mul_kernel_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Metric
open scoped ContDiff
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (ν : Measure V) [ν.IsAddHaarMeasure] {U : Set V}, IsOpen U → ∀ {α : V → ℂ}, Continuous α → HasCompactSupport α → tsupport α ⊆ U → ∀ {K : V × V → ℂ}, ContDiffOn ℝ ∞ K (U ×ˢ U) → ∀ {x : V}, x ∈ U → ∀ v : V, fderiv ℝ (fun x' => ∫ y, α y * K (x', y) ∂ν) x v = ∫ y, α y * fderiv ℝ (fun x' => K (x', y)) x v ∂ν := by
  first | exact @GlobalTheory.fderiv_integral_mul_kernel_apply | exact GlobalTheory.fderiv_integral_mul_kernel_apply | (intros; apply GlobalTheory.fderiv_integral_mul_kernel_apply <;> assumption)
end _root_.GlobalTheory.T
