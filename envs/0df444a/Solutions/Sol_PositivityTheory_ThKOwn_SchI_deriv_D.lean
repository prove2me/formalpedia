-- Prove2me | solution 1 for PositivityTheory.ThKOwn.SchI.deriv_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:02:40.83642+00:00
-- url     : https://prove2.me/submissions/32061c85-6bf0-4428-af80-11c9fbb3e6ee

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_JetApply
import Theorems.Thm_PositivityTheory_ThKOwn_SchI_cont_D
import Theorems.Thm_PositivityTheory_ThKOwn_SchI_bd_D
import Theorems.Thm_PositivityTheory_ThKOwn_SchI_int_D

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKOwn
open PositivityTheory.ThKOwn.SchI
open scoped ContDiff NNReal BoundedContinuousFunction
open MeasureTheory Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {α : Type} [TopologicalSpace α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
  {G : α → SchwartzMap V ℂ} (hG : Continuous G) (hI : ∀ k j : ℕ, Integrable (fun a => SchwartzMap.seminorm ℂ k j (G a)) μ)
include hG hI
namespace PositivityTheory.ThKOwn.SchI
theorem _root_.solution (j : ℕ) (x : V) : HasFDerivAt (fun y => ∫ a, iteratedFDeriv ℝ j (G a) y ∂μ)
    (∫ a, iteratedFDeriv ℝ (j + 1) (G a) x ∂μ).curryLeft x := by
  have hcurry : ∀ (f : SchwartzMap V ℂ) (y : V),
      HasFDerivAt (iteratedFDeriv ℝ j f) (iteratedFDeriv ℝ (j + 1) f y).curryLeft y := by
    intro f y
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j f) y :=
      ((cd f (j + 1)).differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self j)) y
    convert hd.hasFDerivAt using 1
    ext v m
    rw [ContinuousMultilinearMap.curryLeft_apply, iteratedFDeriv_succ_apply_left]
    simp
  have hL : (∫ a, iteratedFDeriv ℝ (j + 1) (G a) x ∂μ).curryLeft =
      ∫ a, (iteratedFDeriv ℝ (j + 1) (G a) x).curryLeft ∂μ :=
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => V) ℂ).toContinuousLinearEquiv.integral_comp_comm _).symm
  rw [hL]
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun y a => iteratedFDeriv ℝ j (G a) y)
    (F' := fun y a => (iteratedFDeriv ℝ (j + 1) (G a) y).curryLeft)
    (bound := fun a => SchwartzMap.seminorm ℂ 0 (j + 1) (G a)) Filter.univ_mem
    (Filter.Eventually.of_forall fun y => (cont_D hG j y).aestronglyMeasurable) (int_D hG hI j x) ?_ ?_
    (hI 0 (j + 1)) ?_
  · exact ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => V) ℂ).continuous.comp
      (cont_D hG (j + 1) x)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun a y _ => ?_
    exact ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => V) ℂ).norm_map _).trans_le
      (bd_D (G a) (j + 1) y)
  · exact Filter.Eventually.of_forall fun a y _ => hcurry (G a) y
end PositivityTheory.ThKOwn.SchI
