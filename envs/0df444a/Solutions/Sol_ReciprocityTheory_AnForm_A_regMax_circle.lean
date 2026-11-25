-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMax_circle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:54:52.265889+00:00
-- url     : https://prove2.me/submissions/b47f6566-321e-4051-91ce-628177b41695

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_abs_regMax_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_convex


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {η : ℝ} (hη : 0 < η) (f : ℂ → ι → ℝ) (c : ℂ) (R : ℝ)
    (hf : ∀ j, CircleIntegrable (fun ζ => f ζ j) c R) :
    CircleIntegrable (fun ζ => regMax η (f ζ)) c R ∧
      regMax η (fun j => Real.circleAverage (fun ζ => f ζ j) c R) ≤
        Real.circleAverage (fun ζ => regMax η (f ζ)) c R := by
  have hμ : volume (Ι (0:ℝ) (2 * Real.pi)) = ENNReal.ofReal (2 * Real.pi) := by
    rw [Set.uIoc_of_le (by positivity), Real.volume_Ioc, sub_zero]
  have : IsFiniteMeasure (volume.restrict (Ι (0:ℝ) (2 * Real.pi))) :=
    isFiniteMeasure_restrict.2 (by rw [hμ]; exact ENNReal.ofReal_ne_top)
  have : NeZero (volume.restrict (Ι (0:ℝ) (2 * Real.pi))) := ⟨fun h => by
    have := Measure.restrict_eq_zero.1 h
    rw [hμ, ENNReal.ofReal_eq_zero] at this; linarith [Real.pi_pos]⟩
  have hg : Integrable (fun θ => f (circleMap c R θ)) (volume.restrict (Ι (0:ℝ) (2 * Real.pi))) :=
    integrable_pi_iff.2 fun j => intervalIntegrable_iff.1 (hf j)
  have hF : Continuous (regMax (ι := ι) η) := (regMax_contDiff hη).continuous
  have hFg : Integrable (fun θ => regMax η (f (circleMap c R θ)))
      (volume.restrict (Ι (0:ℝ) (2 * Real.pi))) := by
    refine Integrable.mono' (hg.norm.add (integrable_const (η / 2)))
      (hF.comp_aestronglyMeasurable hg.aestronglyMeasurable) (Eventually.of_forall fun θ => ?_)
    rw [Real.norm_eq_abs]; exact abs_regMax_le hη.le _
  have hci : CircleIntegrable f c R := intervalIntegrable_iff.2 hg
  refine ⟨intervalIntegrable_iff.2 hFg, ?_⟩
  have e : (fun j => Real.circleAverage (fun ζ => f ζ j) c R) = Real.circleAverage f c R := by
    funext j
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j).circleAverage_comp_comm hci
  rw [e, Real.circleAverage_eq_intervalAverage, Real.circleAverage_eq_intervalAverage]
  exact (regMax_convex η).map_average_le hF.continuousOn isClosed_univ
    (Eventually.of_forall fun _ => trivial) hg hFg
end ReciprocityTheory.AnForm.A
