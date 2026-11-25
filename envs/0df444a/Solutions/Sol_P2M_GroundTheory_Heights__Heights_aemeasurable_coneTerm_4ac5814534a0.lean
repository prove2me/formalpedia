-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_aemeasurable_coneTerm_4ac5814534a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:57:41.250879+00:00
-- url     : https://prove2.me/submissions/ab467406-efc7-4be5-b65e-797e54be33eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetAreaLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetParam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetAreaLintegral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gramVol_eq_gramForm_bbc97b0c0d9c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuous_gramForm_934aa4e46504

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre)
open scoped ENNReal
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {e n : ℕ} {U D : Set (Fin e → ℂ)} {v : (Fin e → ℂ) → (Fin n → ℂ)}
    {F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞} (hU : IsOpen U) (hDU : D ⊆ U)
    (hv : DifferentiableOn ℂ v U) (hF : Measurable F) :
    AEMeasurable (fun x => ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v x)) *
      ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol v x)) (volume.restrict D) := by
  have ha : AEMeasurable v (volume.restrict D) :=
    (hv.continuousOn.aemeasurable hU.measurableSet).mono_measure (Measure.restrict_mono hDU le_rfl)
  have hg : AEMeasurable (fun x => gramVol v x) (volume.restrict D) := by
    have h := continuous_gramForm.measurable.comp_aemeasurable
      (ha.prodMk (measurable_fderiv ℂ v).aemeasurable)
    simpa only [Function.comp_def, ← gramVol_eq_gramForm] using h
  have hmeas : Measurable fun p : (Fin e → ℂ) × ℂ => F (p.2 • WithLp.toLp 2 (ha.mk v p.1)) *
      ENNReal.ofReal (‖p.2‖ ^ (2 * e) * hg.mk _ p.1) := by
    refine (hF.comp (measurable_snd.smul ((PiLp.continuous_toLp 2 _).measurable.comp
      (ha.measurable_mk.comp measurable_fst)))).mul ?_
    exact ENNReal.measurable_ofReal.comp
      ((measurable_snd.norm.pow_const _).mul (hg.measurable_mk.comp measurable_fst))
  refine ⟨_, hmeas.lintegral_prod_right' (ν := (volume : Measure ℂ)), ?_⟩
  filter_upwards [ha.ae_eq_mk, hg.ae_eq_mk] with x h1 h2
  simp only [h1, h2]
end GroundTheory.Heights₂.Heights
