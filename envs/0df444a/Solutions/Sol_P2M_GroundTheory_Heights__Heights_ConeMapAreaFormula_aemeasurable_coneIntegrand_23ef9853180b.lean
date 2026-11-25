-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_aemeasurable_coneIntegrand_23ef9853180b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:33:00.423432+00:00
-- url     : https://prove2.me/submissions/c82b2f1d-4dd8-4c84-adf0-5b8303f84408

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapAreaOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFrameJacobianSum
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VolumePreservingUncurry
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMapAreaOne

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
open MeasureTheory Module
open scoped ENNReal NNReal ComplexOrder
open GroundTheory.Heights₂.Heights.ConeMapAreaFormula
namespace GroundTheory.Heights₂.Heights.ConeMapAreaFormula
theorem _root_.solution {e n : ℕ} {U D : Set (Fin e → ℂ)}
    {v : (Fin e → ℂ) → (Fin n → ℂ)} {F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞} (hD : MeasurableSet D)
    (hDU : D ⊆ U) (hv : DifferentiableOn ℂ v U) (hF : Measurable F) :
    AEMeasurable (coneIntegrand v F) ((volume.restrict D).prod volume) := by
  have hvD : AEMeasurable v (volume.restrict D) := (hv.continuousOn.mono hDU).aemeasurable hD
  have hW : AEMeasurable (gramVecs v) (volume.restrict D) := by
    refine aemeasurable_pi_lambda _ fun a => ?_
    refine Fin.cases ?_ (fun j => ?_) a
    · simpa [gramVecs] using hvD
    · simpa [gramVecs] using
        (measurable_fderiv_apply_const (𝕜 := ℂ) (f := v) (Pi.single j (1 : ℂ))).aemeasurable
  have hΦ : Continuous fun W : Fin (e + 1) → Fin n → ℂ =>
      (Matrix.det (Matrix.of fun a b => ∑ i, star (W a i) * W b i)).re := by
    refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.of_apply]
    refine continuous_finsetSum _ fun i _ => ?_
    fun_prop
  have hg : AEMeasurable (gramVol v) (volume.restrict D) := hΦ.measurable.comp_aemeasurable hW
  have h1 : AEMeasurable (fun q : (Fin e → ℂ) × ℂ => q.2 • WithLp.toLp 2 (v q.1))
      ((volume.restrict D).prod volume) :=
    measurable_snd.aemeasurable.smul
      ((PiLp.continuous_toLp 2 _).measurable.comp_aemeasurable hvD).comp_fst
  refine (hF.comp_aemeasurable h1).mul ?_
  exact ((measurable_snd.norm.pow_const _).aemeasurable.mul hg.comp_fst).ennreal_ofReal
end GroundTheory.Heights₂.Heights.ConeMapAreaFormula
