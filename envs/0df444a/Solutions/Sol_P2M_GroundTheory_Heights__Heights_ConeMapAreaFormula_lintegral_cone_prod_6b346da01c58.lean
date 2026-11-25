-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_lintegral_cone_prod_6b346da01c58
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:33:03.521454+00:00
-- url     : https://prove2.me/submissions/4bed9332-744b-4bdb-8277-7ddfdbd9d1ab

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
theorem _root_.solution {e : ℕ} {D : Set (Fin e → ℂ)} (G : (Fin e → ℂ) × ℂ → ℝ≥0∞)
    (hG : AEMeasurable G ((volume.restrict D).prod volume)) :
    ∫⁻ q in {q : (Fin e → ℂ) × ℂ | q.1 ∈ D ∧ q.2 ≠ 0}, G q = ∫⁻ x in D, ∫⁻ t, G (x, t) := by
  have hnull : (volume : Measure ((Fin e → ℂ) × ℂ)) (Set.univ ×ˢ {0}) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, mul_zero]
  have hset : {q : (Fin e → ℂ) × ℂ | q.1 ∈ D ∧ q.2 ≠ 0} = D ×ˢ Set.univ \ Set.univ ×ˢ {0} := by
    ext q
    simp
  rw [hset, setLIntegral_congr (sdiff_null_ae_eq_self hnull), Measure.volume_eq_prod,
    ← Measure.restrict_univ (μ := (volume : Measure ℂ)), ← Measure.prod_restrict]
  simp only [Measure.restrict_univ]
  exact lintegral_prod G hG
end GroundTheory.Heights₂.Heights.ConeMapAreaFormula
