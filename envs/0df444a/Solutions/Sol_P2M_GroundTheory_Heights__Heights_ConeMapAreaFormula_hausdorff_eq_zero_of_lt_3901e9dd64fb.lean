-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeMapAreaFormula_hausdorff_eq_zero_of_lt_3901e9dd64fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:33:02.76174+00:00
-- url     : https://prove2.me/submissions/c90790a6-5b2d-41b0-b070-8ff4ad5cb7c6

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
theorem _root_.solution {n d : ℕ} (h : n < d) :
    (Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) : Measure (EuclideanSpace ℂ (Fin n))) = 0 := by
  rw [← Measure.measure_univ_eq_zero]
  have hd : dimH (Set.univ : Set (EuclideanSpace ℂ (Fin n))) < (((2 * d : ℕ) : ℝ≥0) : ℝ≥0∞) := by
    rw [Real.dimH_univ_eq_finrank (EuclideanSpace ℂ (Fin n)), finrank_real_of_complex,
      finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 2 * n < 2 * d)
  simpa using hausdorffMeasure_of_dimH_lt hd
end GroundTheory.Heights₂.Heights.ConeMapAreaFormula
