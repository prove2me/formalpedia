-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_two_mul_le_add_div_264c0a734aca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:52:03.415461+00:00
-- url     : https://prove2.me/submissions/2c02be97-60e1-434d-8cc1-0bc42d887d00

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffBoundaryBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.CutOffBoundaryBound
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.CutOffBoundaryBound
theorem _root_.solution {t : ℝ} (ht : 0 < t) (u v : ℝ) : 2 * u * v ≤ t * u ^ 2 + v ^ 2 / t := by
  have h : 0 ≤ (t * u - v) ^ 2 / t := by positivity
  have e : (t * u - v) ^ 2 / t = t * u ^ 2 - 2 * u * v + v ^ 2 / t := by
    field_simp
    ring
  linarith
end GroundTheory.Heights₂.Heights.CutOffBoundaryBound
