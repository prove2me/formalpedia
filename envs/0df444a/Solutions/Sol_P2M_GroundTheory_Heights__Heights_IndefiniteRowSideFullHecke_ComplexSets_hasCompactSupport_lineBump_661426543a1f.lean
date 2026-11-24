-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hasCompactSupport_lineBump_661426543a1f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:31.244359+00:00
-- url     : https://prove2.me/submissions/b2584fc3-a73c-44c0-bb22-e92f6c220b24

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff ENNReal
noncomputable section
variable {n d e : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution : HasCompactSupport lineBump :=
  (ContDiffBump.hasCompactSupport _).comp_homeomorph (Homeomorph.funUnique (Fin 1) ℂ)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
