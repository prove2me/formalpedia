-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_X_mem_lineOriginIdeal_62be9b559b35
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:30.361623+00:00
-- url     : https://prove2.me/submissions/cff74643-cc60-48ab-85af-5bd5aa25bb33

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
theorem _root_.solution : (X 0 : MvPolynomial (Fin 1) ℂ) ∈ lineOriginIdeal := by
  rw [lineOriginIdeal, RingHom.mem_ker]
  simp
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
