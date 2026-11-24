-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionCycle_extMap_newCoord_1cebe4ed4869
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:23.22789+00:00
-- url     : https://prove2.me/submissions/5b30845b-a11d-4376-85f8-af1e72c7424c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SectionCycle
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {P : ArithVariety n} (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.SectionCycle
theorem _root_.solution (j : Fin (D.size + 1)) :
    D.extMap (X (D.newCoord j)) = C (D.elt j) * X none := by
  rw [AddBlockData.extMap, eval₂Hom_X']
  rfl
end GroundTheory.Heights₂.Heights.SectionCycle
