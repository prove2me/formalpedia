-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphPt_natAdd_be63f7604ada
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:39.368046+00:00
-- url     : https://prove2.me/submissions/af5bcfe6-7896-4221-b3db-54706f54ba50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpenPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedFibreOpenPoly

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
open MvPolynomial Topology Filter Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
theorem _root_.solution (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) (i : Fin d) :
    graphPt p x (Fin.natAdd n i) = eval x (p i) := by
  simp [graphPt, Fin.append_right]
end GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
