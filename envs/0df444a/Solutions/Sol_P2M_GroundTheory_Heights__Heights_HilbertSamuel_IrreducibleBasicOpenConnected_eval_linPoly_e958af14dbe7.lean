-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_eval_linPoly_e958af14dbe7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:53.369098+00:00
-- url     : https://prove2.me/submissions/5f46e654-4ddb-4cb8-8acf-8396430c0def

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_BasicOpenSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Filter Topology
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace IrreducibleBasicOpenConnected
theorem _root_.solution {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ)
    (x : Fin n → ℂ) : (fun i => eval x (ComplexSets.linPoly A i)) = A.mulVec x := by
  funext i
  simp [ComplexSets.linPoly, Matrix.mulVec, dotProduct, map_sum]
end IrreducibleBasicOpenConnected
end GroundTheory.Heights₂.Heights.HilbertSamuel
