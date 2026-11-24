-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_eval_linPoly_64fe785a0385
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:52:01.472329+00:00
-- url     : https://prove2.me/submissions/9edeab7e-c351-46c5-b676-796292d0f960

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceObjects

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
open MvPolynomial Matrix ComplexSets
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (L : Matrix (Fin d) (Fin n) ℂ) (i : Fin d) (x : Fin n → ℂ) :
    eval x (linPoly L i) = (L *ᵥ x) i := by
  simp [linPoly, Matrix.mulVec, dotProduct]
end GroundTheory.Heights₂.Heights
