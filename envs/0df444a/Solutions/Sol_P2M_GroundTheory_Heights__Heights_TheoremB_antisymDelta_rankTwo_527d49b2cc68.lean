-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_antisymDelta_rankTwo_527d49b2cc68
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:22:29.163867+00:00
-- url     : https://prove2.me/submissions/e1f3109b-4e67-44da-b245-937eb7cef43c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset
variable (d : IndexData)
namespace GroundTheory.Heights₂.Heights.TheoremB
theorem _root_.solution : antisymDelta (Fin d1.f) d1.N = (X (0, 0) - X (0, 1) : LamPoly d1) := by
  have h0 : Finset.Ioi (0 : Fin 2) = {1} := by decide
  have h1 : Finset.Ioi (1 : Fin 2) = ∅ := by decide
  simp [antisymDelta, Fin.prod_univ_two, h0, h1]
end GroundTheory.Heights₂.Heights.TheoremB
