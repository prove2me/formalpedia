-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_IntNumBaseChange_proof_a61ca187712b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:38:11.659953+00:00
-- url     : https://prove2.me/submissions/340b432e-8866-42ed-835e-147f79fd9168

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_IntNumBaseChange_intersectionNumber_baseChange_006254404d6b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace IntNumBaseChange
theorem _root_.solution (_h1 : MixedDiffConst.Statement) : IntNumBaseChange.Statement :=
  IntNumBaseChange.intersectionNumber_baseChange
end IntNumBaseChange
end GroundTheory.Heights₂.Heights.FieldNumbers
