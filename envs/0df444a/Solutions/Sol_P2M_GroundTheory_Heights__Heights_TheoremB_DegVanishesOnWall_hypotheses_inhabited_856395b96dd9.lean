-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_DegVanishesOnWall_hypotheses_inhabited_856395b96dd9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:22.6578+00:00
-- url     : https://prove2.me/submissions/5dabd3dc-802a-4055-8aa8-c0496af1197d

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
namespace DegVanishesOnWall
theorem _root_.solution :
    ∃ (u : Idx d1 → ℚ) (a b : Fin d1.N), b.val = a.val + 1 ∧ u (0, a) = u (0, b) :=
  ⟨fun _ => 1, ⟨0, by norm_num⟩, ⟨1, by norm_num⟩, rfl, rfl⟩
end DegVanishesOnWall
end GroundTheory.Heights₂.Heights.TheoremB
