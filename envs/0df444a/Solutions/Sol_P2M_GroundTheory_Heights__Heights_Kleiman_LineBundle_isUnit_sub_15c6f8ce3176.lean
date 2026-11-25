-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_isUnit_sub_15c6f8ce3176
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:15:40.942811+00:00
-- url     : https://prove2.me/submissions/4bc140dc-af37-4439-a377-cf4ebd5d3a88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace LineBundle
theorem _root_.solution (Q : LineBundle k x) (I : Chart x) : IsUnit (Q.sub I) := by
  obtain ⟨Q', h⟩ := Q.invertible I
  exact IsUnit.of_mul_eq_one _ h
end LineBundle
end GroundTheory.Heights₂.Heights.Kleiman
