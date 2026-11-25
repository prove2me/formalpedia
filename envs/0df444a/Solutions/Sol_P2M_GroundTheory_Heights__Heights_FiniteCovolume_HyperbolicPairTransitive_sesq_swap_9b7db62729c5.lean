-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_sesq_swap_9b7db62729c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:49:44.145907+00:00
-- url     : https://prove2.me/submissions/c8571ae2-0f82-42d7-8db2-8397e12768d2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHyperbolicPairs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHyperbolicPairTransitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
open GroundTheory.Heights₂.Heights.FiniteCovolume.HyperbolicPairTransitive
omit [NumberField E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.HyperbolicPairTransitive
theorem _root_.solution (h : HermitianForm F E W) (x y : W) :
    h.toSesq y x = conj F E (h.toSesq x y) :=
  (h.isSymm.eq x y).symm
end GroundTheory.Heights₂.Heights.FiniteCovolume.HyperbolicPairTransitive
