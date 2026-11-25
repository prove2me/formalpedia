-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proj_apply_ad92f62b9ffa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:53:19.503252+00:00
-- url     : https://prove2.me/submissions/c90fb291-608b-4174-9256-3e5df4e64ac4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open GroundTheory.Automorphic
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.ComplementExtension
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
variable {h : HermitianForm F E W} {v w : W}
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.ComplementExtension
theorem _root_.solution (hp : IsHyperbolicPair h v w) (x : W) :
    (proj hp x : W) = x - h.toSesq w x • v - h.toSesq v x • w := rfl
end GroundTheory.Heights₂.Heights.FiniteCovolume.ComplementExtension
