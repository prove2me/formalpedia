-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_extMap_id_4a8cefbda138
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:04:58.21931+00:00
-- url     : https://prove2.me/submissions/2b884ad1-de00-4c00-9d47-2ba0d5d885e1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementExtension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_split_520f7645d4f4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_extMap_apply_9a4802f409d1

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
theorem _root_.solution (hp : IsHyperbolicPair h v w) : extMap hp LinearMap.id = LinearMap.id := by
  ext x
  rw [extMap_apply, LinearMap.id_apply, LinearMap.id_apply]
  exact split hp x
end GroundTheory.Heights₂.Heights.FiniteCovolume.ComplementExtension
