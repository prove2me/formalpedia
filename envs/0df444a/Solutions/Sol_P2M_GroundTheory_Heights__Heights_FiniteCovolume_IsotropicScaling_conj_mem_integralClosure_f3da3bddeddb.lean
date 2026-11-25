-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_conj_mem_integralClosure_f3da3bddeddb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:11:28.1137+00:00
-- url     : https://prove2.me/submissions/284a4883-5d90-4345-a7d6-7eaa3ed2a905

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVectorOrbits
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIsotropicScaling

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
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.IsotropicScaling
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
omit [NumberField E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.IsotropicScaling
theorem _root_.solution {z : E}
    (hz : z ∈ integralClosure ℤ E) : conj F E z ∈ integralClosure ℤ E :=
  IsIntegral.map ((conj F E : E ≃ₐ[F] E) : E →+* E).toIntAlgHom hz
end GroundTheory.Heights₂.Heights.FiniteCovolume.IsotropicScaling
