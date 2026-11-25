-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_sigA_inclA_apply_e79317340074
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:19:53.755237+00:00
-- url     : https://prove2.me/submissions/1f17a25e-0032-4083-b985-5dc0a525ad81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_POrthProjection
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
namespace GroundTheory.Heights₂.Heights.StrongApprox
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E)
    (x : E) : sigA c (inclA F E x) = inclA F E (c x) := by
  simp [sigA, inclA, Algebra.TensorProduct.map_tmul]
end GroundTheory.Heights₂.Heights.StrongApprox
