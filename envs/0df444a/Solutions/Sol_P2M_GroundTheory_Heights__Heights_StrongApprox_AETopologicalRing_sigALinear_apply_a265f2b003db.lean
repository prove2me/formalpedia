-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_AETopologicalRing_sigALinear_apply_a265f2b003db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:19:13.558858+00:00
-- url     : https://prove2.me/submissions/e020fb93-6f04-4a4b-ae2f-65925c488494

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PAETopologicalRing
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
omit [NumberField E]
namespace GroundTheory.Heights₂.Heights.StrongApprox
namespace AETopologicalRing
theorem _root_.solution (c : E ≃ₐ[F] E) (a : AE F E) :
    AETopologicalRing.sigALinear c a = sigA c a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]
end AETopologicalRing
end GroundTheory.Heights₂.Heights.StrongApprox
