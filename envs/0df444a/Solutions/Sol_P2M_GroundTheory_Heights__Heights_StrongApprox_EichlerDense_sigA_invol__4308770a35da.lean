-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_sigA_invol__4308770a35da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:20:24.244632+00:00
-- url     : https://prove2.me/submissions/effb01bb-6138-4203-9e9c-af05cddf2338

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerDense
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
open GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
omit [NumberField E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
theorem _root_.solution (c : E ≃ₐ[F] E) (hc2 : ∀ x, c (c x) = x) (a : AE F E) :
    sigA c (sigA c a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigA, Algebra.TensorProduct.map_tmul, hc2]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
end GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
