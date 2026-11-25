-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_sigA_4ec6939ea22f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:20:38.260349+00:00
-- url     : https://prove2.me/submissions/7fd8baef-6271-4d0a-bdaa-68f2312b5405

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PTruncation
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
open Classical
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox
theorem _root_.solution (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : AE F E) :
    compAt E v (sigA c a) = sigV c v (compAt E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [compAt, sigA, sigV]
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
end GroundTheory.Heights₂.Heights.StrongApprox
