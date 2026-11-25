-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_sigA_singleV_eb561977bf38
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:20:22.675832+00:00
-- url     : https://prove2.me/submissions/8b3f3c89-8aa3-4d97-9827-5d1ad3e8fd6a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PPlaceMaps
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_tmul_ed4fb72a7896
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_sigA_tmul_0520df51def7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_sigV_tmul_16c3ccd1e5df
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_singleV_tmul_6c18ac5465de
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
open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
theorem _root_.solution (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : Kv E v) :
    sigA c (singleV E v x) = singleV E v (sigV c v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  | tmul a b => rw [singleV_tmul, sigA_tmul, sigV_tmul, singleV_tmul]
end GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
