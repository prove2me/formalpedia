-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_hf_single_incl_598849498d15
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:19:41.951837+00:00
-- url     : https://prove2.me/submissions/afcf1d0f-2c1b-4b74-b68d-6057f51e6f2b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerAtPlace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_sigV_inclV_43dcc351241d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_sigA_inclA_d6c27ebe640d
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_sigA_inclA_87fddbe307ad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_sigV_inclV_8ef6594cc226
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
open GroundTheory.Heights₂.Heights.StrongApprox.EichlerAtPlace
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.EichlerAtPlace
theorem _root_.solution (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
    (hsi : ∀ (x : Kv E v) (y : E), singleV E v (x * inclV E v y) = singleV E v x * inclA F E y)
    {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (u : Fin N → Kv E v) (y : Fin N → E) :
    hf (sigA c) (J.map (inclA F E)) (singleV E v ∘ u) (inclA F E ∘ y) =
      singleV E v (hf (sigV c v).toRingHom (J.map (inclV E v)) u (inclV E v ∘ y)) := by
  simp only [hf, map_sum, Matrix.map_apply, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [sigA_inclA, sigV_inclV, mul_assoc, ← map_mul (inclA F E), mul_assoc, ← map_mul (inclV E v), hsi]
end GroundTheory.Heights₂.Heights.StrongApprox.EichlerAtPlace
