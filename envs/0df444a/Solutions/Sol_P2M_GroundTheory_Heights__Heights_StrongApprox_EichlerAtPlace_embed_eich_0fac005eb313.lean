-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_embed_eich_0fac005eb313
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:19:39.367137+00:00
-- url     : https://prove2.me/submissions/d82ba478-2729-43cf-87d1-e812104a5d04

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
    (hsig : ∀ x, sigA c (singleV E v x) = singleV E v (sigV c v x))
    {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (e : Fin N → E) (u : Fin N → Kv E v) (c' : Kv E v) :
    embed E v (eich (sigV c v).toRingHom (J.map (inclV E v)) (inclV E v ∘ e) u c') =
      eich (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (singleV E v ∘ u) (singleV E v c') := by
  have hw : ∀ j, ((J.map (inclV E v)) *ᵥ ((sigV c v).toRingHom ∘ (inclV E v ∘ e))) j =
      inclV E v ((J *ᵥ (c ∘ e)) j) := by
    intro j
    simp only [mulVec, dotProduct, map_sum, Matrix.map_apply, Function.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, sigV_inclV, map_mul]
  have hwA : ∀ j, ((J.map (inclA F E)) *ᵥ (sigA c ∘ (inclA F E ∘ e))) j =
      inclA F E ((J *ᵥ (c ∘ e)) j) := by
    intro j
    simp only [mulVec, dotProduct, map_sum, Matrix.map_apply, Function.comp_apply, sigA_inclA,
      map_mul]
  have hz : ∀ j, ((J.map (inclA F E)) *ᵥ (sigA c ∘ (singleV E v ∘ u))) j =
      singleV E v (((J.map (inclV E v)) *ᵥ ((sigV c v).toRingHom ∘ u)) j) := by
    intro j
    simp only [mulVec, dotProduct, map_sum, Matrix.map_apply, Function.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsig, mul_comm (inclV E v (J j k)), hsi, mul_comm]
  ext i j
  simp only [embed, eich, Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply,
    vecMulVec_apply, Function.comp_apply, hw, hwA, hz, smul_eq_mul, map_add, map_sub]
  rw [hsi, mul_comm (inclV E v (e i)), hsi, ← map_mul (inclV E v), hsi, map_mul]
  ring
end GroundTheory.Heights₂.Heights.StrongApprox.EichlerAtPlace
