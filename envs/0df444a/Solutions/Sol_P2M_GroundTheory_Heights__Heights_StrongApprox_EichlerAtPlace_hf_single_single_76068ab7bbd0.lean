-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerAtPlace_hf_single_single_76068ab7bbd0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:19:45.723883+00:00
-- url     : https://prove2.me/submissions/3f4e84b0-e36b-4637-900d-0c810dff33c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerAtPlace
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
open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.EichlerAtPlace
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.EichlerAtPlace
theorem _root_.solution (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
    (hsi : ∀ (x : Kv E v) (y : E), singleV E v (x * inclV E v y) = singleV E v x * inclA F E y)
    (hmul : ∀ x y : Kv E v, singleV E v (x * y) = singleV E v x * singleV E v y)
    (hsig : ∀ x, sigA c (singleV E v x) = singleV E v (sigV c v x))
    {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (u w : Fin N → Kv E v) :
    hf (sigA c) (J.map (inclA F E)) (singleV E v ∘ u) (singleV E v ∘ w) =
      singleV E v (hf (sigV c v).toRingHom (J.map (inclV E v)) u w) := by
  simp only [hf, map_sum, Matrix.map_apply, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsig, hmul, hsi]
end GroundTheory.Heights₂.Heights.StrongApprox.EichlerAtPlace
