-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_param_map_211a8f28762a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:36:37.467812+00:00
-- url     : https://prove2.me/submissions/4cda6625-7823-4fdd-8c7a-22d69d0a18a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerDense
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_hf_map_ce22e49943f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_eich_map_f464f4b49db8
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
variable {R : Type*} [CommRing R] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
theorem _root_.solution {S : Type*} [CommRing S] (σ : R →+* R) (σ' : S →+* S) (φ : R →+* S)
    (hφ : ∀ x, φ (σ x) = σ' (φ x)) (J : Matrix (Fin N) (Fin N) R) (e f : Fin N → R) (κ : R)
    (p : (Fin N → R) × R) :
    (param σ J e f κ p).map φ = param σ' (J.map φ) (φ ∘ e) (φ ∘ f) (φ κ) (φ ∘ p.1, φ p.2) := by
  have hP : φ ∘ perpProj σ J e f p.1 = perpProj σ' (J.map φ) (φ ∘ e) (φ ∘ f) (φ ∘ p.1) := by
    funext i
    simp only [perpProj, Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub,
      map_mul, hf_map σ σ' φ hφ]
  rw [param, param, eich_map σ σ' φ hφ, ← hP, map_sub, map_sub, map_mul, hφ, hf_map σ σ' φ hφ]
end GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
