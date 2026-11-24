-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_hf_map_ce22e49943f2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:53.176376+00:00
-- url     : https://prove2.me/submissions/df63bfdf-5fae-48f1-aa3f-bc0a744d3d15

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
variable {R : Type*} [CommRing R] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
theorem _root_.solution {S : Type*} [CommRing S] (σ : R →+* R) (σ' : S →+* S) (φ : R →+* S)
    (hφ : ∀ x, φ (σ x) = σ' (φ x)) (J : Matrix (Fin N) (Fin N) R) (x y : Fin N → R) :
    hf σ' (J.map φ) (φ ∘ x) (φ ∘ y) = φ (hf σ J x y) := by
  simp [hf, map_sum, map_mul, hφ]
end GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
