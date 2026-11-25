-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_eich_map_f464f4b49db8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:19:54.520563+00:00
-- url     : https://prove2.me/submissions/5853b27c-2647-4210-80ab-06474db7be63

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
    (hφ : ∀ x, φ (σ x) = σ' (φ x)) (J : Matrix (Fin N) (Fin N) R) (e u : Fin N → R) (c : R) :
    (eich σ J e u c).map φ = eich σ' (J.map φ) (φ ∘ e) (φ ∘ u) (φ c) := by
  ext i j
  simp [eich, vecMulVec_apply, mulVec, dotProduct, map_sum, hφ, Matrix.one_apply, apply_ite φ]
end GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
