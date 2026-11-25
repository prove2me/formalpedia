-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_map_inclA_mem_SU_f619b6d027f8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:20:55.158052+00:00
-- url     : https://prove2.me/submissions/ef5c2f42-c6a5-423b-8c5a-0989e9e6b905

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PSAOpenHolds
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
namespace GroundTheory.Heights₂.Heights.StrongApprox
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) {γ : Matrix (Fin N) (Fin N) E}
    (hγ : γ ∈ SU c.toRingHom J) :
    γ.map (inclA F E) ∈ SU (sigA c) (J.map (inclA F E)) := by
  obtain ⟨hdet, hform⟩ := hγ
  have hsig : ∀ y : E, sigA c (inclA F E y) = inclA F E (c y) := by
    intro y
    simp [sigA, inclA, Algebra.TensorProduct.map_tmul]
  have hmap : (γ.map (inclA F E)).map (sigA c) = (γ.map c.toRingHom).map (inclA F E) := by
    ext i j
    simp [hsig]
  refine ⟨?_, ?_⟩
  · rw [show (γ.map (inclA F E)).det = inclA F E γ.det from (RingHom.map_det _ _).symm, hdet, map_one]
  · rw [hmap, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hform]
end GroundTheory.Heights₂.Heights.StrongApprox
