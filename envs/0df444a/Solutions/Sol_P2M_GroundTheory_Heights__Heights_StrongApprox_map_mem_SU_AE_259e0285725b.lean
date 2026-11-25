-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_map_mem_SU_AE_259e0285725b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:48.585863+00:00
-- url     : https://prove2.me/submissions/b61ff16c-feda-430b-bf9f-a007c0a08bde

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PClosureIsSubmonoid
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_sigA_inclA_gen_5b79934e1350
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
namespace GroundTheory.Heights₂.Heights.StrongApprox
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) {γ : Matrix (Fin N) (Fin N) E}
    (hγ : γ ∈ SU c.toRingHom J) :
    γ.map (inclA F E) ∈ SU (sigA c) (J.map (inclA F E)) := by
  obtain ⟨hdet, hJ⟩ := hγ
  refine ⟨?_, ?_⟩
  · have h := (RingHom.map_det (inclA F E) γ).symm
    rw [hdet, map_one] at h
    exact h
  · have hmap : (γ.map (inclA F E)).map (sigA c) = (γ.map c.toRingHom).map (inclA F E) := by
      ext i j; simp [sigA_inclA_gen]
    rw [hmap, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hJ]
end GroundTheory.Heights₂.Heights.StrongApprox
