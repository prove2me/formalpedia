-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_ClosureIsSubmonoid_proof_de44efa112c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:56:02.241719+00:00
-- url     : https://prove2.me/submissions/7130214e-666f-48bb-bb61-5db86e3ef6c1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PClosureIsSubmonoid
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_invol_of_quadratic_a0cb9d4cbe1b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_map_mem_SU_AE_259e0285725b
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_eichAlong_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_mul_mem_SU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_one_mem_SU
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
namespace ClosureIsSubmonoid
theorem _root_.solution (h₁ : AETopologicalRing.Statement) (h₂ : EichlerDense.Statement) :
    ClosureIsSubmonoid.Statement := by
  intro F E _ _ _ _ _ c h2 hc N J hJ _ e f he hff hef _ _
  have hσ : ∀ x, c.toRingHom (c.toRingHom x) = x := invol_of_quadratic c h2 hc
  have hJ' : Jᵀ = J.map c.toRingHom := hJ
  obtain ⟨-, -, -, hmat⟩ := h₁ F E c h2 hc
  obtain ⟨hmul, -, -, hclosed⟩ := hmat N (J.map (inclA F E))
  obtain ⟨hde, hdf⟩ := h₂ F E c h2 hc N J hJ e f he hff hef
  set ι : Matrix (Fin N) (Fin N) E → Matrix (Fin N) (Fin N) (AE F E) := fun γ => γ.map (inclA F E)
  have himg : ι '' SU c.toRingHom J ⊆ SU (sigA c) (J.map (inclA F E)) := by
    rintro _ ⟨γ, hγ, rfl⟩; exact map_mem_SU_AE c J hγ
  refine ⟨closure_minimal himg hclosed, ?_, ?_, ?_⟩
  · apply subset_closure
    exact ⟨1, one_mem_SU, by simp⟩
  · intro a ha b hb
    refine map_mem_closure₂ hmul ha hb ?_
    rintro _ ⟨γ, hγ, rfl⟩ _ ⟨δ, hδ, rfl⟩
    exact ⟨γ * δ, mul_mem_SU hγ hδ, by simp [Matrix.map_mul]⟩
  · have hsub : ∀ {a b : Fin N → E}, hf c.toRingHom J a a = 0 →
        closure (ι '' eichAlong c.toRingHom J a b) ⊆ Cl c J := fun ha =>
      closure_mono (Set.image_mono (eichAlong_sub hσ hJ' ha))
    rintro M (hM | hM)
    · exact hsub he (hde hM)
    · exact hsub hff (hdf hM)
end ClosureIsSubmonoid
end GroundTheory.Heights₂.Heights.StrongApprox
