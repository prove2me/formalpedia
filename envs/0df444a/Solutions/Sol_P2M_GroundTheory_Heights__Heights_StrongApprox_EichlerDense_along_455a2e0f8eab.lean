-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_along_455a2e0f8eab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:43:34.432067+00:00
-- url     : https://prove2.me/submissions/eafca7e8-65d6-4a20-9e25-935c3c79921f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerDense
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_hf_map_ce22e49943f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_param_map_211a8f28762a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_param_mem_17e5ebbedd81
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_eq_param_ece8966a1178
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_continuous_hf_326ae2bee618
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_continuous_eich_25adfc1992d9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_c_invol_cedc9596829d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_sigA_inclA__76fc8e51f144
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_sigA_invol__4308770a35da
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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
theorem _root_.solution (hT : AETopologicalRing.Statement) (hD : EDenseInAE.Statement)
    (hO : OrthProjection.Statement) (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (N : ℕ) (J : Matrix (Fin N) (Fin N) E) (hJ : Jᵀ = J.map c) (e f : Fin N → E)
    (he : hf c.toRingHom J e e = 0) (hff : hf c.toRingHom J f f = 0) (hef : hf c.toRingHom J e f = 1)
    [TopologicalSpace (AE F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (AE F E)] :
    eichAlong (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f) ⊆
      closure ((fun γ : Matrix (Fin N) (Fin N) E => γ.map (inclA F E)) ''
        eichAlong c.toRingHom J e f) := by
  obtain ⟨hring, hσc, -, -⟩ := hT F E c h2 hc
  have hc2 : ∀ x, c.toRingHom (c.toRingHom x) = x := c_invol c h2 hc
  have hσA : ∀ x, sigA c (sigA c x) = x := sigA_invol' c (c_invol c h2 hc)
  have hφ : ∀ x, inclA F E (c.toRingHom x) = sigA c (inclA F E x) := fun x => (sigA_inclA' c x).symm
  have hJA : (J.map (inclA F E))ᵀ = (J.map (inclA F E)).map (sigA c) := by
    ext i j
    have := congrFun (congrFun hJ i) j
    simp only [transpose_apply, map_apply] at this ⊢
    rw [this, sigA_inclA']
  have hκ : (2 : E)⁻¹ + (2 : E)⁻¹ = 1 := by
    rw [← two_mul, mul_inv_cancel₀ two_ne_zero]
  have hcκ : c.toRingHom (2 : E)⁻¹ = (2 : E)⁻¹ := by rw [map_inv₀, map_ofNat]
  have hκA : inclA F E (2 : E)⁻¹ + inclA F E (2 : E)⁻¹ = 1 := by rw [← map_add, hκ, map_one]
  have hσκA : sigA c (inclA F E (2 : E)⁻¹) = inclA F E (2 : E)⁻¹ := by rw [← hφ, hcκ]
  have heA : hf (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ e) = 0 := by
    rw [hf_map c.toRingHom (sigA c) (inclA F E) hφ, he, map_zero]
  have hffA : hf (sigA c) (J.map (inclA F E)) (inclA F E ∘ f) (inclA F E ∘ f) = 0 := by
    rw [hf_map c.toRingHom (sigA c) (inclA F E) hφ, hff, map_zero]
  have hefA : hf (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f) = 1 := by
    rw [hf_map c.toRingHom (sigA c) (inclA F E) hφ, hef, map_one]
  obtain ⟨hP1, hP2⟩ := hO
  obtain ⟨-, -, hPE, -⟩ := hP1 E c.toRingHom hc2 N J hJ e f he hff hef
  obtain ⟨-, -, -, hfixA⟩ := hP1 (AE F E) (sigA c) hσA N (J.map (inclA F E)) hJA _ _ heA hffA hefA
  obtain ⟨hPcont, -⟩ := hP2 F E c h2 hc N J e f
  have hcont : Continuous (param (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f)
      (inclA F E (2 : E)⁻¹)) := by
    have hu : Continuous fun p : (Fin N → AE F E) × AE F E =>
        perpProj (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f) p.1 :=
      hPcont.comp continuous_fst
    exact continuous_eich hσc _ _ hu ((continuous_snd.sub (hσc.comp continuous_snd)).sub
      (continuous_const.mul (continuous_hf hσc _ hu hu)))
  have hdense : DenseRange (Prod.map (Pi.map fun _ : Fin N => inclA F E) (inclA F E)) :=
    (DenseRange.piMap fun _ => hD F E c h2 hc).prodMap (hD F E c h2 hc)
  intro M hM
  obtain ⟨p, rfl⟩ := eq_param hκA hσκA hfixA hM
  refine map_mem_closure hcont (hdense p) ?_
  rintro _ ⟨⟨w, t⟩, rfl⟩
  exact ⟨param c.toRingHom J e f (2 : E)⁻¹ (w, t), param_mem hc2 hJ hκ hcκ hPE (w, t),
    param_map c.toRingHom (sigA c) (inclA F E) hφ J e f (2 : E)⁻¹ (w, t)⟩
end GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
