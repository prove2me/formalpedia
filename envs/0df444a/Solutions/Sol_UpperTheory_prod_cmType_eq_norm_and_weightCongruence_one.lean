-- Prove2me | solution 1 for UpperTheory.prod_cmType_eq_norm_and_weightCongruence_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:03:51.662861+00:00
-- url     : https://prove2.me/submissions/772f6179-5fce-45e5-9d44-c82e9d7114da

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdCmTypeEqNormAndWeightCongruenceOne
import Theorems.Thm_Formalism_FrobeniusOrbits_galE_mem_Psi_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostAx_galE_mem_Psi_iff
import Theorems.Thm_Formalism_HC_HostRaw_sqd_mem_K
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open NumberField IsDedekindDomain Formalism.BasicNotions
private theorem galK_bij {R : Ranks} (H : Host R) : Function.Bijective (galK H) := by
  constructor
  · intro g₁ g₂ h
    have h' : H.sigmaOf (g₁ : R.GG) = H.sigmaOf (g₂ : R.GG) := by
      ext y
      exact congrArg (fun f : H.E ≃ₐ[H.K] H.E => f y) h
    apply Subtype.ext
    simpa [Formalism.BasicNotions.Host.sigmaOf] using h'
  · intro τ
    have hτ : (τ.restrictScalars ℚ) H.sqd = H.sqd := by
      have := τ.commutes (⟨H.sqd, H.sqd_mem_K⟩ : H.K)
      simpa using this
    refine ⟨⟨H.gal (τ.restrictScalars ℚ), ?_⟩, ?_⟩
    · exact (Formalism.HC.HostAx.galE_mem_Psi_iff H.toHostAx _).mpr hτ
    · ext y
      simp [galK, Formalism.BasicNotions.Host.sigmaOf]
end

set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.BasicNotions
namespace UpperTheory
theorem _root_.solution :
    ∀ (R : Ranks) (H : Host R) (ι : Type) [Fintype ι] (eT : ι ≃ R.Psi),
      (∀ x : H.E, ∏ τ, H.sigmaOf ((eT τ : R.Psi) : R.GG) x = algebraMap H.K H.E (Algebra.norm H.K x)) ∧
      UpperTheory.MU (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) (fun _ => 1) := by
  intro R H ι _ eT
  haveI : IsGalois ℚ H.E := H.galois
  haveI : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ H.K H.E
  have hnorm : ∀ x : H.E, ∏ τ, H.sigmaOf ((eT τ : R.Psi) : R.GG) x =
      algebraMap H.K H.E (Algebra.norm H.K x) := by
    intro x
    rw [Algebra.norm_eq_prod_automorphisms]
    exact Fintype.prod_bijective (fun τ => galK H (eT τ)) ((galK_bij H).comp eT.bijective)
      _ _ (fun τ => rfl)
  refine ⟨hnorm, ?_⟩
  intro z hz
  have h1 := hnorm z
  rw [H.der.norm_mu z hz, map_one] at h1
  simp only [zpow_one, Formalism.BasicNotions.Host.emb, RingHom.comp_apply, RingHom.coe_coe]
  rw [← map_prod, h1, map_one]
end UpperTheory
