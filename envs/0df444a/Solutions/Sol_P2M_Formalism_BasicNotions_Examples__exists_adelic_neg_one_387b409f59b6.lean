-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__exists_adelic_neg_one_387b409f59b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:40:56.542653+00:00
-- url     : https://prove2.me/submissions/1ab134ee-c28d-4da7-bda2-3401826072f9

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__adelic_theta_conj_c64eb5f92f34
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__adelic_theta_mul_one_sub_157e8bacc1c8
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__adel_key_82da0ac38b2f
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__adel_hom_key_afaa1b4817b3
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__adel_alg_6c628a2428b5
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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



set_option autoImplicit false
open IsDedekindDomain HeightOneSpectrum IsLocalRing WithZero NumberField Filter Topology
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open scoped TensorProduct
variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution (σ : H.E →ₐ[H.F] H.E) (hσ : ∀ x, σ x = H.conj x) :
    ∃ y : H.E ⊗[H.F] FiniteAdeleRing (𝓞 H.F) H.F,
      Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 H.F) H.F) y * y = -1 := by
  have hL : ∀ x : H.E, Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 H.F) H.F)
      ((Algebra.TensorProduct.includeLeftRingHom :
        H.E →+* H.E ⊗[H.F] FiniteAdeleRing (𝓞 H.F) H.F) x)
      = (Algebra.TensorProduct.includeLeftRingHom :
        H.E →+* H.E ⊗[H.F] FiniteAdeleRing (𝓞 H.F) H.F) (σ x) := by
    intro x
    simp [Formalism.UG.sigR, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul]
  have hR : ∀ a : FiniteAdeleRing (𝓞 H.F) H.F, Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 H.F) H.F)
      ((Algebra.TensorProduct.includeRight :
        FiniteAdeleRing (𝓞 H.F) H.F →ₐ[H.F] H.E ⊗[H.F] FiniteAdeleRing (𝓞 H.F) H.F).toRingHom a)
      = (Algebra.TensorProduct.includeRight :
        FiniteAdeleRing (𝓞 H.F) H.F →ₐ[H.F] H.E ⊗[H.F] FiniteAdeleRing (𝓞 H.F) H.F).toRingHom a := by
    intro a
    simp [Formalism.UG.sigR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  have key := adel_hom_key (Algebra.TensorProduct.includeRight :
    FiniteAdeleRing (𝓞 H.F) H.F →ₐ[H.F] H.E ⊗[H.F] FiniteAdeleRing (𝓞 H.F) H.F).toRingHom _ _ _ (adel_key H)
  have hu : (Algebra.TensorProduct.includeLeftRingHom :
        H.E →+* H.E ⊗[H.F] FiniteAdeleRing (𝓞 H.F) H.F) (adelTheta H)
      * (1 - (Algebra.TensorProduct.includeLeftRingHom :
        H.E →+* H.E ⊗[H.F] FiniteAdeleRing (𝓞 H.F) H.F) (adelTheta H))
      = ((adelNd H : ℤ) : H.E ⊗[H.F] FiniteAdeleRing (𝓞 H.F) H.F) := by
    rw [← map_one (Algebra.TensorProduct.includeLeftRingHom :
        H.E →+* H.E ⊗[H.F] FiniteAdeleRing (𝓞 H.F) H.F), ← map_sub, ← map_mul, adelic_theta_mul_one_sub, map_intCast]
  have hτu : Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 H.F) H.F)
      ((Algebra.TensorProduct.includeLeftRingHom :
        H.E →+* H.E ⊗[H.F] FiniteAdeleRing (𝓞 H.F) H.F) (adelTheta H))
      = 1 - (Algebra.TensorProduct.includeLeftRingHom :
        H.E →+* H.E ⊗[H.F] FiniteAdeleRing (𝓞 H.F) H.F) (adelTheta H) := by
    rw [hL, hσ, adelic_theta_conj, map_sub, map_one]
  exact ⟨_, adel_alg _ _ _ _ _ (hR _) (hR _) hτu hu key⟩
end Formalism.BasicNotions.Examples₂
