-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceComponents_proof_b8a60b85d8c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:08:29.017997+00:00
-- url     : https://prove2.me/submissions/5660a84a-9a5f-4dd6-a9ea-26828f1146f4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartHomogenise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartDehomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PMinimalPrimeHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLocalMultOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_POrdPolynomialLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceComponents
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceComponents_isHomogIdeal_sup_linForm_478a4eaaa94c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceComponents_le_of_le_sup_f963559d6351
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceComponents_isPrime_sup_771df484ccc2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceComponents_mem_support_divCycle_2640b9484206
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceComponents_divCycle_apply_0ef45b426d3d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceComponents_mem_support_iff_2bb896af3ee2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDehomog_proof_43d0929de030
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHomogenise_proof_a08065262b6f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLocDomain_linForm_isHomogeneous_618f3987ba84
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLocDomain_proof_34872f657b6a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLocalOrder_proof_c02df12483c9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSection_proof_5b1b05e34c1e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DehomogOrd_proof_95c60a838754
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalMultOrd_proof_21316c672e2e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimeHomog_proof_bf27ffa11a53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrdPolynomialLocalization_proof_d5922d801c8e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ord_atPrime_congr_c2719e887096


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open SliceComponents
namespace GroundTheory.Heights₂.Heights
namespace SliceComponents
theorem _root_.solution : SliceComponents.Statement := by
  intro n J u ℓ hJ hℓ
  have := hJ.isPrime
  set K := J ⊔ Ideal.span {linForm u} with hKdef
  set L : Ideal (MvPolynomial (Fin n) ℂ) := Ideal.span {linForm ℓ - 1} with hLdef
  have hK : IsHomogIdeal K := isHomogIdeal_sup_linForm hJ.isHomog u
  have hK' : J ⊔ L ⊔ Ideal.span {linForm u} = K ⊔ L := sup_right_comm _ _ _
  have hsupp := fun W => mem_support_iff (W := W) hℓ
  have hhom : ∀ W ∈ K.minimalPrimes, IsHomogIdeal W := fun W hW => MinimalPrimeHomog.proof ℂ n K W hK hW

  have hchart : ∀ Q : Ideal _, Q.IsPrime → K ⊔ L ≤ Q →
      ∃ V, IsProjPrime V ∧ linForm ℓ ∉ V ∧ V ⊔ L = Q ∧ K ≤ V := fun Q hQ hKQ => by
    obtain ⟨V, hV, hℓV, hVQ, hVmax⟩ :=
      ChartHomogenise.proof ℂ n Q ℓ hQ (hKQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    exact ⟨V, hV, hℓV, hVQ, hVmax K hK (le_sup_left.trans hKQ)⟩
  have hmin : ∀ W ∈ (divCycle J u).support, W ⊔ L ∈ (K ⊔ L).minimalPrimes := fun W hW => by
    obtain ⟨hWm, hℓW⟩ := (hsupp W).mp hW
    have := hWm.1.1
    refine ⟨⟨isPrime_sup hWm.1.1 (hhom W hWm) hℓW, sup_le_sup_right hWm.1.2 _⟩, fun Q ⟨hQ, hKQ⟩ hQW => ?_⟩
    obtain ⟨V, hV, -, hVQ, hKV⟩ := hchart Q hQ hKQ
    have hVW : V ≤ W :=
      le_of_le_sup hV.isHomog hWm.1.1 (hhom W hWm) hℓW ((le_sup_left.trans hVQ.le).trans hQW)
    rw [← hVQ]
    exact sup_le_sup_right (hWm.2 ⟨hV.isPrime, hKV⟩ hVW) _
  refine ⟨fun W₁ h₁ W₂ h₂ (e : W₁ ⊔ L = W₂ ⊔ L) => ?_, ?_, fun W hW => ?_⟩
  · obtain ⟨hm₁, hℓ₁⟩ := (hsupp W₁).mp h₁
    obtain ⟨hm₂, hℓ₂⟩ := (hsupp W₂).mp h₂
    exact le_antisymm
      (le_of_le_sup (hhom W₁ hm₁) hm₂.1.1 (hhom W₂ hm₂) hℓ₂ (e ▸ le_sup_left))
      (le_of_le_sup (hhom W₂ hm₂) hm₁.1.1 (hhom W₁ hm₁) hℓ₁ (e.symm ▸ le_sup_left))
  · rw [hK']
    ext Q
    refine ⟨fun ⟨W, hW, hWQ⟩ => hWQ ▸ hmin W hW, fun hQ => ?_⟩
    have := hQ.1.1
    obtain ⟨V, hV, hℓV, hVQ, hKV⟩ := hchart Q hQ.1.1 hQ.1.2
    have := hV.isPrime
    obtain ⟨W, hWm, hWV⟩ := Ideal.exists_minimalPrimes_le hKV
    have hW : W ∈ (divCycle J u).support := (hsupp W).mpr ⟨hWm, fun h => hℓV (hWV h)⟩
    have hle : W ⊔ L ≤ Q := hVQ ▸ sup_le_sup_right hWV _
    exact ⟨W, hW, le_antisymm hle (hQ.2 (hmin W hW).1 hle)⟩
  · obtain ⟨hWm, hℓW⟩ := (hsupp W).mp hW
    have := hWm.1.1
    have hWL := isPrime_sup hWm.1.1 (hhom W hWm) hℓW
    have hJW : J ≤ W := le_sup_left.trans hWm.1.2
    have : (W.map (Ideal.Quotient.mk J)).IsPrime := Ideal.map_isPrime_of_surjective
      Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hJW)
    have hmapeq : (W ⊔ L).map (Ideal.Quotient.mk (J ⊔ L)) = W.map (Ideal.Quotient.mk (J ⊔ L)) := by
      have hL0 : L.map (Ideal.Quotient.mk (J ⊔ L)) = ⊥ :=
        (Ideal.map_eq_bot_iff_le_ker _).mpr (by rw [Ideal.mk_ker]; exact le_sup_right)
      rw [Ideal.map_sup, hL0, sup_bot_eq]
    have hP' : ((W ⊔ L).map (Ideal.Quotient.mk (J ⊔ L))).IsPrime := Ideal.map_isPrime_of_surjective
      Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact sup_le_sup_right hJW _)
    have : (W.map (Ideal.Quotient.mk (J ⊔ L))).IsPrime := hmapeq ▸ hP'
    rw [divCycle_apply (mem_support_divCycle.mp hW).1]
    have e₁ := LocalMultOrd.proof _ J W (linForm u) hWm
    have e₂ := DehomogOrd.proof OrdPolynomialLocalization.proof ℂ n J W ℓ hJ.isHomog (hhom W hWm) hJW hℓW
      (linForm u) 1 (ChartLocDomain.linForm_isHomogeneous u)
    have e₃ := LocalMultOrd.proof _ (J ⊔ L) (W ⊔ L) (linForm u) (hK' ▸ hmin W hW)
    have e₄ := ord_atPrime_congr hmapeq (Ideal.Quotient.mk (J ⊔ L) (linForm u))
    exact_mod_cast e₃.trans (e₄.trans (e₂.symm.trans e₁.symm))
end SliceComponents
end GroundTheory.Heights₂.Heights
