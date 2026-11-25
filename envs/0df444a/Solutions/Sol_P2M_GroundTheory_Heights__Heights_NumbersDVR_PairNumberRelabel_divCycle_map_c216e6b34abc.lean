-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_divCycle_map_c216e6b34abc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:26:41.51001+00:00
-- url     : https://prove2.me/submissions/a6bb8ca4-f7d2-4c0f-a082-b8ba00a56a18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_isRelevant_map_iff_bbef0f1ec389
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isRelevant_map_iff_44c6feca16d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_length_map_8e436c9e22c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_map_mem_minimalPrimes_iff_08aaf3425488


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
variable {K₁ K₂ : Type} {ι₁ : K₁ → Type} {ι₂ : K₂ → Type} {R : Type} [CommRing R]
  (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k))
variable (e : K₁ ≃ K₂)
namespace GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
theorem _root_.solution (hσ : ∀ v, (σ v).1 = e v.1) (P W : Ideal (MRing ι₁ R)) (f : MRing ι₁ R) :
    divCycle (P.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R)) (rename σ f)
        (W.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R)) = divCycle P f W := by
  have hsup : P.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R) ⊔ Ideal.span {rename σ f} =
      (P ⊔ Ideal.span {f}).map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R) := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    rfl
  have hiff : (W.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R) ∈
        (P.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R) ⊔ Ideal.span {rename σ f}).minimalPrimes ∧
        IsRelevant (W.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R))) ↔
      (W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W) := by
    rw [hsup]
    exact and_congr (GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel.map_mem_minimalPrimes_iff _)
      (isRelevant_map_iff σ e hσ W)
  unfold divCycle
  by_cases h : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W
  · rw [dif_pos h, dif_pos (hiff.2 h)]
    have : W.IsPrime := h.1.1.1
    have : (W.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R)).IsPrime := (hiff.2 h).1.1.1
    have hl := GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel.length_map (ren (R := R) σ) P W
      (le_sup_left.trans h.1.1.2) f
    unfold multAt
    exact congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) hl
  · rw [dif_neg h, dif_neg (mt hiff.1 h)]
end GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
