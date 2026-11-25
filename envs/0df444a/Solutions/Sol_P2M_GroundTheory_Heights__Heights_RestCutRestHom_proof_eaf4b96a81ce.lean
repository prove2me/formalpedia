-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutRestHom_proof_eaf4b96a81ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:55.09931+00:00
-- url     : https://prove2.me/submissions/f3fb83f6-8d18-431c-bd47-f20289e05698

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutRestHom
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_isHomogeneous_vandermondeOf_c370fdda67bb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_add_mul_add_sub_one_4f89760d3092
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_sum_card_Ioi_mul_two_69f2c1bd387d


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
namespace GroundTheory.Heights₂.Heights
namespace RestCutRestHom
theorem _root_.solution : RestCutRestHom.Statement := by
  intro f r a c

  have hy : ∀ τ i, (RestTerms.yRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_C_mul_X _ _
  have hz : ∀ τ i, (RestTerms.zRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_X _ _

  have hμ : (RestTerms.smallBlockMu f r a c).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sum _ _ _ fun i _ => hy τ i

  set dy := ∑ i : Fin r, (Finset.Ioi i).card with hdy
  set dz := ∑ i : Fin a, (Finset.Ioi i).card with hdz
  have hfib : (RestTerms.fibreClass f r a c).IsHomogeneous (f * (dy + dz)) := by
    have h := IsHomogeneous.prod (Finset.univ : Finset (Fin f))
      (fun τ => RestTerms.vandermondeOf (RestTerms.yRoot f r a c τ) *
        RestTerms.vandermondeOf (RestTerms.zRoot f r a c τ)) (fun _ => dy + dz)
      fun τ _ => (KRest.isHomogeneous_vandermondeOf _ (hy τ)).mul
        (KRest.isHomogeneous_vandermondeOf _ (hz τ))
    simpa [RestTerms.fibreClass, Finset.sum_const, Finset.card_univ, Fintype.card_fin] using h

  have hdy2 : dy * 2 = r * (r - 1) := KRest.sum_card_Ioi_mul_two r
  have hdz2 : dz * 2 = a * (a - 1) := KRest.sum_card_Ioi_mul_two a
  have hdeg : 1 * (f * (r * a)) + f * (dy + dz) = RestTerms.topDegree f (r + a) := by
    have hS : (r + a) * (r + a - 1) / 2 = r * a + (dy + dz) := by
      rw [KRest.add_mul_add_sub_one, ← hdy2, ← hdz2]
      have : dy * 2 + dz * 2 + 2 * (r * a) = 2 * (r * a + (dy + dz)) := by ring
      rw [this, Nat.mul_div_cancel_left _ two_pos]
    rw [RestTerms.topDegree, hS]
    ring
  refine ⟨?_, ?_⟩
  · rw [← hdeg]
    exact (hμ.pow _).mul hfib
  · have h := (hμ.pow (f * (r * a) + 1)).mul hfib
    have he : 1 * (f * (r * a) + 1) + f * (dy + dz) = RestTerms.topDegree f (r + a) + 1 := by
      rw [← hdeg]; ring
    rw [he] at h
    exact h
end RestCutRestHom
end GroundTheory.Heights₂.Heights
