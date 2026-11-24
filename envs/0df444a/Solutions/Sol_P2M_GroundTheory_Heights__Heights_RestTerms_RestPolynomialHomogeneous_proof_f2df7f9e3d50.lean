-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_RestPolynomialHomogeneous_proof_f2df7f9e3d50
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:41:35.133803+00:00
-- url     : https://prove2.me/submissions/5d14705f-e140-406c-9bbe-1c24ecb7ffd8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PRestPolynomialHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_choose_two_add_d3d2161255a9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace RestPolynomialHomogeneous
theorem _root_.solution (h1 : VandermondeOfHomogeneous.Statement) :
    RestPolynomialHomogeneous.Statement := by
  intro f r a c
  have hy : ∀ τ i, (yRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_C_mul_X c.sign (yIndex f r a c τ i)
  have hz : ∀ τ i, (zRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_X ℚ (zIndex f r a c τ i)
  have hmu : (smallBlockMu f r a c).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sum _ _ _ fun i _ => hy τ i
  have hfib : (fibreClass f r a c).IsHomogeneous
      (∑ _τ : Fin f, (r * (r - 1) / 2 + a * (a - 1) / 2)) :=
    IsHomogeneous.prod _ _ _ fun τ _ =>
      (h1 _ ℚ r (yRoot f r a c τ) (hy τ)).mul (h1 _ ℚ a (zRoot f r a c τ) (hz τ))
  have hF := (hmu.pow (f * (r * a) + 1)).mul hfib
  have hdeg : 1 * (f * (r * a) + 1) + ∑ _τ : Fin f, (r * (r - 1) / 2 + a * (a - 1) / 2) =
      topDegree f (r + a) + 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, topDegree,
      choose_two_add]
    ring
  rw [← hdeg]
  exact hF
end RestPolynomialHomogeneous
end GroundTheory.Heights₂.Heights.RestTerms
