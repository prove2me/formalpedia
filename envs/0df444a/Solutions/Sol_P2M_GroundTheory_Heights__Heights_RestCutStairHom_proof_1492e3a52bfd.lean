-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutStairHom_proof_1492e3a52bfd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:02:23.773968+00:00
-- url     : https://prove2.me/submissions/49b891c7-2c36-4ddb-8473-82af3f55b891

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutStairHom
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_sum_fin_val_mul_two_327ec1f0d7fe


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
namespace RestCutStairHom
theorem _root_.solution : RestCutStairHom.Statement := by
  intro f N
  have hsum : (∑ i : Fin N, (i : ℕ)) = N * (N - 1) / 2 :=
    (Nat.div_eq_of_eq_mul_left (by norm_num) (KRest.sum_fin_val_mul_two N).symm).symm
  have hinner : ∀ τ : Fin f,
      (∏ i : Fin N, (X (τ, i) : RestTerms.RootRing f N) ^ (i : ℕ)).IsHomogeneous
        (∑ i : Fin N, (i : ℕ)) :=
    fun τ => IsHomogeneous.prod _ _ _ fun i _ => isHomogeneous_X_pow _ _
  have h := IsHomogeneous.prod (Finset.univ : Finset (Fin f)) _ _ fun τ _ => hinner τ
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  unfold restStair RestTerms.topDegree
  rw [← hsum]
  exact h
end RestCutStairHom
end GroundTheory.Heights₂.Heights
