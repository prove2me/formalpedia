-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_arithDegree_congr_5fb6b845d5f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:39:05.159466+00:00
-- url     : https://prove2.me/submissions/8e087daf-5203-4c23-a1bf-0e439b99c124

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_finrank_eq_7a942c89c61a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField IsDedekindDomain TensorProduct ComplexAt
open GroundTheory.Heights₂.Heights
universe u v
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {E E' : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] [AddCommGroup E'] [Module (𝓞 K) E'] [Module.Finite (𝓞 K) E']
  [Module.Projective (𝓞 K) E']
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution (h : HermitianMetric K E) (h' : HermitianMetric K E') (e : E' ≃ₗ[𝓞 K] E)
    (he : ∀ (σ : K →+* ℂ) (x y : E'), (h'.form σ).inner ((1 : ComplexAt σ) ⊗ₜ x) (1 ⊗ₜ y) =
      (h.form σ).inner ((1 : ComplexAt σ) ⊗ₜ e x) (1 ⊗ₜ e y)) :
    arithDegree h' = arithDegree h := by
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := E')
  have hs' : LinearIndependent (𝓞 K) (e ∘ s) := hs.map' e.toLinearMap e.ker
  rw [arithDegree_eq h' hs (Fintype.card_fin _),
    arithDegree_eq h hs' (by rw [Fintype.card_fin, e.finrank_eq])]
  unfold degreeWith
  congr 1
  · congr 2
    apply Nat.card_congr
    refine (Submodule.Quotient.equiv _ _ e ?_).toEquiv
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  · congr 2
    funext σ
    congr 1
    unfold gramDet
    congr 3
    ext i j
    exact he σ (s i) (s j)
end GroundTheory.Heights₂.Heights.LatticeLemmas
