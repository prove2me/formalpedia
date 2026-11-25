-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_ChainSum_deg_eq_of_linearEquiv_897173931eb1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:52:54.177807+00:00
-- url     : https://prove2.me/submissions/1829150f-d610-4f76-b89d-4f53b92b72a7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PChainSum
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
open NumberField
open GroundTheory.Heights₂.Heights
universe u v
noncomputable section
open GroundTheory.Heights₂.Heights.LatticeLemmas.ChainSum
namespace GroundTheory.Heights₂.Heights.LatticeLemmas.ChainSum
theorem _root_.solution {K : Type u} [Field K] [NumberField K] (A B : HermitianBundle.{v} K)
    (φ : A.carrier ≃ₗ[𝓞 K] B.carrier)
    (hg : ∀ (σ : K →+* ℂ) (n : ℕ) (s : Fin n → A.carrier),
      GroundTheory.Heights₂.Heights.gramDet A.metric σ s =
        GroundTheory.Heights₂.Heights.gramDet B.metric σ (fun i ↦ φ (s i))) :
    A.deg = B.deg := by
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := A.carrier)
  have ht : LinearIndependent (𝓞 K) (fun i ↦ φ (s i)) := hs.map' φ.toLinearMap φ.ker
  have hcard : Fintype.card (Fin (Module.finrank (𝓞 K) A.carrier)) =
      Module.finrank (𝓞 K) B.carrier := by
    rw [Fintype.card_fin]
    exact φ.finrank_eq
  simp only [HermitianBundle.deg, HermitianBundle.arithDegree]
  rw [arithDegree_eq A.metric hs (Fintype.card_fin _), arithDegree_eq B.metric ht hcard]
  simp only [GroundTheory.Heights₂.Heights.degreeWith, hg]
  have hmap : (Submodule.span (𝓞 K) (Set.range s)).map φ.toLinearMap =
      Submodule.span (𝓞 K) (Set.range fun i ↦ φ (s i)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [Nat.card_congr (Submodule.Quotient.equiv _ _ φ hmap).toEquiv]
end GroundTheory.Heights₂.Heights.LatticeLemmas.ChainSum
