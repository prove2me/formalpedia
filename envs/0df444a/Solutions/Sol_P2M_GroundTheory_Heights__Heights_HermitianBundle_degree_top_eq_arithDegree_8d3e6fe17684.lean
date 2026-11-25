-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_top_eq_arithDegree_8d3e6fe17684
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:48.41159+00:00
-- url     : https://prove2.me/submissions/e9bb7443-9e02-4ba5-b4ba-2c322fcea8fa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DegreeTopEqArithDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_eq_of_linearIndependent_05efcbd2008c


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
open NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace HermitianBundle
theorem _root_.solution {K : Type*} [Field K] [NumberField K]
    (E : HermitianBundle K) : E.degree ⊤ = E.arithDegree := by
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := E.carrier)
  let s' : Fin (Module.finrank (𝓞 K) E.carrier) → (⊤ : Submodule (𝓞 K) E.carrier) :=
    fun i ↦ ⟨s i, Submodule.mem_top⟩
  have hs' : LinearIndependent (𝓞 K) s' :=
    LinearIndependent.of_comp (⊤ : Submodule (𝓞 K) E.carrier).subtype hs
  have hcard : Fintype.card (Fin (Module.finrank (𝓞 K) E.carrier)) = E.rank ⊤ := by
    rw [Fintype.card_fin, HermitianBundle.rank, finrank_top]
  rw [E.degree_eq_of_linearIndependent ⊤ hs' hcard, HermitianBundle.arithDegree,
    arithDegree_eq E.metric hs (Fintype.card_fin _), GroundTheory.Heights₂.Heights.degreeWith]
  have hmap : (Submodule.span (𝓞 K) (Set.range s')).map
      (Submodule.topEquiv : (⊤ : Submodule (𝓞 K) E.carrier) ≃ₗ[𝓞 K] E.carrier).toLinearMap =
      Submodule.span (𝓞 K) (Set.range s) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [Nat.card_congr (Submodule.Quotient.equiv _ _ Submodule.topEquiv hmap).toEquiv]
end HermitianBundle
end GroundTheory.Heights₂.Heights
