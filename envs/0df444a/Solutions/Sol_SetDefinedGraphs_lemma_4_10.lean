-- Prove2me | solution 1 for SetDefinedGraphs.lemma_4_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:21:50.764832+00:00
-- url     : https://prove2.me/submissions/fff1f14b-eda9-42c5-84d7-743b4cbf995e

import Mathlib
import Definitions.Def_SetDefinedGraphs_DigraphBasics
import Definitions.Def_SetDefinedGraphs_realisation
import Definitions.Def_SetDefinedGraphs_VectorSets
import Definitions.Def_SetDefinedGraphs_Clauses
import Definitions.Def_SetDefinedGraphs_Functional

section
set_option autoImplicit false
namespace SetDefinedGraphs
theorem chk_lemma_4_10 {d : ℕ} (D : FullClause (Fin d)) (hD : IsDiscreteClause D)
    (L : Finset (Fin d)) (hLD : L = loopCoords D)
    (V : Set (Fin d → ℕ)) (U : Set (Fin d → ℕ)) (hUV : U ⊆ V) (hU : IsLFunctional L U) :
    IsIndependent (realisation (dnfFun {D}) V) {x | x.1 ∈ U} := by
  classical
  obtain ⟨_, lam, hlamL, φ, hφ⟩ := hU
  intro a ha b hb ⟨hne, hadj⟩
  have hP : eqPattern a.1 b.1 = D := by
    simpa [dnfFun] using hadj
  have hLmem : ∀ i, i ∈ L ↔ D i i = true := by
    intro i; rw [hLD]; simp [loopCoords]
  have heq : ∀ i : L, a.1 i.1 = b.1 i.1 := by
    intro i
    have := congrFun (congrFun hP i.1) i.1
    have h2 : D i.1 i.1 = true := (hLmem i.1).1 i.2
    rw [← this] at h2
    simpa [eqPattern] using h2
  have h1 : a.1 lam = b.1 lam := by
    rw [hφ a.1 ha, hφ b.1 hb]
    congr 1
    funext i
    exact heq i
  have h3 := congrFun (congrFun hP lam) lam
  have h4 : D lam lam = true := by
    rw [← h3]; simp [eqPattern, h1]
  exact hlamL ((hLmem lam).2 h4)
end SetDefinedGraphs
end

theorem solution : type_of% @SetDefinedGraphs.chk_lemma_4_10 := @SetDefinedGraphs.chk_lemma_4_10
