-- Prove2me | solution 1 for SetDefinedGraphs.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:21:50.168095+00:00
-- url     : https://prove2.me/submissions/bee266a1-d119-4825-9929-001dc8f02264

import Mathlib
import Definitions.Def_SetDefinedGraphs_DigraphBasics
import Definitions.Def_SetDefinedGraphs_realisation
import Definitions.Def_SetDefinedGraphs_VectorSets
import Definitions.Def_SetDefinedGraphs_Clauses

section
set_option autoImplicit false
namespace SetDefinedGraphs
theorem chk_lemma_3_4 {d : ℕ} (C : Clause (Fin d)) (I : Set (Fin d)) (V : Set (Fin d → ℕ))
    (hV : ∀ u ∈ V, ∀ v ∈ V, u ≠ v → restrictVec I u = restrictVec I v → ¬ C.Holds (eqPattern u v)) :
    Homomorphic (realisation C.toFun V) (realisation (C.restrict I).toFun (restrictSet I V)) := by
  classical
  refine ⟨fun u => ⟨restrictVec I u.1, u.1, u.2, rfl⟩, ?_⟩
  intro u w ⟨hne, hadj⟩
  have hH : C.Holds (eqPattern u.1 w.1) := by
    simpa [Clause.toFun] using hadj
  refine ⟨?_, ?_⟩
  · intro h
    have h' : restrictVec I u.1 = restrictVec I w.1 := congrArg Subtype.val h
    exact hV u.1 u.2 w.1 w.2 (fun e => hne (Subtype.ext e)) h' hH
  · simp only [Clause.toFun, decide_eq_true_eq]
    intro i j
    exact hH i.1 j.1
end SetDefinedGraphs
end

theorem solution : type_of% @SetDefinedGraphs.chk_lemma_3_4 := @SetDefinedGraphs.chk_lemma_3_4
