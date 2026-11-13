-- Prove2me | solution 1 for SetDefinedGraphs.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:21:49.608431+00:00
-- url     : https://prove2.me/submissions/0fbe2019-a72f-4175-ac91-e598226b45c8

import Mathlib
import Definitions.Def_SetDefinedGraphs_realisation
import Definitions.Def_SetDefinedGraphs_VectorSets
import Definitions.Def_SetDefinedGraphs_Clauses

section
set_option autoImplicit false
namespace SetDefinedGraphs.Dev.L42
open SetDefinedGraphs

theorem key {d : ℕ} (P : Setoid (Fin d)) (C : FullClause (Fin d)) (hC : IsPCompatible P C)
    {i i' j j' : Fin d} (hi : P.r i i') (hj : P.r j j') (h : C i j = true) : C i' j' = true := by
  have h1 : C i j' = true := by
    rcases hC.1 i with hf | ⟨k, hk⟩
    · rw [hf j] at h; exact absurd h (by simp)
    · have := (hk j).1 h
      exact (hk j').2 (P.trans (P.symm hj) this)
  rcases hC.2 j' with hf | ⟨k, hk⟩
  · rw [hf i] at h1; exact absurd h1 (by simp)
  · have := (hk i).1 h1
    exact (hk i').2 (P.trans (P.symm hi) this)

theorem key' {d : ℕ} (P : Setoid (Fin d)) (C : FullClause (Fin d)) (hC : IsPCompatible P C)
    {i i' j j' : Fin d} (hi : P.r i i') (hj : P.r j j') : C i j = C i' j' := by
  rw [Bool.eq_iff_iff]
  exact ⟨key P C hC hi hj, key P C hC (P.symm hi) (P.symm hj)⟩

theorem rep {d : ℕ} (P : Setoid (Fin d)) (i : Fin d) :
    ∃ m, P.r i m ∧ m ∈ leastElems P := by
  classical
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun j => P.r i j)) id
    ⟨i, by simp [P.refl]⟩
  refine ⟨m, by simpa using hm, fun j hj => ?_⟩
  exact hmin j (by simp; exact P.trans (by simpa using hm) hj)
end SetDefinedGraphs.Dev.L42
namespace SetDefinedGraphs
open SetDefinedGraphs.Dev.L42 in
theorem chk_lemma_4_2 {d : ℕ} (P : Setoid (Fin d)) (C : FullClause (Fin d)) (hC : IsPCompatible P C)
    (u w : Fin d → ℕ) (hu : IsPHomogeneousVec P u) (hw : IsPHomogeneousVec P w) :
    eqPattern u w = C ↔
      eqPattern (restrictVec (leastElems P) u) (restrictVec (leastElems P) w) =
        fullRestrict C (leastElems P) := by
  constructor
  · intro h
    funext i j
    have := congrFun (congrFun h i.1) j.1
    simp only [eqPattern, restrictVec, fullRestrict] at this ⊢
    exact this
  · intro h
    funext i j
    obtain ⟨ri, hri, hriI⟩ := rep P i
    obtain ⟨rj, hrj, hrjI⟩ := rep P j
    have h1 := congrFun (congrFun h ⟨ri, hriI⟩) ⟨rj, hrjI⟩
    simp only [eqPattern, restrictVec, fullRestrict] at h1
    have e1 : u i = u ri := (hu _ _).2 hri
    have e2 : w j = w rj := (hw _ _).2 hrj
    have : eqPattern u w i j = decide (u ri = w rj) := by
      simp [eqPattern, e1, e2]
    rw [this]
    have h1' : decide (u ri = w rj) = C ri rj := by convert h1; congr
    exact h1'.trans (key' P C hC hri hrj).symm
end SetDefinedGraphs
end

theorem solution : type_of% @SetDefinedGraphs.chk_lemma_4_2 := @SetDefinedGraphs.chk_lemma_4_2
