-- Prove2me | solution 1 for Reduce.push_back_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:09:54.28066+00:00
-- url     : https://prove2.me/submissions/ea682999-6627-4ae7-b81b-5a898dd5451d

import Definitions.Def_Bdd_Reduce_State
import Definitions.Def_Bdd_Reduce_Populate
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_RawBdd_cook_aux
import Theorems.Thm_RawBdd_cook_inj
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
open RawBdd
open Reduce
namespace Reduce
theorem _root_.solution {n s : Nat} {v : Vector (RawNode n) s} {N : RawNode n}
    {hh  : ∀ k : Fin s,       v[k].Bounded k}
    {hh' : ∀ k : Fin (s + 1), (v.push N)[k].Bounded k}
    {p : RawPointer} (hp : p.Bounded s) {hp' : p.Bounded (s + 1)} :
    ∀ j : Fin (s + 1),
      Pointer.Reachable (cook_heap (v.push N) hh') (p.cook hp') (.node j) →
      ∃ hj : j.1 < s,
        Pointer.Reachable (cook_heap v hh) (p.cook hp) (.node ⟨j.1, hj⟩) := by
  suffices h : ∀ q : Pointer (s + 1),
      Pointer.Reachable (cook_heap (v.push N) hh') (p.cook hp') q →
      ∀ j : Fin (s + 1), q = .node j →
      ∃ hj : j.1 < s,
        Pointer.Reachable (cook_heap v hh) (p.cook hp) (.node ⟨j.1, hj⟩) from
    fun j hreach => h _ hreach j rfl
  intro q hq
  have cook_inr_node : ∀ (jj : Fin (s+1)) (bnd : RawPointer.Bounded (s+1) (.inr jj.1)),
      RawPointer.cook (.inr jj.1) bnd = .node jj := fun jj _ => by
    simp only [RawPointer.cook, Fin.eta]
  induction hq with
  | refl =>
    intro j hj
    have hp_eq : p = .inr j.1 :=
      cook_inj (hj.trans (cook_inr_node j (fun h => by injection h; omega)).symm)
    have hj_lt : j.1 < s := hp hp_eq
    have hcook : p.cook hp = .node ⟨j.1, hj_lt⟩ := by
      subst hp_eq; simp [RawPointer.cook]
    exact ⟨hj_lt, hcook ▸ .refl⟩
  | tail hprev edge ih =>
    intro j hj; subst hj
    cases edge with
    | low h =>
      rename_i k
      simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn, RawNode.cook] at h
      have hlo : (v.push N)[k.1].lo = .inr j.1 :=
        cook_inj (h.trans (cook_inr_node j (fun h => by injection h; omega)).symm)
      have hj_lt_k : j.1 < k.1 :=
        (hh' k).1 (show (v.push N)[k].lo = .inr j.1 by simp [Fin.getElem_fin, hlo] <;> rfl)
      obtain ⟨hk_lt, hk_reach⟩ := ih k rfl
      have hj_lt : j.1 < s := Nat.lt_trans hj_lt_k hk_lt
      refine ⟨hj_lt, .tail hk_reach (Edge.low ?_)⟩
      simp_rw [Vector.getElem_push_lt hk_lt] at h
      simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn, RawNode.cook]
      exact cook_aux h (hj := hj_lt)
        (h1 := RawPointer.bounded_of_le (hh ⟨k.1, hk_lt⟩).1 (by omega))
        (h2 := RawPointer.bounded_of_le (hh ⟨k.1, hk_lt⟩).1 (by omega))
    | high h =>
      rename_i k
      simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn, RawNode.cook] at h
      have hhi : (v.push N)[k.1].hi = .inr j.1 :=
        cook_inj (h.trans (cook_inr_node j (fun h => by injection h; omega)).symm)
      have hj_lt_k : j.1 < k.1 :=
        (hh' k).2 (show (v.push N)[k].hi = .inr j.1 by simp [Fin.getElem_fin, hhi] <;> rfl)
      obtain ⟨hk_lt, hk_reach⟩ := ih k rfl
      have hj_lt : j.1 < s := Nat.lt_trans hj_lt_k hk_lt
      refine ⟨hj_lt, .tail hk_reach (Edge.high ?_)⟩
      simp_rw [Vector.getElem_push_lt hk_lt] at h
      simp only [cook_heap, Fin.getElem_fin, Vector.getElem_ofFn, RawNode.cook]
      exact cook_aux h (hj := hj_lt)
        (h1 := RawPointer.bounded_of_le (hh ⟨k.1, hk_lt⟩).2 (by omega))
        (h2 := RawPointer.bounded_of_le (hh ⟨k.1, hk_lt⟩).2 (by omega))
end Reduce
