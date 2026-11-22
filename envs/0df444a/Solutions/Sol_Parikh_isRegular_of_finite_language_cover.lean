-- Prove2me | solution 1 for Parikh.isRegular_of_finite_language_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:47:59.065947+00:00
-- url     : https://prove2.me/submissions/e408c358-b225-4da5-aa81-9bc624a2d7dd

module
public import Mathlib.Computability.DFA
public import Mathlib.Computability.NFA
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata

set_option autoImplicit true
@[expose] public section
public section
open scoped Computability
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution (L : Language T)
    (F : Set (Language T)) (hF : F.Finite) (hL : L ∈ F)
    (hcover : ∀ K ∈ F, ∀ a w, a :: w ∈ K →
      ∃ J ∈ F, w ∈ J ∧ ∀ v ∈ J, a :: v ∈ K) : L.IsRegular := by
  classical
  let : Fintype F := hF.fintype
  let M : NFA T F :=
    { step := fun K a => {J | ∀ v ∈ J.val, a :: v ∈ K.val}
      start := {⟨L, hL⟩}
      accept := {K | [] ∈ K.val} }
  have hcons (K : F) (a : T) (w : List T) :
      a :: w ∈ K.val ↔ ∃ J ∈ M.step K a, w ∈ J.val := by
    constructor
    · intro hw
      obtain ⟨J, hJ, hw, hs⟩ := hcover K.val K.prop a w hw
      exact ⟨⟨J, hJ⟩, hs, hw⟩
    · rintro ⟨J, hs, hw⟩
      exact hs w hw
  have heval (w : List T) (S : Set F) :
      (∃ K ∈ M.evalFrom S w, [] ∈ K.val) ↔ ∃ K ∈ S, w ∈ K.val := by
    induction w generalizing S with
    | nil => rfl
    | cons a w ih =>
      rw [NFA.evalFrom_cons, ih]
      constructor
      · rintro ⟨J, hJ, hw⟩
        obtain ⟨K, hK, hs⟩ := NFA.mem_stepSet.mp hJ
        exact ⟨K, hK, (hcons K a w).mpr ⟨J, hs, hw⟩⟩
      · rintro ⟨K, hK, hw⟩
        obtain ⟨J, hs, hw⟩ := (hcons K a w).mp hw
        exact ⟨J, NFA.mem_stepSet.mpr ⟨K, hK, hs⟩, hw⟩
  have hM : M.accepts = L := by
    ext w
    rw [NFA.mem_accepts]
    change (∃ K, [] ∈ K.val ∧ K ∈ M.evalFrom {⟨L, hL⟩} w) ↔ w ∈ L
    constructor
    · rintro ⟨K, ha, hs⟩
      obtain ⟨J, hJ, hw⟩ := (heval w {⟨L, hL⟩}).mp ⟨K, hs, ha⟩
      have hJ : J = ⟨L, hL⟩ := Set.mem_singleton_iff.mp hJ
      cases hJ
      exact hw
    · intro hw
      obtain ⟨K, hs, ha⟩ := (heval w {⟨L, hL⟩}).mpr
        ⟨⟨L, hL⟩, Set.mem_singleton _, hw⟩
      exact ⟨K, ha, hs⟩
  exact Language.isRegular_iff.mpr
    ⟨Set F, inferInstance, M.toDFA, M.toDFA_correct.trans hM⟩
end Parikh
