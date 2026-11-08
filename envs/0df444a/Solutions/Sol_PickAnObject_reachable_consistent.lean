-- Prove2me | solution 1 for PickAnObject.reachable_consistent
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:01:43.136497+00:00
-- url     : https://prove2.me/submissions/2c9db6a6-53fb-4264-989d-962c24cdcf6b

import Mathlib
import Definitions.Def_PickAnObject_Model

namespace Aux_PAO_reach
open PickAnObject

theorem ofKey_lt {Obj : Type*} [Fintype Obj] [DecidableEq Obj] (f : Option Obj → ℕ)
    (hf : Function.Injective f) (o o' : Option Obj) :
    ofKey f hf o < ofKey f hf o' ↔ f o < f o' := by
  letI : LinearOrder (Option Obj) := LinearOrder.lift' f hf
  exact (Fintype.orderIsoFinOfCardEq (Option Obj) rfl).symm.lt_iff_lt

def Inv {Obj : Type*} (l : ChoiceHistory Obj) : Prop :=
  ∀ j (hj : j < l.length), l[j].2 ∈ l[j].1 ∧
    ∀ o ∈ l[j].1, ∀ j' (hj' : j' < j), o ≠ (l[j']'(by omega)).2

theorem inv_reach {A Obj : Type*} [Fintype Obj] [DecidableEq Obj] (S : MenuFunction A Obj)
    (hS : IsMenuFunction S) (h : CollectiveHistory A Obj) (hh : Reachable S h) :
    ∀ a, Inv (h a) := by
  induction hh with
  | init => intro a j hj; simp [emptyHistory] at hj
  | @step h c _ hc ih =>
    intro a
    unfold advance
    by_cases he : S h a = ∅
    · rw [if_pos he]; exact ih a
    · rw [if_neg he]
      have hne : (S h a).Nonempty := Finset.nonempty_iff_ne_empty.mpr he
      have hca := hc a hne
      intro j hj
      rw [List.length_append, List.length_singleton] at hj
      by_cases hjl : j < (h a).length
      · rw [List.getElem_append_left hjl]
        obtain ⟨h1, h2⟩ := ih a j hjl
        refine ⟨h1, fun o ho j' hj' => ?_⟩
        rw [List.getElem_append_left (by omega)]
        exact h2 o ho j' hj'
      · have hjeq : j = (h a).length := by omega
        subst hjeq
        rw [List.getElem_append_right (by omega)]
        simp only [Nat.sub_self, List.getElem_cons_zero]
        refine ⟨hca, fun o ho j' hj' => ?_⟩
        rw [List.getElem_append_left hj']
        -- use the menu-function property with the last pair
        have hlen : 0 < (h a).length := by omega
        set J := (h a).length - 1 with hJ
        have hJl : J < (h a).length := by omega
        have hlast : (h a).getLast? = some ((h a)[J]) := by
          rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hJl]
        have hsub := hS.2 h a _ hlast ho
        rw [Finset.mem_erase] at hsub
        by_cases hj'J : j' = J
        · subst hj'J; exact hsub.1
        · exact (ih a J hJl).2 o hsub.2 j' (by omega)

end Aux_PAO_reach

open PickAnObject Aux_PAO_reach in
theorem solution {A Obj : Type*} [Fintype Obj] [DecidableEq Obj]
    (S : MenuFunction A Obj) (hS : IsMenuFunction S) (h : CollectiveHistory A Obj)
    (hh : Reachable S h) :
    ∃ P : Profile A Obj, ProfileConsistentWith P h := by
  have Q0 : Pref Obj := Fintype.equivFin _
  refine ⟨fun a => prefixPref ((h a).map Prod.snd) Q0, fun a => ?_⟩
  have hinv := inv_reach S hS h hh a
  set l := h a with hl
  set γ := l.map Prod.snd with hγ
  have hlenγ : γ.length = l.length := List.length_map _
  have hγj : ∀ j (hj : j < l.length), γ[j]'(by omega) = (l[j]).2 := by
    intro j hj; simp [hγ]
  have hnodup : γ.Nodup := by
    rw [List.nodup_iff_injective_get]
    intro ⟨i, hi⟩ ⟨i', hi'⟩ heq
    simp only [List.get_eq_getElem] at heq
    rw [hγj i (by omega), hγj i' (by omega)] at heq
    by_contra hne
    have hne' : i ≠ i' := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · exact (hinv i' (by omega)).2 _ (hinv i' (by omega)).1 i hlt heq.symm
    · exact (hinv i (by omega)).2 _ (hinv i (by omega)).1 i' hlt heq
  intro p hp o ho
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
  by_cases hoe : l[j].2 = o
  · right; exact hoe
  left
  show prefixPref γ Q0 (l[j]).2 < prefixPref γ Q0 o
  unfold prefixPref
  rw [ofKey_lt]
  have hcmem : (l[j]).2 ∈ γ := by rw [← hγj j hj]; exact List.getElem_mem _
  have hkey_c : prefixKey γ Q0 (l[j]).2 = j := by
    unfold prefixKey
    rw [if_pos hcmem, ← hγj j hj, hnodup.idxOf_getElem]
  rw [hkey_c]
  unfold prefixKey
  by_cases hoγ : o ∈ γ
  · rw [if_pos hoγ]
    obtain ⟨j', hj', hj'e⟩ := List.getElem_of_mem hoγ
    rw [← hj'e, hnodup.idxOf_getElem]
    rw [hlenγ] at hj'
    rw [hγj j' hj'] at hj'e
    rcases lt_trichotomy j' j with hlt | heq | hgt
    · exfalso; exact (hinv j hj).2 o ho j' hlt hj'e.symm
    · exfalso; subst heq; exact hoe hj'e
    · exact hgt
  · rw [if_neg hoγ]
    omega
