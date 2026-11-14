-- Prove2me | solution 1 for StabilityDichotomies.Solvability.delete_occurrence_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:26:45.87158+00:00
-- url     : https://prove2.me/submissions/fdffc84f-0394-4966-9414-c321960401e1

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability

private def atMultiset {α : Type} (s : Multiset α) (i : Fin s.card) : α :=
  s.toList.get ⟨i.val, by simpa using i.isLt⟩

private theorem cast_value {α : Type} {s t : Multiset α} (h : s = t) (v : s.ToType) :
    ((Equiv.cast (congrArg Multiset.ToType h) v).1) = v.1 := by
  subst t
  rfl

private theorem multiset_equiv_index {α : Type} (s : Multiset α) :
    ∃ e : Fin s.card ≃ s.ToType, ∀ i, (e i).1 = atMultiset s i := by
  classical
  let idx : Multiset (Fin s.card) := (Finset.univ : Finset (Fin s.card)).val
  have idxeq : idx = ↑(List.finRange s.card) := by
    have hn : (↑(List.finRange s.card) : Multiset (Fin s.card)).Nodup := by
      simpa using List.nodup_finRange s.card
    apply (Multiset.Nodup.ext Finset.univ.nodup hn).2
    intro i
    simp [idx]
  have hm : idx.map (atMultiset s) = s := by
    rw [idxeq, Multiset.map_coe, ← List.ofFn_eq_map]
    have hh : List.ofFn (atMultiset s) = s.toList := by
      apply List.ext_getElem
      · simp
      · intro i hi hj
        simp [atMultiset]
    rw [hh, Multiset.coe_toList]
  let eidx : Fin s.card ≃ idx.ToType :=
    { toFun := fun i => ⟨i, ⟨0, by simp [idx]⟩⟩
      invFun := fun x => x.1
      left_inv := by intro i; rfl
      right_inv := by
        rintro ⟨i, k⟩
        rcases k with ⟨k, hk⟩
        have hk0 : k = 0 := by simp [idx] at hk; omega
        subst k
        rfl }
  let emap : idx.ToType ≃ (idx.map (atMultiset s)).ToType := idx.mapEquiv (atMultiset s)
  let ecast : (idx.map (atMultiset s)).ToType ≃ s.ToType := Equiv.cast (congrArg Multiset.ToType hm)
  refine ⟨eidx.trans (emap.trans ecast), ?_⟩
  intro i
  change ((ecast (emap (eidx i))).1) = atMultiset s i
  rw [cast_value hm]
  exact idx.mapEquiv_apply (atMultiset s) (eidx i)

private theorem cons_equiv_value {α : Type} (c : α) (s : Multiset α)
    (z : (c ::ₘ s).ToType) :
    (Multiset.consEquiv z).elim c (fun u => u.1) = z.1 := by
  let e := (Multiset.consEquiv : (c ::ₘ s).ToType ≃ Option s.ToType)
  obtain ⟨o, ho⟩ := e.symm.surjective z
  subst z
  change (e (e.symm o)).elim c (fun u => u.1) = (e.symm o).1
  rw [e.apply_symm_apply]
  cases o with
  | none => simp [e]
  | some x => simp [e]

private theorem erase_occurrence_equivalence {α : Type} (s : Multiset α) (c : α) (hc : c ∈ s) :
    ∃ e : Fin s.card ≃ Option (Fin (s.erase c).card),
      ∀ j, (e j).elim c (atMultiset (s.erase c)) = atMultiset s j := by
  obtain ⟨es, hs⟩ := multiset_equiv_index s
  obtain ⟨et, ht⟩ := multiset_equiv_index (s.erase c)
  have hcons : c ::ₘ s.erase c = s := Multiset.cons_erase hc
  let cast : s.ToType ≃ (c ::ₘ s.erase c).ToType := Equiv.cast (congrArg Multiset.ToType hcons.symm)
  let e : Fin s.card ≃ Option (Fin (s.erase c).card) :=
    es.trans (cast.trans (Multiset.consEquiv.trans (Equiv.optionCongr et.symm)))
  refine ⟨e, ?_⟩
  intro j
  have hv := cons_equiv_value c (s.erase c) (cast (es j))
  have hcast : (cast (es j)).1 = (es j).1 := cast_value hcons.symm (es j)
  have hoption (o : Option (s.erase c).ToType) :
      ((Equiv.optionCongr et.symm) o).elim c (atMultiset (s.erase c)) = o.elim c (fun z => z.1) := by
    cases o with
    | none => rfl
    | some z => simp only [Equiv.optionCongr_apply, Option.map_some, Option.elim_some]
                simpa using (ht (et.symm z)).symm
  change ((Equiv.optionCongr et.symm) (Multiset.consEquiv (cast (es j)))).elim c
    (atMultiset (s.erase c)) = atMultiset s j
  rw [hoption, hv, hcast, hs]

theorem solution {Γ : Language} {V : Type} (I : Instance Γ V)
    (c : Constraint Γ V) (hc : c ∈ I.constraints) :
    ∃ e : Fin I.constraints.card ≃ Option (Fin (I.delete c).constraints.card),
      ∀ j, (e j).elim c (occurrenceAt (I.delete c)) = occurrenceAt I j := by
  change ∃ e : Fin I.constraints.card ≃ Option (Fin (I.constraints.erase c).card),
    ∀ j, (e j).elim c (atMultiset (I.constraints.erase c)) = atMultiset I.constraints j
  exact erase_occurrence_equivalence I.constraints c hc
