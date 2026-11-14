-- Prove2me | solution 1 for StabilityDichotomies.Solvability.delete_thinned_mask_alignment
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:26:47.771597+00:00
-- url     : https://prove2.me/submissions/6a74cdf0-147a-4258-a03a-b81666d1fa4e

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability

private theorem filter_map_as_sum {α β : Type} (mask : α → Bool) (l : List (α × β)) :
    (↑((l.filter fun q => mask q.1).map Prod.snd) : Multiset β) =
      (l.map fun q => if mask q.1 then ({q.2} : Multiset β) else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hm : mask a.1 with
    | false => simpa [hm] using ih
    | true =>
      simp only [List.filter_cons, hm, ↓reduceIte, List.map_cons, List.sum_cons]
      change a.2 ::ₘ (↑((l.filter fun q => mask q.1).map Prod.snd)) =
        {a.2} + (l.map fun q => if mask q.1 then ({q.2} : Multiset β) else 0).sum
      rw [ih, Multiset.singleton_add]

private theorem thinned_as_sum {Γ : Language} {V : Type} (I : Instance Γ V)
    (mask : Fin I.constraints.card → Bool) :
    (thinnedInstance I mask).constraints = ∑ j : Fin I.constraints.card,
      if mask j then ({occurrenceAt I j} : Multiset (Constraint Γ V)) else 0 := by
  change (↑(((List.ofFn fun i : Fin I.constraints.card => (i, occurrenceAt I i)).filter
      (fun p => mask p.1)).map Prod.snd) : Multiset (Constraint Γ V)) = _
  rw [filter_map_as_sum, List.map_ofFn, List.sum_ofFn]
  rfl

theorem solution {Γ : Language} {V : Type} (I : Instance Γ V)
    (c : Constraint Γ V) (hc : c ∈ I.constraints)
    (e : Fin I.constraints.card ≃ Option (Fin (I.delete c).constraints.card))
    (he : ∀ j, (e j).elim c (occurrenceAt (I.delete c)) = occurrenceAt I j)
    (mask : Fin I.constraints.card → Bool) :
    thinnedInstance I (Function.update mask (e.symm none) false) =
      thinnedInstance (I.delete c) (fun k => mask (e.symm (some k))) := by
  have hshape (z : Option (Fin (I.delete c).constraints.card)) :
      (if Function.update mask (e.symm none) false (e.symm z) then
        ({occurrenceAt I (e.symm z)} : Multiset (Constraint Γ V)) else 0) =
      z.elim 0 (fun k => if mask (e.symm (some k)) then
        ({occurrenceAt (I.delete c) k} : Multiset (Constraint Γ V)) else 0) := by
    cases z with
    | none => simp
    | some k =>
      have hne : e.symm (some k) ≠ e.symm none := by
        intro h
        have := congrArg e h
        simpa using this
      have hv : occurrenceAt I (e.symm (some k)) = occurrenceAt (I.delete c) k := by
        have h := he (e.symm (some k))
        simpa using h.symm
      simp [Function.update, hne, hv]
  have hs : (thinnedInstance I (Function.update mask (e.symm none) false)).constraints =
      (thinnedInstance (I.delete c) (fun k => mask (e.symm (some k)))).constraints := by
    rw [thinned_as_sum, thinned_as_sum]
    rw [← e.symm.sum_comp]
    simp_rw [hshape]
    simp [Fintype.sum_option]
  exact congrArg Instance.mk hs
