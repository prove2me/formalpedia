-- Prove2me | solution 1 for TenChallenges.challenge_10_finite
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:30:37.393191+00:00
-- url     : https://prove2.me/submissions/4e90624c-b563-49b1-b567-cb502ee5627d

import Mathlib
import Definitions.Def_TenChallenges_Challenge_10
universe u v

namespace Aux_TC10

open Classical

variable {V : Type u} [Fintype V] (G : SimpleGraph V)

noncomputable def mono (c : V → Bool) (x y : V) : ℤ := if G.Adj x y ∧ c x = c y then 1 else 0

noncomputable def M (c : V → Bool) : ℤ := ∑ x, ∑ y, mono G c x y

noncomputable def E (c : V → Bool) (v y : V) : ℤ :=
  (if G.Adj v y ∧ c y ≠ c v then 1 else 0) - (if G.Adj v y ∧ c y = c v then 1 else 0)

theorem flip_diff (c : V → Bool) (v : V) :
    M G (Function.update c v (!c v)) - M G c = 2 * ∑ y, E G c v y := by
  set c' := Function.update c v (!c v) with hc'
  have hc'v : c' v = !c v := Function.update_self _ _ _
  have hc'o : ∀ x, x ≠ v → c' x = c x := fun x hx => Function.update_of_ne hx _ _
  have hD : ∀ x y, mono G c' x y - mono G c x y =
      if x = v then E G c v y else if y = v then E G c v x else 0 := by
    intro x y
    by_cases hx : x = v
    · subst hx
      rw [if_pos rfl]
      by_cases hy : y = x
      · subst hy
        simp [mono, E]
      · unfold mono E
        rw [hc'v, hc'o y hy]
        cases h1 : c x <;> cases h2 : c y <;> simp
    · rw [if_neg hx]
      by_cases hy : y = v
      · subst hy
        rw [if_pos rfl]
        unfold mono E
        rw [hc'v, hc'o x hx]
        have hadj : G.Adj x y ↔ G.Adj y x := G.adj_comm x y
        cases h1 : c x <;> cases h2 : c y <;> simp [hadj]
      · rw [if_neg hy]
        unfold mono
        rw [hc'o x hx, hc'o y hy]
        ring
  have hEv : E G c v v = 0 := by simp [E]
  unfold M
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, hD]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
  simp only [if_true]
  have h2 : ∑ x ∈ Finset.univ.erase v, ∑ y, (if x = v then E G c v y else
      if y = v then E G c v x else 0) = ∑ x ∈ Finset.univ.erase v, E G c v x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxv : x ≠ v := Finset.ne_of_mem_erase hx
    simp only [hxv, if_false]
    rw [Finset.sum_ite_eq']
    simp
  rw [h2, Finset.sum_erase _ hEv]
  ring

theorem exists_unfriendly [Nonempty V] : ∃ c : V → Bool, ∀ v,
    (Finset.univ.filter (fun w => G.Adj v w ∧ c w = c v)).card ≤
      (Finset.univ.filter (fun w => G.Adj v w ∧ c w ≠ c v)).card := by
  obtain ⟨c0, -, hmin⟩ := Finset.exists_min_image Finset.univ (M G) Finset.univ_nonempty
  refine ⟨c0, fun v => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hd := flip_diff G c0 v
  have hsum : ∑ y, E G c0 v y =
      ((Finset.univ.filter (fun w => G.Adj v w ∧ c0 w ≠ c0 v)).card : ℤ) -
        (Finset.univ.filter (fun w => G.Adj v w ∧ c0 w = c0 v)).card := by
    unfold E
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]
  have hm := hmin (Function.update c0 v (!c0 v)) (Finset.mem_univ _)
  have hlt' : ((Finset.univ.filter (fun w => G.Adj v w ∧ c0 w ≠ c0 v)).card : ℤ) <
      (Finset.univ.filter (fun w => G.Adj v w ∧ c0 w = c0 v)).card := by exact_mod_cast hlt
  linarith

end Aux_TC10

open Classical Aux_TC10 in
theorem solution : ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (r : Ordinal.{v}),
    PartitionerWins G (emptyPartition V) r := by
  intro V _ G r
  haveI := Fintype.ofFinite V
  by_cases hV : Nonempty V
  swap
  · rw [PartitionerWins]
    intro w
    exact absurd ⟨w⟩ hV
  obtain ⟨c, hc⟩ := exists_unfriendly G
  let F : V → Option Bool := fun w => some (c w)
  have hcard : ∀ (w : V) (b : Bool),
      Cardinal.mk (NeighColored G F w (some b)) =
        ((Finset.univ.filter (fun x => G.Adj w x ∧ c x = b)).card : Cardinal) := by
    intro w b
    unfold NeighColored
    rw [Cardinal.mk_fintype, Fintype.card_subtype]
    congr 2
    apply Finset.filter_congr
    intro x _
    simp [F, SimpleGraph.mem_neighborSet]
  have hunf : ∀ w, UnfriendlyAt G F w := by
    intro w
    refine ⟨c w, rfl, ?_⟩
    rw [hcard, hcard]
    have h := hc w
    have heq : (Finset.univ.filter (fun x => G.Adj w x ∧ c x = !c w)) =
        Finset.univ.filter (fun x => G.Adj w x ∧ c x ≠ c w) := by
      apply Finset.filter_congr
      intro x _
      cases c x <;> cases c w <;> simp
    rw [heq]
    exact_mod_cast h
  have hfin : HasFiniteDomain F := Set.toFinite _
  have hfull : ∀ α : Ordinal.{v}, PartitionerWins G F α := by
    intro α
    induction α using Ordinal.induction with
    | h α ih =>
      rw [PartitionerWins]
      intro w β hβ
      exact ⟨F, ⟨fun _ _ h => h, hfin, hunf w⟩, ih β hβ⟩
  rw [PartitionerWins]
  intro w β _
  refine ⟨F, ⟨fun x b h => ?_, hfin, hunf w⟩, hfull β⟩
  simp [emptyPartition] at h
