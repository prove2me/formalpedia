-- Prove2me | solution 1 for RestrictedAssignment.Svensson.dual_objective_neg_of_no_potential_move
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-10-29T05:28:32.212985+00:00
-- url     : https://prove2.me/submissions/d282b5a9-26f7-4718-9f54-eb728cf8d5f9

import Mathlib.Tactic
import Mathlib.Data.Fintype.Powerset
import Definitions.Def_RestrictedAssignment_Svensson_configLP
import Definitions.Def_RestrictedAssignment_Svensson_extendSchedule

open Finset Classical RestrictedAssignment.Svensson

namespace SchedulingDualCounterexample

def allowed : Bool → Finset Unit := fun _ ↦ {()}

noncomputable def size (j : Bool) : ℝ := if j then 19 / 10 else 1 / 10

def initial (j : Bool) : Option Unit := if j then some () else none

def root : Blocker Bool Unit := ⟨{false}, none, .small⟩

def blocker : Blocker Bool Unit := ⟨{true}, some (), .small⟩

def stuck : AlgState Bool Unit := ⟨initial, [root, blocker]⟩

lemma bool_univ : (univ : Finset Bool) = {false, true} := by decide

@[simp] lemma none_ne_some {α : Type} (a : α) : (none : Option α) ≠ some a := by
  intro h
  cases h

lemma potential_not_small_blocked {J M : Type} [Fintype J] [Fintype M]
    [DecidableEq J] [DecidableEq M] (Γ : J → Finset M) (p : J → ℝ)
    (s : AlgState J M) (j : J) (i : M) (h : IsPotentialMove Γ p s j i) : ¬ InMS s i := by
  obtain ⟨t, ht⟩ := h
  have hMT : ¬ InMT s i → ¬ InMS s i :=
    fun h1 ⟨B, hB, _, hBm⟩ ↦ h1 ⟨B, hB, hBm⟩
  cases t with
  | small =>
    rcases ht.2.2 with ⟨_, h⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩
    · exact h
    · exact hMT h
    · exact h
  | medLargeToBig =>
    rcases ht.2.2.1 with ⟨_, h⟩ | ⟨_, _, h⟩
    · exact hMT h
    · exact h
  | hugeToSmall => exact hMT ht.2.2.2.1
  | hugeToBig => exact hMT ht.2.2.2.1
  | hugeToMedium => exact hMT ht.2.2.2.1

lemma initial_valid : Valid allowed size initial := by
  constructor
  · intro j i _
    cases i
    simp [allowed]
  · intro i
    cases i
    have hb : univ.filter (fun j ↦ initial j = some () ∧ IsBig size j) = {true} := by
      ext j
      cases j <;> norm_num [initial, size, IsBig]
    have ha : univ.filter (fun j ↦ initial j = some ()) = {true} := by
      ext j
      cases j <;> simp [initial]
    constructor
    · rw [hb]
      norm_num
    · rw [pload, ha]
      norm_num [size, R]

lemma new_small : IsPotentialMoveOf allowed size (initState initial false) false () .small := by
  refine ⟨?_, ?_, Or.inl ⟨?_, ?_⟩⟩
  · refine ⟨root, ?_, ?_⟩ <;> simp [initState, root]
  · constructor
    · simp [allowed]
    · change (none : Option Unit) ≠ some ()
      decide
  · norm_num [IsSmall, size]
  · rintro ⟨B, hB, _, hm⟩
    have hEq : B = root := by simpa [initState, root] using hB
    subst B
    cases hm

lemma new_not_valid : ¬ IsValidMove allowed size (initState initial false) false () := by
  intro h
  have hload := (h.2.2 ()).2
  have ha : univ.filter (fun j ↦ Function.update initial false (some ()) j = some ()) =
      (univ : Finset Bool) := by
    ext j
    cases j <;> simp [initial]
  change (∑ j ∈ univ.filter (fun j ↦ Function.update initial false (some ()) j = some ()),
    size j) ≤ 1 + R at hload
  rw [ha, bool_univ, Finset.sum_pair (by decide)] at hload
  norm_num [size, R] at hload

lemma first_step : Step allowed size false (initState initial false) stuck := by
  have hmin : ∀ j i, IsPotentialMove allowed size (initState initial false) j i →
      moveVal allowed size (initState initial false) false () ≤
        moveVal allowed size (initState initial false) j i := by
    intro j i h
    cases i
    cases j with
    | false => exact le_refl _
    | true =>
      obtain ⟨t, ht⟩ := h
      have hm : IsMove allowed (initState initial false) true () := by
        cases t <;> exact ht.2.1
      simp [IsMove, initState, initial] at hm
  refine ⟨rfl, false, (), ⟨.small, new_small⟩, hmin, 0, by decide, ?_, ?_⟩
  · simp [initState]
  · rw [if_neg new_not_valid, if_pos (Or.inl new_small)]
    have heq : Finset.univ.filter (fun j ↦ initial j = some ()) \
        jobsT (initState initial false) = ({true} : Finset Bool) := by
      ext j
      cases j <;> simp [initial, jobsT, InJT, initState]
    change stuck = ⟨initial, [root] ++
      [⟨univ.filter (fun j ↦ initial j = some ()) \ jobsT (initState initial false),
        some (), .small⟩]⟩
    rw [heq]
    rfl

lemma stuck_blocked : InMS stuck () := by
  exact ⟨blocker, by simp [stuck], rfl, rfl⟩

lemma stuck_no_move : ∀ j i, ¬ IsPotentialMove allowed size stuck j i := by
  intro j i h
  cases i
  exact potential_not_small_blocked allowed size stuck j () h stuck_blocked

lemma stuck_job (j : Bool) : InJT stuck j := by
  cases j with
  | false => exact ⟨root, by simp [stuck], by simp [root]⟩
  | true => exact ⟨blocker, by simp [stuck], by simp [blocker]⟩

lemma stuck_objective : (∑ i, yStar allowed size stuck i) = 1 ∧
    (∑ j, zStar allowed size stuck j) = 11 / 17 + 1 / 10 := by
  constructor
  · simp [yStar, stuck_blocked]
  · norm_num [bool_univ, zStar, stuck_job, size, IsBig, IsMedium, IsSmall]

end SchedulingDualCounterexample

open SchedulingDualCounterexample in
theorem solution : ¬ (∀ {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (σ0 : J → Option M) (jnew : J)
    (hσ0 : Valid Γ p σ0) (hjnew : σ0 jnew = none) (hΓnew : (Γ jnew).Nonempty)
    (s : AlgState J M) (hs : Reachable Γ p σ0 jnew s) (hloop : s.σ jnew = none)
    (hnone : ∀ j i, ¬ IsPotentialMove Γ p s j i),
    ∑ i, yStar Γ p s i < ∑ j, zStar Γ p s j) := by
  intro h
  have hbad := h allowed size (by intro j; cases j <;> norm_num [size]) initial false
    initial_valid rfl (by simp [allowed]) stuck
    (Relation.ReflTransGen.single first_step) rfl stuck_no_move
  obtain ⟨hy, hz⟩ := SchedulingDualCounterexample.stuck_objective
  rw [hy, hz] at hbad
  norm_num at hbad
