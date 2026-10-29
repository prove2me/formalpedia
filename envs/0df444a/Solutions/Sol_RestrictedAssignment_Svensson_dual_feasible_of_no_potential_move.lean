-- Prove2me | solution 1 for RestrictedAssignment.Svensson.dual_feasible_of_no_potential_move
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-10-29T05:54:03.881994+00:00
-- url     : https://prove2.me/submissions/82289058-5327-4feb-99fc-0188b29b9943

import Mathlib.Tactic
import Mathlib.Data.Fintype.Powerset
import Definitions.Def_RestrictedAssignment_Svensson_configLP
import Definitions.Def_RestrictedAssignment_Svensson_extendSchedule

open Finset Classical RestrictedAssignment.Svensson

namespace SchedulingDualFeasibilityCounterexample

def allowed (j : Fin 4) : Finset Bool :=
  if j.val = 0 then {false} else if j.val = 3 then {true} else univ

noncomputable def size (j : Fin 4) : ℝ :=
  if j.val = 0 then 3 / 2 else if j.val = 1 then 3 / 5 else if j.val = 2 then 9 / 10 else 1 / 2

def initial (j : Fin 4) : Option Bool :=
  if j.val = 0 then none else if j.val = 1 then some false else some true

def root : Blocker (Fin 4) Bool := ⟨{0}, none, .small⟩

def medium : Blocker (Fin 4) Bool := ⟨{1}, some false, .medium⟩

def big : Blocker (Fin 4) Bool := ⟨{2}, some true, .big⟩

def state1 : AlgState (Fin 4) Bool := ⟨initial, [root, medium]⟩

def stuck : AlgState (Fin 4) Bool := ⟨initial, [root, medium, big]⟩

lemma jobs_univ : (univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide

@[simp] lemma fin4_ne01 : (0 : Fin 4) ≠ 1 := by decide
@[simp] lemma fin4_ne02 : (0 : Fin 4) ≠ 2 := by decide
@[simp] lemma fin4_ne03 : (0 : Fin 4) ≠ 3 := by decide
@[simp] lemma fin4_ne10 : (1 : Fin 4) ≠ 0 := by decide
@[simp] lemma fin4_ne12 : (1 : Fin 4) ≠ 2 := by decide
@[simp] lemma fin4_ne13 : (1 : Fin 4) ≠ 3 := by decide
@[simp] lemma fin4_ne20 : (2 : Fin 4) ≠ 0 := by decide
@[simp] lemma fin4_ne21 : (2 : Fin 4) ≠ 1 := by decide
@[simp] lemma fin4_ne23 : (2 : Fin 4) ≠ 3 := by decide
@[simp] lemma fin4_ne30 : (3 : Fin 4) ≠ 0 := by decide
@[simp] lemma fin4_ne31 : (3 : Fin 4) ≠ 1 := by decide
@[simp] lemma fin4_ne32 : (3 : Fin 4) ≠ 2 := by decide

attribute [local simp] Finset.filter_insert Finset.filter_singleton Finset.sum_insert

@[simp] lemma none_ne_some {α : Type} (a : α) : (none : Option α) ≠ some a := by
  intro h
  cases h

lemma potential_facts {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (s : AlgState J M) (j : J) (i : M)
    (h : IsPotentialMove Γ p s j i) : InJT s j ∧ IsMove Γ s j i := by
  obtain ⟨t, ht⟩ := h
  cases t <;> exact ⟨ht.1, ht.2.1⟩

lemma assigned_false : univ.filter (fun j ↦ initial j = some false) = ({1} : Finset (Fin 4)) := by
  ext j
  fin_cases j <;> decide

lemma assigned_true : univ.filter (fun j ↦ initial j = some true) = ({2, 3} : Finset (Fin 4)) := by
  ext j
  fin_cases j <;> decide

lemma big_false : univ.filter (fun j ↦ initial j = some false ∧ IsBig size j) = ∅ := by
  rw [← filter_filter, assigned_false]
  norm_num [IsBig, size]

lemma big_true : univ.filter (fun j ↦ initial j = some true ∧ IsBig size j) = ({2} : Finset (Fin 4)) := by
  rw [← filter_filter, assigned_true]
  norm_num [IsBig, size]

lemma initial_Si : Si allowed size (initState initial 0) false = ∅ := by
  change univ.filter (fun j ↦ initial j = some false ∧ InS allowed size (initState initial 0) j) = ∅
  rw [← filter_filter, assigned_false]
  norm_num [InS, IsSmall, size]

lemma initial_Mi : Mi size (initState initial 0) false = ({1} : Finset (Fin 4)) := by
  change univ.filter (fun j ↦ initial j = some false ∧ IsMedium size j) = {1}
  rw [← filter_filter, assigned_false]
  norm_num [IsMedium, size]

lemma initial_no_big : ¬ HasBig size (initState initial 0) false := by
  rintro ⟨j, hj, hb⟩
  have hmem : j ∈ univ.filter (fun j ↦ initial j = some false) := by
    simpa [initState] using hj
  rw [assigned_false] at hmem
  have hj1 := mem_singleton.mp hmem
  subst j
  norm_num [IsBig, size] at hb

lemma initial_valid : Valid allowed size initial := by
  constructor
  · intro j i hij
    fin_cases j <;> cases i <;> simp_all [allowed, initial]
  · intro i
    cases i
    · constructor
      · rw [big_false]; norm_num
      · rw [pload, assigned_false]; norm_num [size, R]
    · constructor
      · rw [big_true]; norm_num
      · rw [pload, assigned_true]; norm_num [size, R]

lemma root_medium : IsPotentialMoveOf allowed size (initState initial 0) 0 false .hugeToMedium := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨root, by simp [root, initState], by simp [root]⟩
  · constructor
    · norm_num [allowed]
    · change (none : Option Bool) ≠ some false
      decide
  · norm_num [IsHuge, size]
  · rintro ⟨B, hB, hm⟩
    have hEq : B = root := by simpa [root, initState] using hB
    subst B
    cases hm
  · rw [initial_Si]
    norm_num [size, R]
  · rw [initial_Si, initial_Mi]
    norm_num [size, R]

lemma root_not_valid : ¬ IsValidMove allowed size (initState initial 0) 0 false := by
  intro h
  have hh := (h.2.2 false).2
  norm_num [pload, initial, initState, size, jobs_univ, R] at hh

lemma first_step : Step allowed size 0 (initState initial 0) state1 := by
  have hmin : ∀ j i, IsPotentialMove allowed size (initState initial 0) j i →
      moveVal allowed size (initState initial 0) 0 false ≤
        moveVal allowed size (initState initial 0) j i := by
    intro j i h
    obtain ⟨hj, hi⟩ := potential_facts allowed size _ j i h
    have hj0 : j = 0 := by simpa [InJT, initState] using hj
    subst j
    have hi0 : i = false := by simpa [allowed] using hi.1
    subst i
    exact le_refl _
  refine ⟨rfl, 0, false, ⟨.hugeToMedium, root_medium⟩, hmin, 0, by decide, ?_, ?_⟩
  · simp [initState]
  · rw [if_neg root_not_valid]
    have hs : ¬ (IsPotentialMoveOf allowed size (initState initial 0) 0 false .small ∨
        IsPotentialMoveOf allowed size (initState initial 0) 0 false .hugeToSmall) := by
      norm_num [IsPotentialMoveOf, IsSmall, IsMedium, IsLarge, initial_no_big,
        size, initial_Si, initial_Mi, R]
    have hb : ¬ (IsPotentialMoveOf allowed size (initState initial 0) 0 false .medLargeToBig ∨
        IsPotentialMoveOf allowed size (initState initial 0) 0 false .hugeToBig) := by
      norm_num [IsPotentialMoveOf, IsSmall, IsMedium, IsLarge, initial_no_big, size]
    rw [if_neg hs, if_neg hb]
    have heq : univ.filter (fun j ↦ initial j = some false ∧ IsMedium size j) =
        ({1} : Finset (Fin 4)) := by
      ext j
      fin_cases j <;> norm_num [initial, IsMedium, size]
    change state1 = ⟨initial, [root] ++
      [⟨univ.filter (fun j ↦ initial j = some false ∧ IsMedium size j), some false, .medium⟩]⟩
    rw [heq]
    rfl

lemma medium_big : IsPotentialMoveOf allowed size state1 1 true .medLargeToBig := by
  refine ⟨?_, ?_, Or.inl ⟨?_, ?_⟩, ?_⟩
  · exact ⟨medium, by simp [state1], by simp [medium]⟩
  · constructor
    · norm_num [allowed]
    · change (some false : Option Bool) ≠ some true
      decide
  · norm_num [IsMedium, size]
  · simp [InMT, state1, root, medium]
  · exact ⟨2, by norm_num [state1, initial], by norm_num [IsBig, size]⟩

lemma medium_not_valid : ¬ IsValidMove allowed size state1 1 true := by
  intro h
  have hh := (h.2.2 true).2
  norm_num [pload, initial, state1, size, jobs_univ, R] at hh

lemma second_step : Step allowed size 0 state1 stuck := by
  have hmin : ∀ j i, IsPotentialMove allowed size state1 j i →
      moveVal allowed size state1 1 true ≤ moveVal allowed size state1 j i := by
    intro j i h
    obtain ⟨hj, hi⟩ := potential_facts allowed size state1 j i h
    have hj01 : j = 0 ∨ j = 1 := by simpa [InJT, state1, root, medium] using hj
    rcases hj01 with rfl | rfl
    · have hi0 : i = false := by simpa [allowed] using hi.1
      subst i
      obtain ⟨t, ht⟩ := h
      cases t <;> norm_num [IsPotentialMoveOf, size, IsSmall, IsMedium, IsLarge,
        InMT, state1, root, medium] at ht
    · have hi1 : i = true := by
        cases i
        · simp [IsMove, initial, state1] at hi
        · rfl
      subst i
      exact le_refl _
  refine ⟨rfl, 1, true, ⟨.medLargeToBig, medium_big⟩, hmin, 1, by decide, ?_, ?_⟩
  · simp [state1, medium]
  · rw [if_neg medium_not_valid]
    have hs : ¬ (IsPotentialMoveOf allowed size state1 1 true .small ∨
        IsPotentialMoveOf allowed size state1 1 true .hugeToSmall) := by
      have hb : HasBig size state1 true := ⟨2, rfl, by norm_num [IsBig, size]⟩
      norm_num [IsPotentialMoveOf, size, IsSmall, IsMedium, IsLarge, IsHuge,
        hb]
    rw [if_neg hs, if_pos (Or.inl medium_big)]
    have heq := big_true
    change stuck = ⟨initial, [root, medium] ++
      [⟨univ.filter (fun j ↦ initial j = some true ∧ IsBig size j), some true, .big⟩]⟩
    rw [heq]
    rfl

lemma stuck_no_move : ∀ j i, ¬ IsPotentialMove allowed size stuck j i := by
  intro j i ⟨t, ht⟩
  fin_cases j <;> cases i <;> cases t <;>
    norm_num [IsPotentialMoveOf, InJT, IsMove, InMS, InMT, InMB, InMM, IsSmall,
      IsMedium, IsLarge, IsHuge, allowed, size, initial, stuck, root, medium, big] at ht

lemma stuck_bad_dual : ¬ CLPDualFeasible allowed size 1 (yStar allowed size stuck)
    (zStar allowed size stuck) := by
  intro h
  have hC : ({2} : Finset (Fin 4)) ∈ configs allowed size 1 false := by
    norm_num [configs, allowed, size]
  have hh := h.2.2 false {2} hC
  have hMS : ¬ InMS stuck false := by simp [InMS, stuck, root, medium, big]
  have hJT1 : InJT stuck 1 := ⟨medium, by simp [stuck], by simp [medium]⟩
  have hJT2 : InJT stuck 2 := ⟨big, by simp [stuck], by simp [big]⟩
  have hy : yStar allowed size stuck false = 9 / 17 := by
    rw [yStar, if_neg hMS]
    change (∑ j ∈ univ.filter (fun j ↦ initial j = some false), zStar allowed size stuck j) = 9 / 17
    rw [assigned_false]
    norm_num [zStar, hJT1, IsBig, IsMedium, IsSmall, size]
  have hz : zStar allowed size stuck 2 = 11 / 17 := by
    norm_num [zStar, hJT2, IsBig, size]
  norm_num [hy, hz] at hh

end SchedulingDualFeasibilityCounterexample

open SchedulingDualFeasibilityCounterexample in
theorem solution : ¬ (∀ {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (σ0 : J → Option M) (jnew : J)
    (hσ0 : Valid Γ p σ0) (hjnew : σ0 jnew = none) (s : AlgState J M)
    (hs : Reachable Γ p σ0 jnew s) (hloop : s.σ jnew = none)
    (hnone : ∀ j i, ¬ IsPotentialMove Γ p s j i),
    CLPDualFeasible Γ p 1 (yStar Γ p s) (zStar Γ p s)) := by
  intro h
  exact stuck_bad_dual (h allowed size (by intro j; fin_cases j <;> norm_num [size])
    initial 0 initial_valid rfl stuck
    ((Relation.ReflTransGen.single first_step).tail second_step) rfl stuck_no_move)
