-- Prove2me | solution 1 for ProjSchedTW.OrderPolyhedra.schedule_order_feasible_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T10:08:45.454036+00:00
-- url     : https://prove2.me/submissions/3b608433-caa2-4aa6-b0a0-b56ef6df23fb

import Mathlib
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Project
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Resources
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Orders

set_option autoImplicit false

namespace ProjSchedTW.OrderPolyhedra.SOFI

open ProjSchedTW.OrderPolyhedra

theorem path_bound {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ)
    (hS : ∀ e ∈ P.E, (P.δ e.1 e.2 : ℝ) ≤ S e.2 - S e.1) :
    ∀ (l : List (Fin (n + 2))) (i j : Fin (n + 2)), P.network.IsPath i j l →
      ((P.network.walkLength l : ℤ) : ℝ) ≤ S j - S i
  | [], i, j, h => by simp [Network.IsPath] at h
  | [a], i, j, h => by
      obtain ⟨h1, h2, -⟩ := h
      simp at h1 h2
      subst h1; subst h2
      simp [Network.walkLength]
  | a :: b :: t, i, j, h => by
      obtain ⟨h1, h2, h3⟩ := h
      simp only [List.head?_cons, Option.some.injEq] at h1
      subst h1
      have h3' : (a, b) ∈ P.network.arcs ∧ (b :: t).IsChain (fun x y => (x, y) ∈ P.network.arcs) := by
        simpa using h3
      have h2' : (b :: t).getLast? = some j := by simpa using h2
      have ih := path_bound P S hS (b :: t) b j ⟨by simp, h2', h3'.2⟩
      have hab : (a, b) ∈ P.E := h3'.1
      have hδ := hS (a, b) hab
      have hw : P.network.walkLength (a :: b :: t) = P.δ a b + P.network.walkLength (b :: t) := rfl
      rw [hw]
      push_cast
      simp only at hδ
      linarith

theorem last_pos {n : ℕ} {K : Type} (P : Project n K) (hP : P.StandingAssumptions)
    (S : Fin (n + 2) → ℝ) (hS : P.IsTimeFeasible S) : 0 < S (Fin.last (n + 1)) := by
  obtain ⟨hn, -, -, hpos, -, -, -, -, hpath⟩ := hP
  have h10 : (1 : Fin (n + 2)) ≠ 0 := by
    simp [Fin.ext_iff]
  have h1l : (1 : Fin (n + 2)) ≠ Fin.last (n + 1) := by
    simp [Fin.ext_iff]; omega
  have hp1 := hpos 1 h10 h1l
  obtain ⟨l, hl, hlen⟩ := hpath 1
  have hb := path_bound P S hS.2 l 1 (Fin.last (n + 1)) hl
  have hS1 : 0 ≤ S 1 := hS.1.2 1
  have hc : ((P.p 1 : ℤ) : ℝ) ≤ ((P.network.walkLength l : ℤ) : ℝ) := by exact_mod_cast hlen
  have hp1' : (0 : ℝ) < (P.p 1 : ℝ) := by exact_mod_cast hp1
  push_cast at hc
  linarith

theorem zero_dur {n : ℕ} {K : Type} (P : Project n K) (hP : P.StandingAssumptions)
    (S : Fin (n + 2) → ℝ) (hS : P.IsTimeFeasible S) (i j : Fin (n + 2)) (hij : i ≠ j)
    (hi : P.p i = 0) (hj : P.p j = 0) (hSij : S i = S j) : False := by
  have hlast := last_pos P hP S hS
  have hpos := hP.2.2.2.1
  have h0 : S 0 = 0 := hS.1.1
  have key : ∀ x : Fin (n + 2), P.p x = 0 → x = 0 ∨ x = Fin.last (n + 1) := by
    intro x hx
    by_contra hc
    push_neg at hc
    have := hpos x hc.1 hc.2
    omega
  rcases key i hi with h | h <;> rcases key j hj with h' | h' <;> subst h <;> subst h'
  · exact hij rfl
  · linarith
  · linarith
  · exact hij rfl

theorem strict {n : ℕ} {K : Type} (P : Project n K) (hP : P.StandingAssumptions)
    (S : Fin (n + 2) → ℝ) (hS : P.IsTimeFeasible S) : IsStrictOrderSet (P.scheduleOrder S) := by
  constructor
  · intro i j hij hji
    simp [Project.scheduleOrder] at hij hji
    have hpi : (0 : ℝ) ≤ P.p i := by positivity
    have hpj : (0 : ℝ) ≤ P.p j := by positivity
    have e1 : (P.p i : ℝ) = 0 := by linarith [hij.2, hji.2]
    have e2 : (P.p j : ℝ) = 0 := by linarith [hij.2, hji.2]
    exact zero_dur P hP S hS i j hij.1 (by exact_mod_cast e1) (by exact_mod_cast e2)
      (by linarith [hij.2, hji.2])
  · intro h i j hhi hij
    simp [Project.scheduleOrder] at hhi hij ⊢
    have hph : (0 : ℝ) ≤ P.p h := by positivity
    have hpi : (0 : ℝ) ≤ P.p i := by positivity
    refine ⟨?_, by linarith [hhi.2, hij.2]⟩
    intro hhj
    subst hhj
    have e1 : (P.p h : ℝ) = 0 := by linarith [hhi.2, hij.2]
    have e2 : (P.p i : ℝ) = 0 := by linarith [hhi.2, hij.2]
    exact zero_dur P hP S hS h i hhi.1 (by exact_mod_cast e1) (by exact_mod_cast e2)
      (by linarith [hhi.2, hij.2])

theorem resource {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ)
    (hF : P.IsFeasible S) (S' : Fin (n + 2) → ℝ) (hS' : S' ∈ P.orderPolyhedron (P.scheduleOrder S)) :
    P.IsResourceFeasible S' := by
  intro t ht k
  unfold Project.usage
  set A := P.activeSet S' t with hA
  by_cases hne : A.Nonempty
  · obtain ⟨j, hjA, hjeq⟩ := Finset.exists_mem_eq_sup' hne S
    set tstar := A.sup' hne S with htstar
    have hjA' : S' j ≤ t ∧ t < S' j + P.p j := by
      simpa [hA, Project.activeSet] using hjA
    have hsub : A ⊆ P.activeSet S tstar := by
      intro i hi
      have hi' : S' i ≤ t ∧ t < S' i + P.p i := by
        simpa [hA, Project.activeSet] using hi
      simp only [Project.activeSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨Finset.le_sup' S hi, ?_⟩
      rw [hjeq]
      by_contra hc
      push_neg at hc
      by_cases hij : i = j
      · subst hij
        linarith [hi'.1, hi'.2]
      · have hmem : (i, j) ∈ P.scheduleOrder S := by
          simp [Project.scheduleOrder]
          exact ⟨hij, hc⟩
        have := hS'.2 (i, j) hmem
        simp only at this
        linarith [hi'.2, hjA'.1]
    have h0 : 0 ≤ tstar := by rw [hjeq]; exact hF.1.1.2 j
    calc ∑ i ∈ A, P.r i k ≤ ∑ i ∈ P.activeSet S tstar, P.r i k :=
          Finset.sum_le_sum_of_subset hsub
      _ ≤ P.R k := hF.2 tstar h0 k
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp

end ProjSchedTW.OrderPolyhedra.SOFI

open ProjSchedTW.OrderPolyhedra in
theorem solution {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (hP : P.StandingAssumptions)
    (S : Fin (n + 2) → ℝ) (hS : P.IsTimeFeasible S) :
    P.IsFeasibleOrder (P.scheduleOrder S) ↔ P.IsFeasible S := by
  constructor
  · intro h
    apply h.2 S
    refine ⟨hS, ?_⟩
    intro e he
    simp [Project.scheduleOrder] at he
    exact he.2
  · intro hF
    have hmem : S ∈ P.orderPolyhedron (P.scheduleOrder S) := by
      refine ⟨hS, ?_⟩
      intro e he
      simp [Project.scheduleOrder] at he
      exact he.2
    refine ⟨⟨ProjSchedTW.OrderPolyhedra.SOFI.strict P hP S hS, ⟨S, hmem⟩⟩, ?_⟩
    intro S' hS'
    exact ⟨hS'.1, ProjSchedTW.OrderPolyhedra.SOFI.resource P S hF S' hS'⟩
