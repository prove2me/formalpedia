-- Prove2me | solution 1 for UndecidableSpectralGap.usg_switch_entrywise_laplacian
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T07:43:33.778269+00:00
-- url     : https://prove2.me/submissions/56d49c58-994f-4fff-af3b-95c8bce8d44d

import Definitions.Def_usg_switch_entry_data
set_option autoImplicit false
set_option maxHeartbeats 8000000
open UndecidableSpectralGap

namespace AgentBUSG

variable {L : ℕ}

theorem agree_eq_iff {p q : Site L} {c c' : Config L 3}
    (h : ∀ s, s ≠ p → s ≠ q → c s = c' s) :
    c = c' ↔ c p = c' p ∧ c q = c' q := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    funext s
    by_cases hp : s = p
    · subst hp; exact h1
    by_cases hq : s = q
    · subst hq; exact h2
    exact h s hp hq

theorem agree_swap_iff {p q : Site L} (hpq : p ≠ q) {c c' : Config L 3}
    (h : ∀ s, s ≠ p → s ≠ q → c s = c' s) :
    c' = c ∘ Equiv.swap p q ↔ c' p = c q ∧ c' q = c p := by
  constructor
  · rintro rfl
    simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  · rintro ⟨h1, h2⟩
    funext s
    by_cases hp : s = p
    · subst hp; simp [h1]
    by_cases hq : s = q
    · subst hq; simp [h2]
    simp [Equiv.swap_apply_of_ne_of_ne hp hq, h s hp hq]

theorem one_entry (p : Site L) (a : ℝ) (c c' : Config L 3) :
    embedOne p ((a : ℂ) • switchProjector) c c' =
      if c = c' then (if c p ≠ 0 then (a : ℂ) else 0) else 0 := by
  unfold embedOne
  by_cases hc : c = c'
  · subst hc; simp [switchProjector]
  · rw [if_neg hc]
    split_ifs with hag
    · have hne : c p ≠ c' p := by
        intro he; apply hc; funext s
        by_cases hs : s = p
        · subst hs; exact he
        · exact hag s hs
      simp [switchProjector, hne]
    · rfl

theorem guard_entry (e : Site L × Site L) (hne : e.1 ≠ e.2) (c c' : Config L 3) :
    embedTwo e.1 e.2 switchGuard c c' =
      if c = c' then (if switchBoundaryAt c e then (1 : ℂ) else 0) else 0 := by
  unfold embedTwo
  by_cases hc : c = c'
  · subst hc
    simp only [implies_true, if_true]
    unfold switchGuard
    by_cases hb : switchBoundaryAt c e
    · rw [if_pos hb, if_pos ⟨rfl, hb⟩]
    · rw [if_neg hb, if_neg (fun h => hb h.2)]
  · rw [if_neg hc]
    split_ifs with hag
    · have := (agree_eq_iff hag).not.mp hc
      unfold switchGuard
      rw [if_neg]
      rintro ⟨h1, -⟩
      simp only [Prod.mk.injEq] at h1
      exact this h1
    · rfl

theorem exch_entry (e : Site L × Site L) (hne : e.1 ≠ e.2) (c c' : Config L 3) :
    embedTwo e.1 e.2 switchExchange c c' =
      if c = c' then (if c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2 then (1 : ℂ) else 0)
      else (if c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2 ∧ c' = c ∘ Equiv.swap e.1 e.2
        then (-1 : ℂ) else 0) := by
  unfold embedTwo
  by_cases hag : ∀ s, s ≠ e.1 → s ≠ e.2 → c s = c' s
  · rw [if_pos hag]
    simp only [agree_eq_iff hag, agree_swap_iff hne hag]
    generalize c e.1 = x1, c e.2 = x2, c' e.1 = y1, c' e.2 = y2
    fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;>
      simp [switchExchange, switchVector]
  · rw [if_neg hag]
    have h1 : c ≠ c' := by rintro rfl; exact hag (fun _ _ _ => rfl)
    rw [if_neg h1, if_neg]
    rintro ⟨-, -, -, hsw⟩
    apply hag
    intro s hs1 hs2
    rw [hsw]
    simp [Equiv.swap_apply_of_ne_of_ne hs1 hs2]

theorem lin_entry (p q : Site L) (b : ℝ) (c c' : Config L 3) :
    embedTwo p q (switchGuard + (b : ℂ) • switchExchange) c c' =
      embedTwo p q switchGuard c c' + (b : ℂ) * embedTwo p q switchExchange c c' := by
  unfold embedTwo
  split_ifs <;> simp [Matrix.add_apply, Matrix.smul_apply]

theorem row_ne {e : Site L × Site L} (he : e ∈ rowEdges L) : e.1 ≠ e.2 := by
  intro h
  simp only [rowEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
  rw [h] at he
  omega

theorem col_ne {e : Site L × Site L} (he : e ∈ colEdges L) : e.1 ≠ e.2 := by
  intro h
  simp only [colEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
  rw [h] at he
  omega

theorem sum_ite_const {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] (x : ℂ) :
    (∑ i ∈ s, if P i then x else 0) = x * ((s.filter P).card : ℂ) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem rate_sum (b : ℝ) (c : Config L 3) :
    ∑ j ∈ Finset.univ.erase c, switchTransitionRate L b c j =
      b * (((rowEdges L).filter (fun e => c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2)).card : ℝ) := by
  unfold switchTransitionRate
  rw [← Finset.mul_sum]
  congr 1
  simp only [Finset.card_filter]
  push_cast
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hD : c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2
  · have hne : c ∘ Equiv.swap e.1 e.2 ≠ c := by
      intro h
      have := congrFun h e.1
      simp [Equiv.swap_apply_left] at this
      exact hD.2.2 this.symm
    have hiff : ∀ x : Config L 3, (c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2 ∧
        x = c ∘ Equiv.swap e.1 e.2) ↔ x = c ∘ Equiv.swap e.1 e.2 :=
      fun x => ⟨fun h => h.2.2.2, fun h => ⟨hD.1, hD.2.1, hD.2.2, h⟩⟩
    simp only [hiff]
    rw [Finset.sum_ite_eq']
    simp [hne]
    exact hD
  · have hf : ∀ x : Config L 3, ¬(c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2 ∧
        x = c ∘ Equiv.swap e.1 e.2) := fun x h => hD ⟨h.1, h.2.1, h.2.2.1⟩
    simp only [hf, hD, if_false, Finset.sum_const_zero]

end AgentBUSG

open AgentBUSG in
theorem _root_.solution
    (L : ℕ) (a b : ℝ) (c c' : Config L 3) :
    switchHam L a b c c' =
      if c = c' then
        ((switchPotential L a c +
          ∑ j ∈ Finset.univ.erase c, switchTransitionRate L b c j : ℝ) : ℂ)
      else -((switchTransitionRate L b c c' : ℝ) : ℂ) := by
  unfold switchHam latticeHam
  simp only [Matrix.add_apply, Matrix.sum_apply]
  rw [Finset.sum_congr rfl (fun e he => by
      rw [lin_entry, guard_entry e (row_ne he), exch_entry e (row_ne he)])]
  rw [Finset.sum_congr rfl (fun e he => guard_entry (L := L) e (col_ne he) c c')]
  simp only [one_entry]
  by_cases hc : c = c'
  · subst hc
    simp only [if_true]
    rw [rate_sum]
    unfold switchPotential switchBoundaryCount switchOccupiedCount
    rw [Finset.sum_add_distrib]
    rw [← Finset.mul_sum, sum_ite_const, sum_ite_const, sum_ite_const, sum_ite_const]
    push_cast
    ring
  · simp only [if_neg hc, Finset.sum_const_zero, add_zero, zero_add]
    rw [← Finset.mul_sum, sum_ite_const]
    unfold switchTransitionRate
    push_cast
    ring

#print axioms solution
