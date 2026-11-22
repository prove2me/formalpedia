-- Prove2me | solution 1 for ResourceScheduling.Poly.q_res1dot1_bottleneck
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-22T18:21:39.561987+00:00
-- url     : https://prove2.me/submissions/763c89df-78dd-4458-8205-4383fac9646c

import Mathlib
import Definitions.Def_ResourceScheduling_Poly_Model
import Definitions.Def_ResourceScheduling_Poly_SlotAssignment

set_option autoImplicit false

namespace ResourceScheduling.Poly.BottleneckCounterexample

open ResourceScheduling.Poly

/-- Three uniform machines of speeds `3/2, 1, 1`, one resource of size `s₁ = 2`, and four
unit-time jobs that all require one unit of the resource. The two fastest machines are
`M₀, M₁`, so the speed hypothesis holds. -/
noncomputable abbrev cexI : Instance where
  n := 4
  m := 3
  q := ![3 / 2, 1, 1]
  q_pos := by
    intro i
    fin_cases i <;> norm_num
  l := 1
  s := fun _ => 2
  s_pos := fun _ => by norm_num
  r := fun _ _ => 1
  arc := fun _ _ => False
  acyclic := by
    intro j h
    rcases h with h | ⟨_, h⟩ <;> exact h

/-- Jobs `0, 1` on the fast machine `M₀` at times `0` and `1` (with an idle gap `[2/3, 1)`),
job `2` on `M₁` at time `0`, and job `3` on `M₂` at time `2/3`. -/
noncomputable abbrev cexσ : Schedule cexI where
  machine := ![0, 0, 1, 2]
  start := ![0, 1, 0, 2 / 3]

theorem completion_eq (j : Fin cexI.n) :
    cexσ.completion j = ![2 / 3, 5 / 3, 1, 5 / 3] j := by
  fin_cases j <;>
    simp [Schedule.completion, Instance.procTime] <;> norm_num

theorem executing_iff (j : Fin cexI.n) (t : ℝ) :
    cexσ.IsExecutingAt j t ↔ ![0, 1, 0, 2 / 3] j ≤ t ∧ t < ![2 / 3, 5 / 3, 1, 5 / 3] j := by
  unfold Schedule.IsExecutingAt
  rw [completion_eq]

/-- At every time at most two jobs run: the busy intervals `[0,2/3)`, `[1,5/3)`, `[0,1)`,
`[2/3,5/3)` form the path `0 – 2 – 3 – 1` under intersection. -/
theorem activeSet_card_le (t : ℝ) : (cexσ.activeSet t).card ≤ 2 := by
  classical
  have hsub : cexσ.activeSet t ⊆
      (if t < 2 / 3 then {0, 2} else if t < 1 then {2, 3} else {3, 1} : Finset (Fin 4)) := by
    intro j hj
    have hj' : cexσ.IsExecutingAt j t := by
      unfold Schedule.activeSet at hj
      simpa using hj
    obtain ⟨h1, h2⟩ := (executing_iff j t).1 hj'
    split_ifs with ht1 ht2 <;> fin_cases j <;> simp at h1 h2 ⊢ <;> norm_num at h1 h2 ⊢ <;> linarith
  refine (Finset.card_le_card hsub).trans ?_
  split_ifs <;> exact Finset.card_le_two

theorem cexσ_feasible : cexσ.Feasible := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j <;> simp <;> norm_num
  · intro j k hjk hm
    rw [completion_eq, completion_eq]
    fin_cases j <;> fin_cases k <;> simp at hjk hm ⊢ <;> norm_num
  · intro j k h
    exact absurd h (by rintro (h | ⟨_, h⟩) <;> exact h)
  · intro t h
    have hsum : ∑ j ∈ cexσ.activeSet t, cexI.r h j = (cexσ.activeSet t).card := by
      simp
    rw [hsum]
    exact activeSet_card_le t

theorem cexσ_makespan_le : cexσ.makespan ≤ 5 / 3 := by
  unfold Schedule.makespan
  rw [dif_pos Finset.univ_nonempty]
  refine Finset.sup'_le _ _ fun j _ => ?_
  rw [completion_eq]
  fin_cases j <;> norm_num

/-- Every slot of a fast machine (`M₀` or `M₁`) with cost at most `5/3` is one of the three
slots `(M₀, 1)`, `(M₀, 2)`, `(M₁, 1)` (1-based positions). -/
theorem slot_mem (p : Fin 3 × Fin 4) (hp : p.1.val < 2)
    (hc : ((p.2.val : ℝ) + 1) / cexI.q p.1 ≤ 5 / 3) :
    p ∈ ({(0, 0), (0, 1), (1, 0)} : Finset (Fin 3 × Fin 4)) := by
  obtain ⟨i, k⟩ := p
  fin_cases i <;> fin_cases k <;> simp at hp hc ⊢ <;> norm_num at hc

end ResourceScheduling.Poly.BottleneckCounterexample

open ResourceScheduling.Poly
open ResourceScheduling.Poly.BottleneckCounterexample

set_option linter.unusedVariables false in
theorem solution : ¬ (∀ (I : Instance) (hl : I.l = 1) (hprec : I.NoPrecedence)
    (hr : ∀ j, I.r ⟨0, by omega⟩ j ≤ 1)
    (hfast : ∀ h i : Fin I.m, h.val < I.s ⟨0, by omega⟩ → I.s ⟨0, by omega⟩ ≤ i.val →
      I.q i ≤ I.q h),
    (∀ σ : Schedule I, σ.Feasible →
        ∃ x, I.IsSlotAssignment hl x ∧ I.bottleneck x ≤ σ.makespan) ∧
      ∀ x, I.IsSlotAssignment hl x →
        ∃ σ : Schedule I, σ.Feasible ∧ σ.makespan ≤ I.bottleneck x) := by
  intro hthm
  have hprec : cexI.NoPrecedence := fun _ _ h => h
  have hr : ∀ j, cexI.r ⟨0, by decide⟩ j ≤ 1 := fun _ => le_rfl
  have hfast : ∀ h i : Fin cexI.m, h.val < cexI.s ⟨0, by decide⟩ →
      cexI.s ⟨0, by decide⟩ ≤ i.val → cexI.q i ≤ cexI.q h := by
    intro h i hh hi
    fin_cases h <;> fin_cases i <;> simp at hh hi ⊢ <;> norm_num
  obtain ⟨x, ⟨hinj, hres⟩, hb⟩ :=
    (hthm cexI rfl hprec hr hfast).1 cexσ cexσ_feasible
  have hb' : cexI.bottleneck x ≤ 5 / 3 := hb.trans cexσ_makespan_le
  have hmem : ∀ j, x j ∈ ({(0, 0), (0, 1), (1, 0)} : Finset (Fin 3 × Fin 4)) := by
    intro j
    refine slot_mem (x j) (hres j rfl) ?_
    refine le_trans ?_ hb'
    unfold Instance.bottleneck
    rw [dif_pos Finset.univ_nonempty]
    exact Finset.le_sup' (fun j => (((x j).2.val : ℝ) + 1) / cexI.q (x j).1)
      (Finset.mem_univ j)
  have hcard := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin cexI.n))) x
    (fun j _ => hmem j) hinj.injOn
  exact absurd hcard (by decide)
