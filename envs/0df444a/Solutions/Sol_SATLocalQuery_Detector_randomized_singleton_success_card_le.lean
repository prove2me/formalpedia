-- Prove2me | solution 1 for SATLocalQuery.Detector.randomized_singleton_success_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T21:46:44.954918+00:00
-- url     : https://prove2.me/submissions/c9865984-75a3-4142-8fe6-8b4b88c4eaa0

import Definitions.Def_SATLocalQueryDetector

set_option autoImplicit false

namespace SATLocalQuery.Detector

variable {I O : Type*}

/-- The entire transcript and output survive changes at unqueried points. -/
theorem replay (first second : I → Bool) (D : Detector I O)
    (agreement : ∀ i ∈ calls first D, second i = first i) :
    calls second D = calls first D ∧ run second D = run first D := by
  induction D with
  | result o => exact ⟨rfl,rfl⟩
  | ask i next ih =>
    have here : second i = first i := agreement i (by simp [calls])
    have remaining : ∀ j ∈ calls first (next (first i)), second j = first j := by
      intro j present
      exact agreement j (by simp [calls,present])
    obtain ⟨trace,reply⟩ := ih (first i) remaining
    exact ⟨by simp only [calls,here,trace], by simp only [run,here,reply]⟩

theorem replay_unqueried_singleton [DecidableEq I] (D : Detector I O) {target : I}
    (missed : target ∉ calls (fun _ => false) D) :
    calls (onlyAt target) D = calls (fun _ => false) D ∧
      run (onlyAt target) D = run (fun _ => false) D := by
  apply replay
  intro i visited
  exact decide_eq_false (fun h => missed (h ▸ visited))

/-- Sound and complete zero-versus-singleton discrimination requires
visiting the entire input universe on its all-zero transcript. -/
theorem discrimination_calls_ge_card [Fintype I] [DecidableEq I] (D : Detector I Bool)
    (zero : run (fun _ => false) D = false)
    (positive : ∀ target, run (onlyAt target) D = true) :
    Fintype.card I ≤ (calls (fun _ => false) D).length := by
  have full (target : I) : target ∈ calls (fun _ => false) D := by
    by_contra missed
    have impossible := (replay_unqueried_singleton D missed).2
    simp only [positive,zero] at impossible
    cases impossible
  have eq : (calls (fun _ => false) D).toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    simpa using full i
  rw [← Finset.card_univ,← eq]
  exact List.toFinset_card_le _

/-- For singleton targets, every successful detector output belongs to
its all-zero trace or to its sole output on that trace. -/
theorem singleton_success_card_le [Fintype I] [DecidableEq I] (D : Detector I (Option I)) :
    (Finset.univ.filter fun target => run (onlyAt target) D = some target).card ≤
      (calls (fun _ => false) D).length + 1 := by
  let trace := calls (fun _ => false) D
  let guess := (run (fun _ => false) D).toList
  have sub : (Finset.univ.filter fun target => run (onlyAt target) D = some target) ⊆
      (trace ++ guess).toFinset := by
    intro target yes
    have solves := (Finset.mem_filter.mp yes).2
    by_cases visited : target ∈ trace
    · exact List.mem_toFinset.mpr (List.mem_append.mpr (Or.inl visited))
    · have answer : run (fun _ => false) D = some target :=
        (replay_unqueried_singleton D visited).2.symm.trans solves
      apply List.mem_toFinset.mpr (List.mem_append.mpr (Or.inr ?_))
      simp [guess,answer]
  have guessSize : guess.length ≤ 1 := by
    unfold guess
    cases run (fun _ => false) D <;> simp
  calc
    _ ≤ (trace ++ guess).toFinset.card := Finset.card_le_card sub
    _ ≤ (trace ++ guess).length := List.toFinset_card_le _
    _ ≤ _ := by simp only [List.length_append,trace]; omega

end SATLocalQuery.Detector

open SATLocalQuery SATLocalQuery.Detector

theorem solution {I R : Type*}
    [Fintype R] [DecidableEq R] [Fintype I] [DecidableEq I]
    (D : R → Detector I (Option I)) (q : ℕ)
    (short : ∀ r, (calls (fun _ => false) (D r)).length ≤ q) :
    (Finset.univ.filter fun p : R × I => run (onlyAt p.2) (D p.1) = some p.2).card ≤
      Fintype.card R * (q+1) := by
  let success (r : R) : Finset I :=
    Finset.univ.filter fun target => run (onlyAt target) (D r) = some target
  let good : Finset (R × I) :=
    Finset.univ.filter fun p => run (onlyAt p.2) (D p.1) = some p.2
  have fiber (r : R) : good.filter (fun p => p.1 = r) = {r} ×ˢ success r := by
    apply Finset.ext
    intro p
    rw [Finset.mem_product]
    simp only [good,success,Finset.mem_filter,Finset.mem_singleton,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨solves,eq⟩
      exact ⟨eq,eq ▸ solves⟩
    · rintro ⟨eq,solves⟩
      exact ⟨eq.symm ▸ solves,eq⟩
  change good.card ≤ _
  calc
    good.card = ∑ r : R, (good.filter fun p => p.1 = r).card :=
      Finset.card_eq_sum_card_fiberwise (s := good) (t := (Finset.univ : Finset R))
        (f := Prod.fst) (fun _ _ => Finset.mem_univ _)
    _ = ∑ r : R, (success r).card := by
      apply Finset.sum_congr rfl
      intro r _
      simp [fiber r]
    _ ≤ ∑ _r : R, (q+1) := by
      apply Finset.sum_le_sum
      intro r _
      exact (singleton_success_card_le (D r)).trans (Nat.add_le_add_right (short r) 1)
    _ = _ := by simp

#print axioms solution
