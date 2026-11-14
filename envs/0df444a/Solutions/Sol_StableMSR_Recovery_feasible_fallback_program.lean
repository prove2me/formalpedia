-- Prove2me | solution 1 for StableMSR.Recovery.feasible_fallback_program
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T14:49:18.442116+00:00
-- url     : https://prove2.me/submissions/ffac91a6-881a-4a85-a9a3-56464c5a8695

import Theorems.Thm_StableMSR_Recovery_validLabels_feasible


set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery
namespace FallbackAux

/- Write singleton labels 0,...,k-2, then label k-1 on all remaining points. -/
def program : MinSumFPT.Program := [
  .core (.pset 1 1), .integerLoad 2 1, .core (.pdec 2), .core (.pdec 2),
  .integerLoad 3 0, .core (.pdec 3), .core (.pset 4 (-1)),
  .core (.pjle 5 2 9), .core (.pjle 0 0 13),
  .integerStore 4 5, .core (.pdec 4), .core (.pinc 5), .core (.pjle 0 0 7),
  .core (.pcopy 6 5), .core (.pjle 6 3 16), .halt 0,
  .integerStore 4 5, .core (.pdec 4), .core (.pinc 6), .core (.pjle 0 0 14)]

lemma deterministic : DeterministicProgram program := by
  constructor
  · intro i hi
    simp only [program, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
      subst i <;> simp [MinSumFPT.Admissible]
  · intro i hi
    simp only [program, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
      subst i <;> trivial

/- Integer memory after writing the first t point labels. -/
def memory (n k t : ℕ) (a : ℤ) : ℤ :=
  if -(t : ℤ) ≤ a ∧ a < 0 then (min (-1 - a).toNat (k - 1) : ℕ)
  else if a = 0 then n else if a = 1 then k else 0

lemma memory_zero (n k : ℕ) : memory n k 0 =
    fun a => if a = 0 then (n : ℤ) else if a = 1 then (k : ℤ) else 0 := by
  funext a
  simp only [memory, Nat.cast_zero, neg_zero]
  split_ifs <;> omega

lemma memory_step (n k t : ℕ) :
    Function.update (memory n k t) (-1 - (t : ℤ)) (min t (k-1) : ℕ) =
      memory n k (t+1) := by
  funext a
  by_cases ha : a = -1 - (t : ℤ)
  · subst a
    simp only [Function.update_self, memory, Nat.cast_add, Nat.cast_one]
    have hloc : -((t : ℤ)+1) ≤ -1-(t : ℤ) ∧ -1-(t : ℤ)<0 := by omega
    rw [if_pos hloc]
    congr 2
    omega
  · rw [Function.update_of_ne ha]
    unfold memory
    have hloc : (-((t+1 : ℕ) : ℤ) ≤ a ∧ a < 0) ↔ (-(t : ℤ) ≤ a ∧ a < 0) := by
      push_cast
      omega
    simp only [hloc]

/- Pointer values at the head of the first loop. -/
def pointers₁ (n k t : ℕ) (q : ℕ) : ℤ :=
  if q = 1 then 1 else if q = 2 then (k : ℤ)-2 else if q = 3 then (n : ℤ)-1
  else if q = 4 then -1-(t : ℤ) else if q = 5 then t else 0

/- Pointer values at the head of the second loop. -/
def pointers₂ (n k t : ℕ) (q : ℕ) : ℤ :=
  if q = 1 then 1 else if q = 2 then (k : ℤ)-2 else if q = 3 then (n : ℤ)-1
  else if q = 4 then -1-(t : ℤ) else if q = 5 then (k : ℤ)-1
  else if q = 6 then t else 0

noncomputable def state₁ (n k t w : ℕ) : MinSumFPT.State where
  cfg := ⟨7, fun _ => 0, pointers₁ n k t, fun _ => 0⟩
  imem := memory n k t
  tapePos := 0
  work := w
  queries := 0
  halted := false
  output := 0

noncomputable def state₂ (n k t w : ℕ) : MinSumFPT.State where
  cfg := ⟨14, fun _ => 0, pointers₂ n k t, fun _ => 0⟩
  imem := memory n k t
  tapePos := 0
  work := w
  queries := 0
  halted := false
  output := 0

noncomputable def advance {n : ℕ} (d : Point n → Point n → ℝ)
    (t : ℕ) (s : MinSumFPT.State) : MinSumFPT.State :=
  (MinSumFPT.step program d (fun _ => 0))^[t] s

lemma first_loop_step {n : ℕ} (d : Point n → Point n → ℝ) (k t w : ℕ)
    (ht : t < k-1) :
    advance d 5 (state₁ n k t w) = state₁ n k (t+1) (w+5) := by
  have htest : (t : ℤ) ≤ (k : ℤ)-2 := by omega
  have hmin : min t (k-1) = t := Nat.min_eq_left (by omega)
  simp only [advance, Function.iterate_succ_apply, Function.iterate_zero_apply]
  simp [program, MinSumFPT.step,
    state₁, SmaleNinth.RAMStep, MinSumFPT.Instr.coreOf, MinSumFPT.State.next,
    pointers₁, htest, Nat.add_assoc]
  constructor
  · funext q
    simp only [Function.update_apply, pointers₁]
    split_ifs <;> simp_all <;> omega
  · simpa only [hmin] using memory_step n k t


lemma second_loop_step {n : ℕ} (d : Point n → Point n → ℝ) (k t w : ℕ)
    (hk : 1 ≤ k) (hkt : k-1 ≤ t) (ht : t < n) :
    advance d 5 (state₂ n k t w) = state₂ n k (t+1) (w+5) := by
  have htest : (t : ℤ) ≤ (n : ℤ)-1 := by omega
  have hmin : ((min t (k-1) : ℕ) : ℤ) = (k : ℤ)-1 := by
    rw [Nat.min_eq_right hkt]
    omega
  simp only [advance, Function.iterate_succ_apply, Function.iterate_zero_apply]
  simp [program, MinSumFPT.step, state₂, SmaleNinth.RAMStep,
    MinSumFPT.Instr.coreOf, MinSumFPT.State.next, pointers₂, htest, Nat.add_assoc]
  constructor
  · funext q
    simp only [Function.update_apply, pointers₂]
    split_ifs <;> simp_all <;> omega
  · simpa only [hmin] using memory_step n k t

lemma setup {n : ℕ} (d : Point n → Point n → ℝ) (k : ℕ) :
    advance d 7 (MinSumFPT.initState n k 0 0) = state₁ n k 0 7 := by
  simp only [advance, Function.iterate_succ_apply, Function.iterate_zero_apply]
  simp [program, MinSumFPT.step, state₁, MinSumFPT.initState, SmaleNinth.RAMStep,
    MinSumFPT.Instr.coreOf, MinSumFPT.State.next, pointers₁, memory_zero]
  funext q
  simp only [Function.update_apply, pointers₁]
  split_ifs <;> simp_all <;> omega

lemma switch_loop {n : ℕ} (d : Point n → Point n → ℝ) (k w : ℕ)
    (hk : 1 ≤ k) :
    advance d 3 (state₁ n k (k-1) w) = state₂ n k (k-1) (w+3) := by
  have htest : ¬ ((k-1 : ℕ) : ℤ) ≤ (k : ℤ)-2 := by omega
  simp only [advance, Function.iterate_succ_apply, Function.iterate_zero_apply]
  simp [program, MinSumFPT.step, state₁, state₂, SmaleNinth.RAMStep,
    MinSumFPT.Instr.coreOf, MinSumFPT.State.next, pointers₁, htest, Nat.add_assoc]
  funext q
  simp only [Function.update_apply, pointers₁, pointers₂]
  split_ifs <;> simp_all <;> omega

lemma advance_add {n : ℕ} (d : Point n → Point n → ℝ)
    (a b : ℕ) (s : MinSumFPT.State) :
    advance d (a+b) s = advance d b (advance d a s) := by
  unfold advance
  rw [Nat.add_comm a b, Function.iterate_add_apply]

lemma first_loop_run {n : ℕ} (d : Point n → Point n → ℝ) (k j : ℕ)
    (hj : j ≤ k-1) :
    advance d (5*j) (state₁ n k 0 7) = state₁ n k j (7+5*j) := by
  induction j with
  | zero => simp [advance]
  | succ j ih =>
    rw [Nat.mul_succ, advance_add, ih (by omega)]
    simpa only [Nat.mul_succ, Nat.add_assoc] using
      first_loop_step d k j (7+5*j) (by omega)

lemma second_loop_run {n : ℕ} (d : Point n → Point n → ℝ) (k t w q : ℕ)
    (hk : 1 ≤ k) (hkt : k-1 ≤ t) (hqn : t+q ≤ n) :
    advance d (5*q) (state₂ n k t w) = state₂ n k (t+q) (w+5*q) := by
  induction q with
  | zero => simp [advance]
  | succ q ih =>
    rw [Nat.mul_succ, advance_add, ih (by omega)]
    simpa only [Nat.mul_succ, Nat.add_assoc] using
      second_loop_step d k (t+q) (w+5*q) hk (by omega) (by omega)

noncomputable def finished (n k w : ℕ) : MinSumFPT.State :=
  { state₂ n k n w with
    cfg := { (state₂ n k n w).cfg with pc := 15 }, halted := true }

lemma finish {n : ℕ} (d : Point n → Point n → ℝ) (k w : ℕ) :
    advance d 2 (state₂ n k n w) = finished n k (w+2) := by
  have htest : ¬ (n : ℤ) ≤ (n : ℤ)-1 := by omega
  simp only [advance, Function.iterate_succ_apply, Function.iterate_zero_apply]
  simp [program, MinSumFPT.step, state₂, finished, SmaleNinth.RAMStep,
    MinSumFPT.Instr.coreOf, pointers₂, htest, Nat.add_assoc]

/- The actual interpreter halts after exactly 5n+12 charged instructions. -/
lemma execute_eq {n : ℕ} (d : Point n → Point n → ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    execute program n k d (5*n+12) = finished n k (5*n+12) := by
  change advance d (5*n+12) (MinSumFPT.initState n k 0 0) = _
  have ht : 5*n+12 = 7 + 5*(k-1) + 3 + 5*(n-(k-1)) + 2 := by omega
  rw [ht, advance_add, advance_add, advance_add, advance_add, setup,
    first_loop_run d k (k-1) (by omega), switch_loop d k _ hk,
    second_loop_run d k (k-1) _ (n-(k-1)) hk (by omega) (by omega)]
  have hn : k-1+(n-(k-1)) = n := by omega
  rw [hn, finish]

lemma memory_label (n k x : ℕ) (hx : x < n) :
    memory n k n (-1-(x : ℤ)) = ((min x (k-1) : ℕ) : ℤ) := by
  unfold memory
  rw [if_pos (show -(n : ℤ) ≤ -1-(x : ℤ) ∧ -1-(x : ℤ)<0 by omega)]
  have hidx : (-1-(-1-(x : ℤ))).toNat = x := by omega
  rw [hidx]

lemma valid_finished (n k w : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ValidLabels n k (finished n k w) := by
  change (∀ x : Point n, 0 ≤ memory n k n (-1-(x.val : ℤ)) ∧
    memory n k n (-1-(x.val : ℤ)) < (k : ℤ)) ∧
    ∀ j : Fin k, ∃ x : Point n, memory n k n (-1-(x.val : ℤ)) = (j.val : ℤ)
  constructor
  · intro x
    rw [memory_label n k x.val x.isLt]
    have hm := Nat.min_le_right x.val (k-1)
    omega
  · intro j
    let x : Point n := ⟨j.val, by omega⟩
    refine ⟨x, ?_⟩
    rw [memory_label n k x.val x.isLt]
    have hj : j.val ≤ k-1 := by omega
    simp only [x, Nat.min_eq_left hj]

/- A concrete deterministic feasible fallback with an exact linear execution count. -/
theorem feasible_execution {n : ℕ} (d : Point n → Point n → ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    let s := execute program n k d (5*n+12)
    s.halted = true ∧ s.work = 5*n+12 ∧ ValidLabels n k s ∧
      Feasible Finset.univ k (outputPartition n k s) := by
  rw [execute_eq d k hk hkn]
  exact ⟨rfl, rfl, valid_finished n k _ hk hkn,
    validLabels_feasible _ (valid_finished n k _ hk hkn)⟩

lemma feasible_one_unique {n : ℕ} {W : Cluster n} {Q : Partition n}
    (hQ : Feasible W 1 Q) : Q = {W} := by
  obtain ⟨C, hC⟩ := Finset.card_eq_one.mp hQ.1
  have hcover := hQ.2.2.2
  rw [hC] at hcover
  have hCW : C = W := by simpa using hcover
  simpa [hCW] using hC

/- The fallback is the exact recovery algorithm when there is one cluster. -/
theorem recovers_one {n : ℕ} (d : Point n → Point n → ℝ)
    (hn : 1 ≤ n) (γ : ℝ) :
    RecoversWithin program n 1 d γ (5*n+12) := by
  obtain ⟨hh, hw, hl, hf⟩ := feasible_execution d 1 (by omega) hn
  refine ⟨5*n+12, le_rfl, hh, hw.le, hl, hf, ?_⟩
  intro O hO
  rw [feasible_one_unique hf, feasible_one_unique hO.1]

end FallbackAux

/- One finite deterministic program produces an exact-k feasible partition on
all valid input sizes in exactly 5n+12 interpreter steps. -/
end StableMSR.Recovery

open StableMSR.Recovery

theorem solution :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
      ∀ (n k : ℕ) (d : Point n → Point n → ℝ), 1 ≤ k → k ≤ n →
        let s := execute P n k d (5*n+12)
        s.halted = true ∧ s.work = 5*n+12 ∧ ValidLabels n k s ∧
          Feasible Finset.univ k (outputPartition n k s) := by
  exact ⟨FallbackAux.program, FallbackAux.deterministic,
    fun _ k d hk hkn => FallbackAux.feasible_execution d k hk hkn⟩

