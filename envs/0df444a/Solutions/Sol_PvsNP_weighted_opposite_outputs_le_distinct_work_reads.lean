-- Prove2me | solution 1 for PvsNP.weighted_opposite_outputs_le_distinct_work_reads
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T03:36:03.348371+00:00
-- url     : https://prove2.me/submissions/fd1a4ecf-3b9f-417f-bc52-f2fbfb52bd07

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Run
import Mathlib

namespace PvsNP.ActualReadCertificate

open Turing Turing.MultiTapeTM
open scoped NNReal

variable {k : ℕ} {Γ Q : Type} {x : List Γ}

private structure Agrees (s : Fin k → Set ℤ) (offset : Fin k → ℤ) (a b : Cfg k Γ Q x) : Prop where
  state : a.state = b.state
  input : a.inputPos = b.inputPos
  heads : ∀ i, b.workTapePos i = a.workTapePos i + offset i
  cells : ∀ i z, z ∈ s i → a.workTapes i z = b.workTapes i (z + offset i)

private noncomputable def command (tm : MultiTapeTM k Γ Q) (a : Cfg k Γ Q x) :=
  a.state.map fun q => tm.tr q a.inputSymbol a.workTapeSymbols

private theorem step_command (tm : MultiTapeTM k Γ Q) (a : Cfg k Γ Q x) :
    tm.step a = (command tm a).elim a (·.apply a) := by
  cases h : a.state with
  | none => simpa only [command,h,Option.map_none,Option.elim_none] using (step_of_halt (tm := tm) h)
  | some q => simpa only [command,h,Option.map_some,Option.elim_some] using (step_of_state (tm := tm) h)

private theorem Agrees.apply {s offset} {a b : Cfg k Γ Q x} (h : Agrees s offset a b)
    (e : Action k Γ Q) : Agrees s offset (e.apply a) (e.apply b) := by
  refine ⟨rfl,by simp only [Action.apply_inputPos,h.input],?_,?_⟩
  · intro i
    simp only [Action.apply_workTapePos,h.heads]
    omega
  · intro i z inside
    have same : (z = a.workTapePos i) ↔ z + offset i = b.workTapePos i := by rw [h.heads]; omega
    simp only [Action.apply_workTapes_eq_ite,← same,h.cells i z inside]

private theorem Agrees.step (tm : MultiTapeTM k Γ Q) {s offset} {a b : Cfg k Γ Q x}
    (h : Agrees s offset a b) (read : a.state.isSome = true → ∀ i, a.workTapePos i ∈ s i) :
    Agrees s offset (tm.step a) (tm.step b) ∧ ∃ w : List Γ,
      (tm.step a).output = a.output ++ w ∧ (tm.step b).output = b.output ++ w := by
  have cmd : command tm a = command tm b := by
    cases ha : a.state with
    | none => simp [command,← h.state,ha]
    | some q =>
      have work : a.workTapeSymbols = b.workTapeSymbols := by
        funext i
        change a.workTapes i (a.workTapePos i) = b.workTapes i (b.workTapePos i)
        rw [h.heads]
        exact h.cells i _ (read (by simp [ha]) i)
      have input : a.inputSymbol = b.inputSymbol := by
        rw [Cfg.inputSymbol_eq_inputAt,Cfg.inputSymbol_eq_inputAt,h.input]
      simp only [command,h.state,input,work]
  rw [step_command,step_command,← cmd]
  cases command tm a with
  | none => exact ⟨h,[],by simp,by simp⟩
  | some act => exact ⟨h.apply act,act.output.toList,rfl,rfl⟩

private theorem replay (tm : MultiTapeTM k Γ Q) {s offset} {a b : Cfg k Γ Q x}
    (h : Agrees s offset a b) (t : ℕ)
    (inside : ∀ j < t, (tm.runFrom a j).state.isSome = true → ∀ i, (tm.runFrom a j).workTapePos i ∈ s i) :
    Agrees s offset (tm.runFrom a t) (tm.runFrom b t) ∧ ∃ w : List Γ,
      (tm.runFrom a t).output = a.output ++ w ∧ (tm.runFrom b t).output = b.output ++ w := by
  induction t with
  | zero => exact ⟨h,[],by simp [MultiTapeTM.runFrom],by simp [MultiTapeTM.runFrom]⟩
  | succ t ih =>
    obtain ⟨agree,w,wa,wb⟩ := ih fun j lt => inside j (by omega)
    obtain ⟨next,v,va,vb⟩ := agree.step tm (inside t (by omega))
    rw [runFrom_succ,runFrom_succ]
    exact ⟨next,w++v,by rw [va,wa,List.append_assoc],by rw [vb,wb,List.append_assoc]⟩

/-- Only initial cells read on the first execution are needed to reproduce its
answer from a second post-prefix configuration. Tape origins and existing output
can differ. All later writes and adaptive choices are permitted. -/
theorem same_answer_of_agree_on_reads (tm : MultiTapeTM k Γ Q) (a b : Cfg k Γ Q x)
    (t : ℕ) (offset : Fin k → ℤ) (control : a.state = b.state)
    (input : a.inputPos = b.inputPos) (heads : ∀ i, b.workTapePos i = a.workTapePos i + offset i)
    (agree : ∀ (j : Fin t), (tm.runFrom a j.val).state.isSome = true → ∀ i, let z := (tm.runFrom a j.val).workTapePos i
      a.workTapes i z = b.workTapes i (z+offset i)) :
    (tm.runFrom a t).state = (tm.runFrom b t).state ∧
    (tm.runFrom a t).output.drop a.output.length = (tm.runFrom b t).output.drop b.output.length := by
  let s (i : Fin k) : Set ℤ := {z | ∃ j : Fin t, (tm.runFrom a j.val).state.isSome = true ∧
    (tm.runFrom a j.val).workTapePos i = z}
  have h : Agrees s offset a b := ⟨control,input,heads,fun i _ ⟨j,live,e⟩ => e ▸ agree j live i⟩
  obtain ⟨sync,w,wa,wb⟩ := replay tm h t (fun j lt live i => ⟨⟨j,lt⟩,live,rfl⟩)
  exact ⟨sync.state,by rw [wa,wb,List.drop_left,List.drop_left]⟩

/-- Normalize the weight that any cell can carry to one. A finite set of
cells meeting all alternatives bounds their total weight even when arbitrarily
many alternatives overlap. -/
private theorem weighted_cover {I P : Type} [Fintype I] [Fintype P]
    (hit : I → P → Prop) [DecidableRel hit] (weight : I → ℝ≥0)
    (cover : ∀ u, ∃ p, hit u p)
    (load : ∀ p, ∑ u, (if hit u p then weight u else 0) ≤ 1) :
    ∑ u, weight u ≤ (Fintype.card P : ℝ≥0) := by
  have row (u : I) : weight u ≤ ∑ p, (if hit u p then weight u else 0) := by
    obtain ⟨p,hp⟩ := cover u
    calc
      weight u = (if hit u p then weight u else 0) := (if_pos hp).symm
      _ ≤ _ := Finset.single_le_sum (f := fun v => if hit u v then weight u else 0)
        (fun _ _ => zero_le) (Finset.mem_univ p)
  calc
    ∑ u, weight u ≤ ∑ u, ∑ p, (if hit u p then weight u else 0) :=
      Finset.sum_le_sum (fun u _ => row u)
    _ = ∑ p, ∑ u, (if hit u p then weight u else 0) := Finset.sum_comm
    _ ≤ ∑ _p : P, (1 : ℝ≥0) := Finset.sum_le_sum (fun p _ => load p)
    _ = _ := by simp

/-- Distinct tape addresses inspected before the clock limit, omitting halted steps. -/
noncomputable def actualCells (tm : MultiTapeTM k Γ Q) (a : Cfg k Γ Q x) (t : ℕ) :
    Finset (Fin k × ℤ) :=
  (Finset.univ.filter (fun j : Fin t × Fin k => (tm.runFrom a j.1.val).state.isSome)).image
    (fun j => (j.2,(tm.runFrom a j.1.val).workTapePos j.2))

/-- For an arbitrary finite set of initially variable cells, a comparison
with a fixed reference execution bounds the weight of opposite-answer
alternatives by the number of distinct cells both variable and actually
read. The alternative executions may inspect other cells. -/
theorem weighted_opposites {I : Type} [Fintype I]
    (tm : MultiTapeTM k Γ Q) (a : Cfg k Γ Q x) (b : I → Cfg k Γ Q x) (t : ℕ)
    (offset : I → Fin k → ℤ) (control : ∀ u, a.state = (b u).state)
    (input : ∀ u, a.inputPos = (b u).inputPos)
    (heads : ∀ u i, (b u).workTapePos i = a.workTapePos i + offset u i)
    (opposite : ∀ u, (tm.runFrom a t).output.drop a.output.length ≠
      (tm.runFrom (b u) t).output.drop (b u).output.length)
    (region : Finset (Fin k × ℤ)) (weight : I → ℝ≥0) [DecidableEq Γ]
    (outside : ∀ u i z, (i,z) ∉ region → a.workTapes i z = (b u).workTapes i (z+offset u i))
    (load : ∀ i z, (∑ u, if a.workTapes i z ≠ (b u).workTapes i (z+offset u i)
      then weight u else 0) ≤ 1) :
    ∑ u, weight u ≤ ((actualCells tm a t ∩ region).card : ℝ≥0) := by
  classical
  let hit (u : I) (p : Fin k × ℤ) :=
    a.workTapes p.1 p.2 ≠ (b u).workTapes p.1 (p.2+offset u p.1)
  let atProbe (r : Fin t × Fin k) : Fin k × ℤ := (r.2,(tm.runFrom a r.1.val).workTapePos r.2)
  let relevant := actualCells tm a t ∩ region
  apply (weighted_cover (P := relevant) (fun u p => hit u p.val) weight ?_
    (fun p => load p.val.1 p.val.2)).trans
  · simp [relevant]
  · intro u
    by_contra! missing
    apply opposite u
    apply (same_answer_of_agree_on_reads tm a (b u) t (offset u) (control u) (input u) (heads u) ?_).2
    intro j live i
    let p := atProbe (j,i)
    have probed : p ∈ actualCells tm a t := Finset.mem_image.mpr
      ⟨(j,i),Finset.mem_filter.mpr ⟨Finset.mem_univ _,live⟩,rfl⟩
    by_cases mem : p ∈ region
    · exact not_ne_iff.mp (missing ⟨p,Finset.mem_inter.mpr ⟨probed,mem⟩⟩)
    · exact outside u p.1 p.2 mem

theorem distinct_relevant_cells_le (tm : MultiTapeTM k Γ Q) (a : Cfg k Γ Q x)
    (t : ℕ) (region : Finset (Fin k × ℤ)) :
    (actualCells tm a t ∩ region).card ≤ min (t*k) region.card := by
  apply le_min _ (Finset.card_le_card Finset.inter_subset_right)
  calc
    _ ≤ (actualCells tm a t).card := Finset.card_le_card Finset.inter_subset_left
    _ ≤ _ := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin t × Fin k)).card := Finset.card_filter_le _ _
    _ = _ := by simp

end PvsNP.ActualReadCertificate

open Turing Turing.MultiTapeTM
open scoped NNReal

theorem solution {k : ℕ} {Γ Q : Type} {x : List Γ} {I : Type} [Fintype I]
    (tm : MultiTapeTM k Γ Q) (a : Cfg k Γ Q x) (b : I → Cfg k Γ Q x) (t : ℕ)
    (offset : I → Fin k → ℤ) (control : ∀ u, a.state = (b u).state)
    (input : ∀ u, a.inputPos = (b u).inputPos)
    (heads : ∀ u i, (b u).workTapePos i = a.workTapePos i + offset u i)
    (opposite : ∀ u, (tm.runFrom a t).output.drop a.output.length ≠
      (tm.runFrom (b u) t).output.drop (b u).output.length)
    (region : Finset (Fin k × ℤ)) (weight : I → ℝ≥0) [DecidableEq Γ]
    (outside : ∀ u i z, (i,z) ∉ region → a.workTapes i z = (b u).workTapes i (z+offset u i))
    (load : ∀ i z, (∑ u, if a.workTapes i z ≠ (b u).workTapes i (z+offset u i)
      then weight u else 0) ≤ 1) :
    let positions : Finset (Fin k × ℤ) :=
      (Finset.univ.filter (fun j : Fin t × Fin k => (tm.runFrom a j.1.val).state.isSome)).image
        (fun j => (j.2,(tm.runFrom a j.1.val).workTapePos j.2))
    ∑ u, weight u ≤ ((positions ∩ region).card : ℝ≥0) :=
  PvsNP.ActualReadCertificate.weighted_opposites tm a b t offset control input heads opposite region weight outside load
