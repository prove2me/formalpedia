-- Prove2me | solution 1 for TwoAgentSched.TotalTotal.CountPositive.correct_and_total
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:46:37.94521+00:00
-- url     : https://prove2.me/submissions/8709c4bc-0f59-478f-a9d5-216e5f912e35

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_CountPositive
import Theorems.Thm_StackProgPortLift_liftProgC_exec
import Theorems.Thm_CookPvsNP_CanonicalBlockParser_execution_and_bounds
import Theorems.Thm_CookPvsNP_stack_transfer

set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace StackProgPortLift

private theorem write_at_local {K L A : Type} (r : K ↪ L) (t : K → List A)
    (s : L → List A) (k : K) : write r t s (r k) = t k := by
  classical
  unfold write
  split
  · rename_i h
    have hk : Classical.choose h = k := r.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

private theorem write_outside_local {K L A : Type} (r : K ↪ L) (t : K → List A)
    (s : L → List A) {l : L} (h : ∀ k, r k ≠ l) : write r t s l = s l := by
  classical
  unfold write
  split
  · rename_i hex
    obtain ⟨k, hk⟩ := hex
    exact (h k hk).elim
  · rfl


end StackProgPortLift


namespace LocalCounterParserProof

open CookPvsNP.CanonicalBlockParser

private theorem readAct_step (b : Bool) (rest acc status : List BSym) :
    StackProg.applyAct readAct (store (digitSym b :: rest) acc status) =
      store rest (digitSym b :: acc) status := by
  funext k
  fin_cases k <;> cases b <;>
    simp [StackProg.applyAct, readAct, store, digitSym, StackAct.apply]

private theorem acceptAct_step (tail acc status : List BSym) :
    StackProg.applyAct acceptAct (store (BSym.sep :: tail) acc status) =
      store tail acc (BSym.one :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, acceptAct, store, StackAct.apply]

private theorem rejectAct_step (rest acc status : List BSym) :
    StackProg.applyAct rejectAct (store rest acc status) =
      store rest acc (BSym.zero :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, rejectAct, store, StackAct.apply]

private theorem scan_exec (digits : List Bool) (stop acc status : List BSym)
    (hstop : isDigit stop.head? = false) :
    (StackProg.loop digitTest (.act readAct)).Exec
      (store (digits.map digitSym ++ stop) acc status)
      (store stop ((digits.map digitSym).reverse ++ acc) status)
      (3 * digits.length + 1) := by
  induction digits generalizing acc with
  | nil =>
    apply StackProg.Exec.loopFalse
    simpa [digitTest, store] using hstop
  | cons b digits ih =>
    have htest : digitTest (fun k ↦ (store (digitSym b ::
        (digits.map digitSym ++ stop)) acc status k).head?) = true := by
      cases b <;> rfl
    have hact : (StackProg.act readAct).Exec
        (store (digitSym b :: (digits.map digitSym ++ stop)) acc status)
        (store (digits.map digitSym ++ stop) (digitSym b :: acc) status) 1 := by
      rw [← readAct_step]
      exact StackProg.Exec.act _ _
    have hloop := StackProg.Exec.loopTrue htest hact (ih (digitSym b :: acc))
    simpa [List.reverse_cons, List.append_assoc, Nat.mul_add,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hloop

/-- A terminated block is consumed and accepted, with exact cost 3d+4. -/
theorem parseBlockProg_success (digits : List Bool) (tail acc status : List BSym) :
    parseBlockProg.Exec
      (store (digits.map digitSym ++ BSym.sep :: tail) acc status)
      (store tail ((digits.map digitSym).reverse ++ acc) (BSym.one :: status))
      (3 * digits.length + 4) := by
  have hs := scan_exec digits (BSym.sep :: tail) acc status (by rfl)
  have hact : (StackProg.act acceptAct).Exec
      (store (BSym.sep :: tail) ((digits.map digitSym).reverse ++ acc) status)
      (store tail ((digits.map digitSym).reverse ++ acc) (BSym.one :: status)) 1 := by
    rw [← acceptAct_step]
    exact StackProg.Exec.act _ _
  have ht : separatorTest (fun k ↦
      (store (BSym.sep :: tail) ((digits.map digitSym).reverse ++ acc) status k).head?) = true := rfl
  have hb : (StackProg.branch separatorTest (.act acceptAct) (.act rejectAct)).Exec
      (store (BSym.sep :: tail) ((digits.map digitSym).reverse ++ acc) status)
      (store tail ((digits.map digitSym).reverse ++ acc) (BSym.one :: status)) 2 :=
    StackProg.Exec.branchTrue ht hact
  have hseq := StackProg.Exec.seq hs hb
  convert hseq using 1 <;> simp [parseBlockProg] <;> omega

/-- A minus sign in place of the separator is rejected and left unconsumed. -/
theorem parseBlockProg_reject_minus (digits : List Bool) (tail acc status : List BSym) :
    parseBlockProg.Exec
      (store (digits.map digitSym ++ BSym.minus :: tail) acc status)
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status))
      (3 * digits.length + 4) := by
  have hs := scan_exec digits (BSym.minus :: tail) acc status (by rfl)
  have hact : (StackProg.act rejectAct).Exec
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) status)
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status)) 1 := by
    rw [← rejectAct_step]
    exact StackProg.Exec.act _ _
  have ht : separatorTest (fun k ↦
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) status k).head?) = false := rfl
  have hb : (StackProg.branch separatorTest (.act acceptAct) (.act rejectAct)).Exec
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) status)
      (store (BSym.minus :: tail) ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status)) 2 :=
    StackProg.Exec.branchFalse ht hact
  have hseq := StackProg.Exec.seq hs hb
  convert hseq using 1 <;> simp [parseBlockProg] <;> omega

/-- End of input in place of the separator is rejected. -/
theorem parseBlockProg_reject_eof (digits : List Bool) (acc status : List BSym) :
    parseBlockProg.Exec
      (store (digits.map digitSym) acc status)
      (store [] ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status))
      (3 * digits.length + 4) := by
  have hs := scan_exec digits [] acc status (by rfl)
  have hact : (StackProg.act rejectAct).Exec
      (store [] ((digits.map digitSym).reverse ++ acc) status)
      (store [] ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status)) 1 := by
    rw [← rejectAct_step]
    exact StackProg.Exec.act _ _
  have ht : separatorTest (fun k ↦
      (store [] ((digits.map digitSym).reverse ++ acc) status k).head?) = false := rfl
  have hb : (StackProg.branch separatorTest (.act acceptAct) (.act rejectAct)).Exec
      (store [] ((digits.map digitSym).reverse ++ acc) status)
      (store [] ((digits.map digitSym).reverse ++ acc) (BSym.zero :: status)) 2 :=
    StackProg.Exec.branchFalse ht hact
  have hseq := StackProg.Exec.seq hs hb
  convert hseq using 1 <;> simp [parseBlockProg] <;> omega


private theorem markTrue_step (input acc status : List BSym) :
    StackProg.applyAct markTrueAct (store input acc status) =
      store input acc (BSym.one :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, markTrueAct, store, StackAct.apply]

private theorem markFalse_step (input acc status : List BSym) :
    StackProg.applyAct markFalseAct (store input acc status) =
      store input acc (BSym.zero :: status) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, markFalseAct, store, StackAct.apply]

/-- Empty blocks and nonempty blocks ending in one are accepted and leave
    their reversed digits available for decoding. -/
theorem parseCanonicalBlockProg_accept (digits : List Bool) (tail status : List BSym)
    (hcanon : digits = [] ∨ ∃ pre, digits = pre ++ [true]) :
    parseCanonicalBlockProg.Exec
      (store (digits.map digitSym ++ BSym.sep :: tail) [] status)
      (store tail (digits.map digitSym).reverse (BSym.one :: BSym.one :: status))
      (3 * digits.length + 7) := by
  have hp : parseBlockProg.Exec
      (store (digits.map digitSym ++ BSym.sep :: tail) [] status)
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (3 * digits.length + 4) := by
    simpa using parseBlockProg_success digits tail [] status
  have ht : canonicalTest (fun k ↦
      (store tail (digits.map digitSym).reverse (BSym.one :: status) k).head?) = true := by
    rcases hcanon with rfl | ⟨pre, rfl⟩
    · rfl
    · simp [canonicalTest, store, List.map_append, List.reverse_append, digitSym]
  have ha : (StackProg.act markTrueAct).Exec
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (store tail (digits.map digitSym).reverse (BSym.one :: BSym.one :: status)) 1 := by
    simpa only [markTrue_step] using
      (StackProg.Exec.act markTrueAct (store tail (digits.map digitSym).reverse (BSym.one :: status)))
  have hb : (StackProg.branch canonicalTest (.act markTrueAct) (.act markFalseAct)).Exec
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (store tail (digits.map digitSym).reverse (BSym.one :: BSym.one :: status)) 2 :=
    StackProg.Exec.branchTrue ht ha
  have hs := StackProg.Exec.seq hp hb
  convert hs using 1 <;> simp [parseCanonicalBlockProg] <;> omega

/-- A nonempty block with most significant digit zero is rejected. -/
theorem parseCanonicalBlockProg_reject_high_zero (pre : List Bool) (tail status : List BSym) :
    parseCanonicalBlockProg.Exec
      (store ((pre ++ [false]).map digitSym ++ BSym.sep :: tail) [] status)
      (store tail ((pre ++ [false]).map digitSym).reverse (BSym.zero :: BSym.one :: status))
      (3 * (pre ++ [false]).length + 7) := by
  let digits := pre ++ [false]
  have hp : parseBlockProg.Exec
      (store (digits.map digitSym ++ BSym.sep :: tail) [] status)
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (3 * digits.length + 4) := by
    simpa using parseBlockProg_success digits tail [] status
  have ht : canonicalTest (fun k ↦
      (store tail (digits.map digitSym).reverse (BSym.one :: status) k).head?) = false := by
    simp [digits, canonicalTest, store, List.map_append, List.reverse_append, digitSym]
  have ha : (StackProg.act markFalseAct).Exec
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (store tail (digits.map digitSym).reverse (BSym.zero :: BSym.one :: status)) 1 := by
    rw [← markFalse_step]
    exact StackProg.Exec.act _ _
  have hb : (StackProg.branch canonicalTest (.act markTrueAct) (.act markFalseAct)).Exec
      (store tail (digits.map digitSym).reverse (BSym.one :: status))
      (store tail (digits.map digitSym).reverse (BSym.zero :: BSym.one :: status)) 2 :=
    StackProg.Exec.branchFalse ht ha
  have hs := StackProg.Exec.seq hp hb
  convert hs using 1 <;> simp [parseCanonicalBlockProg, digits] <;> omega


/-- A minus sign where the delimiter is required remains rejected by the full
    two-stage parser, regardless of the scanned digit sequence. -/
theorem parseCanonicalBlockProg_reject_minus (digits : List Bool) (tail status : List BSym) :
    parseCanonicalBlockProg.Exec
      (store (digits.map digitSym ++ BSym.minus :: tail) [] status)
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status))
      (3 * digits.length + 7) := by
  have hp : parseBlockProg.Exec
      (store (digits.map digitSym ++ BSym.minus :: tail) [] status)
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: status))
      (3 * digits.length + 4) := by
    simpa using parseBlockProg_reject_minus digits tail [] status
  have ht : canonicalTest (fun k ↦
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: status) k).head?) = false := by
    simp [canonicalTest, store]
  have ha : (StackProg.act markFalseAct).Exec
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: status))
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status)) 1 := by
    simpa only [markFalse_step] using
      (StackProg.Exec.act markFalseAct
        (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: status)))
  have hb : (StackProg.branch canonicalTest (.act markTrueAct) (.act markFalseAct)).Exec
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: status))
      (store (BSym.minus :: tail) (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status)) 2 :=
    StackProg.Exec.branchFalse ht ha
  have hs := StackProg.Exec.seq hp hb
  convert hs using 1 <;> simp [parseCanonicalBlockProg] <;> omega

/-- A missing separator at end of input remains rejected by both stages. -/
theorem parseCanonicalBlockProg_reject_eof (digits : List Bool) (status : List BSym) :
    parseCanonicalBlockProg.Exec
      (store (digits.map digitSym) [] status)
      (store [] (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status))
      (3 * digits.length + 7) := by
  have hp : parseBlockProg.Exec
      (store (digits.map digitSym) [] status)
      (store [] (digits.map digitSym).reverse (BSym.zero :: status))
      (3 * digits.length + 4) := by
    simpa using parseBlockProg_reject_eof digits [] status
  have ht : canonicalTest (fun k ↦
      (store [] (digits.map digitSym).reverse (BSym.zero :: status) k).head?) = false := by
    simp [canonicalTest, store]
  have ha : (StackProg.act markFalseAct).Exec
      (store [] (digits.map digitSym).reverse (BSym.zero :: status))
      (store [] (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status)) 1 := by
    simpa only [markFalse_step] using
      (StackProg.Exec.act markFalseAct (store [] (digits.map digitSym).reverse (BSym.zero :: status)))
  have hb : (StackProg.branch canonicalTest (.act markTrueAct) (.act markFalseAct)).Exec
      (store [] (digits.map digitSym).reverse (BSym.zero :: status))
      (store [] (digits.map digitSym).reverse (BSym.zero :: BSym.zero :: status)) 2 :=
    StackProg.Exec.branchFalse ht ha
  have hs := StackProg.Exec.seq hp hb
  convert hs using 1 <;> simp [parseCanonicalBlockProg] <;> omega

end LocalCounterParserProof

namespace CookPvsNP.CanonicalBlockParser

private theorem digit_end_cases (digits : List Bool) :
    digits = [] ∨ (∃ pre, digits = pre ++ [true]) ∨ ∃ pre, digits = pre ++ [false] := by
  cases hr : digits.reverse with
  | nil =>
    left
    have h := congrArg List.reverse hr
    simpa using h
  | cons b pre =>
    have h : digits = pre.reverse ++ [b] := by
      have h' := congrArg List.reverse hr
      simpa using h'
    cases b with
    | false => exact Or.inr (Or.inr ⟨pre.reverse, h⟩)
    | true => exact Or.inr (Or.inl ⟨pre.reverse, h⟩)

/-- Every alphabet string decomposes into its maximal 0/1 prefix followed by
    a separator, a minus sign, or end of input. -/
private theorem split_digit_prefix (input : List BSym) :
    ∃ digits : List Bool, ∃ stop : List BSym,
      input = digits.map digitSym ++ stop ∧
        (stop = [] ∨ (∃ tail, stop = BSym.sep :: tail) ∨ ∃ tail, stop = BSym.minus :: tail) := by
  induction input with
  | nil => exact ⟨[], [], rfl, Or.inl rfl⟩
  | cons a input ih =>
    cases a with
    | zero =>
      obtain ⟨digits, stop, heq, hstop⟩ := ih
      refine ⟨false :: digits, stop, ?_, hstop⟩
      simp [digitSym, heq]
    | one =>
      obtain ⟨digits, stop, heq, hstop⟩ := ih
      refine ⟨true :: digits, stop, ?_, hstop⟩
      simp [digitSym, heq]
    | minus => exact ⟨[], BSym.minus :: input, by simp, Or.inr (Or.inr ⟨input, rfl⟩)⟩
    | sep => exact ⟨[], BSym.sep :: input, by simp, Or.inr (Or.inl ⟨input, rfl⟩)⟩

private theorem exec_det_local {K A : Type} {p : StackProg K A} {s t : K → List A} {n : ℕ}
    (h : p.Exec s t n) : ∀ {u : K → List A} {m : ℕ}, p.Exec s u m → t = u := by
  induction h with
  | act f s =>
      intro u m h2
      cases h2
      rfl
  | seq hab hbc ihab ihbc =>
      intro u m h2
      cases h2 with
      | seq hab' hbc' =>
          have e : _ = _ := ihab hab'
          rw [← e] at hbc'
          exact ihbc hbc'
  | branchTrue ht hb ih =>
      intro u m h2
      cases h2 with
      | branchTrue _ hb' => exact ih hb'
      | branchFalse hf _ =>
          rw [ht] at hf
          cases hf
  | branchFalse ht hb ih =>
      intro u m h2
      cases h2 with
      | branchFalse _ hb' => exact ih hb'
      | branchTrue hf _ =>
          rw [ht] at hf
          cases hf
  | loopFalse ht =>
      intro u m h2
      cases h2 with
      | loopFalse _ => rfl
      | loopTrue ht' _ _ =>
          rw [ht] at ht'
          cases ht'
  | loopTrue ht hb hrest ihab ihrest =>
      intro u m h2
      cases h2 with
      | loopFalse ht' =>
          rw [ht] at ht'
          cases ht'
      | loopTrue _ hb' hrest' =>
          have e : _ = _ := ihab hb'
          rw [← e] at hrest'
          exact ihrest hrest'






private theorem success_progress_local (input status rest digits markerTail : List BSym) (steps : ℕ)
    (h : parseCanonicalBlockProg.Exec
      (store input [] status) (store rest digits (.one :: markerTail)) steps) :
    rest.length < input.length := by
  obtain ⟨preBits, stop, hw, hstop⟩ := split_digit_prefix input
  subst input
  rcases hstop with hempty | ⟨tail, hsep⟩ | ⟨tail, hminus⟩
  · subst stop
    simp only [List.append_nil] at h
    have hbad := LocalCounterParserProof.parseCanonicalBlockProg_reject_eof preBits status
    have heq := exec_det_local h hbad
    have hc := congrFun heq (2 : Fin 3)
    simp [store] at hc
  · subst stop
    have finish {outdigits outstatus : List BSym} {k : ℕ}
        (hrun : parseCanonicalBlockProg.Exec
          (store (preBits.map digitSym ++ BSym.sep :: tail) [] status)
          (store tail outdigits outstatus) k) : rest.length < (preBits.map digitSym ++ BSym.sep :: tail).length := by
      have heq := exec_det_local h hrun
      have hr : rest = tail := by simpa [store] using congrFun heq (0 : Fin 3)
      rw [hr]
      simp only [List.length_append, List.length_map, List.length_cons]
      omega
    rcases digit_end_cases preBits with hnil | ⟨pre, htrue⟩ | ⟨pre, hfalse⟩
    · exact finish (LocalCounterParserProof.parseCanonicalBlockProg_accept preBits tail status (Or.inl hnil))
    · exact finish (LocalCounterParserProof.parseCanonicalBlockProg_accept preBits tail status (Or.inr ⟨pre, htrue⟩))
    · subst preBits
      exact finish (LocalCounterParserProof.parseCanonicalBlockProg_reject_high_zero pre tail status)
  · subst stop
    have hbad := LocalCounterParserProof.parseCanonicalBlockProg_reject_minus preBits tail status
    have heq := exec_det_local h hbad
    have hc := congrFun heq (2 : Fin 3)
    simp [store] at hc

end CookPvsNP.CanonicalBlockParser

namespace TwoAgentSched.TotalTotal.CountPositive

open StackProgPortLift CookPvsNP.CanonicalBlockParser

private theorem parseInverse_correct (l : Fin 4) (k : Fin 3) :
    parseInverse l = some k ↔ parsePorts k = l := by fin_cases l <;> fin_cases k <;> decide

private theorem write_parse (a b c input digits status count : List BSym) :
    write parsePorts (CookPvsNP.CanonicalBlockParser.store a b c) (store4 input digits status count) =
      store4 a b c count := by
  funext k
  fin_cases k
  · simpa [parsePorts, CookPvsNP.CanonicalBlockParser.store, store4] using
      (StackProgPortLift.write_at_local parsePorts (CookPvsNP.CanonicalBlockParser.store a b c) (store4 input digits status count) (0 : Fin 3))
  · simpa [parsePorts, CookPvsNP.CanonicalBlockParser.store, store4] using
      (StackProgPortLift.write_at_local parsePorts (CookPvsNP.CanonicalBlockParser.store a b c) (store4 input digits status count) (1 : Fin 3))
  · simpa [parsePorts, CookPvsNP.CanonicalBlockParser.store, store4] using
      (StackProgPortLift.write_at_local parsePorts (CookPvsNP.CanonicalBlockParser.store a b c) (store4 input digits status count) (2 : Fin 3))
  · have ho : ∀ j : Fin 3, parsePorts j ≠ (3 : Fin 4) := by intro j; fin_cases j <;> decide
    simpa [store4] using StackProgPortLift.write_outside_local parsePorts (CookPvsNP.CanonicalBlockParser.store a b c)
      (store4 input digits status count) ho

private theorem parse_exec4 (input digits status count input' digits' status' : List BSym)
    (steps : ℕ) (h : parseCanonicalBlockProg.Exec
      (CookPvsNP.CanonicalBlockParser.store input digits status) (CookPvsNP.CanonicalBlockParser.store input' digits' status') steps) :
    (liftProgC parsePorts parseInverse parseCanonicalBlockProg).Exec
      (store4 input digits status count) (store4 input' digits' status' count) steps := by
  have hp : project parsePorts (store4 input digits status count) = CookPvsNP.CanonicalBlockParser.store input digits status := by
    funext k
    fin_cases k <;> simp [project, parsePorts, store4, CookPvsNP.CanonicalBlockParser.store]
  have hr := liftProgC_exec parsePorts parseInverse parseInverse_correct h (store4 input digits status count) hp
  rw [write_parse] at hr
  exact hr

private theorem increment_step (input digits status count : List BSym) :
    StackProg.applyAct incrementAct (store4 input digits status count) = store4 input digits status (.one :: count) := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, incrementAct, store4, StackAct.apply]
private theorem keep_step (input digits status count : List BSym) :
    StackProg.applyAct keepAct (store4 input digits status count) = store4 input digits status count := by
  funext k
  fin_cases k <;> simp [StackProg.applyAct, keepAct, store4, StackAct.apply]

/-- A valid canonical block contributes one marker exactly when it has digits. -/
theorem countBody_encNat (m : ℕ) (tail status count : List BSym) :
    countBody.Exec (store4 (encNat m ++ tail) [] status count)
      (store4 tail [] (.one :: .one :: status)
        (if m.bits = [] then count else .one :: count)) (6 * m.bits.length + 12) := by
  let ds := (m.bits.map CookPvsNP.CanonicalBlockParser.digitSym).reverse
  let st := BSym.one :: BSym.one :: status
  let ct := if m.bits = [] then count else BSym.one :: count
  have hp := parse_exec4 (encNat m ++ tail) [] status count tail ds st
    (3 * m.bits.length + 7) (CookPvsNP.CanonicalBlockParser.execution_and_bounds.1 m tail status)
  have hb : (StackProg.branch incrementTest (.act incrementAct) (.act keepAct)).Exec
      (store4 tail ds st count) (store4 tail ds st ct) 2 := by
    by_cases hz : m.bits = []
    · have ht : incrementTest (fun k => (store4 tail ds st count k).head?) = false := by
        simp [incrementTest, store4, ds, st, hz]
      have ha : (StackProg.act keepAct).Exec (store4 tail ds st count) (store4 tail ds st count) 1 := by
        rw [← keep_step]
        exact StackProg.Exec.act _ _
      simpa [ct, hz] using StackProg.Exec.branchFalse (p := .act incrementAct) ht ha
    · have hds : ds ≠ [] := by simpa [ds] using hz
      have ht : incrementTest (fun k => (store4 tail ds st count k).head?) = true := by
        cases h : ds with
        | nil => exact (hds h).elim
        | cons a xs => simp [incrementTest, store4, st, h]
      have ha : (StackProg.act incrementAct).Exec (store4 tail ds st count)
          (store4 tail ds st (.one :: count)) 1 := by
        rw [← increment_step]
        exact StackProg.Exec.act _ _
      simpa [ct, hz] using StackProg.Exec.branchTrue (q := .act keepAct) ht ha
  have hc := CookPvsNP.stack_transfer (1 : Fin 4) (fun _ => false) (store4 tail ds st ct)
  have hstore : transferStore (1 : Fin 4) (fun _ => false) (store4 tail ds st ct) = store4 tail [] st ct := by
    funext k
    fin_cases k <;> simp [transferStore, store4]
  rw [hstore] at hc
  have hseq := StackProg.Exec.seq hp (StackProg.Exec.seq hb hc)
  simp only [store4, ds, List.length_reverse, List.length_map] at hseq
  unfold countBody clearProg
  convert hseq using 1 <;> simp [st, ct, store4] <;> omega


/-- Number of source blocks whose canonical digit string is nonempty. -/
def nonzeroCount : List ℕ → ℕ
  | [] => 0
  | m :: ms => (if m.bits = [] then 0 else 1) + nonzeroCount ms

/-- Exact source cost of scanning all canonical blocks, including final guard. -/
def countCost : List ℕ → ℕ
  | [] => 1
  | m :: ms => 6 * m.bits.length + 14 + countCost ms

/-- On a canonical list of input blocks, the loop counts all nonzero blocks,
    consumes the input, and records the exact source-step cost. -/
theorem countPositive_encNats (xs : List ℕ) (status count : List BSym)
    (hs : status.head? = some .one) :
    countPositive.Exec (store4 (encNats xs) [] status count)
      (store4 [] [] (List.replicate (2 * xs.length) .one ++ status)
        (List.replicate (nonzeroCount xs) .one ++ count)) (countCost xs) := by
  induction xs generalizing status count with
  | nil =>
    apply StackProg.Exec.loopFalse
    rfl
  | cons m ms ih =>
    have hg : continueTest (fun k => (store4 (encNats (m :: ms)) [] status count k).head?) = true := by
      cases hb : m.bits <;> simp [continueTest, store4, encNats, encNat, hb, hs]
    have hb := countBody_encNat m (encNats ms) status count
    have hi := ih (.one :: .one :: status) (if m.bits = [] then count else .one :: count) (by rfl)
    have hloop := StackProg.Exec.loopTrue hg hb hi
    have hrep (k : ℕ) (out : List BSym) :
        List.replicate k BSym.one ++ BSym.one :: out =
          BSym.one :: (List.replicate k BSym.one ++ out) := by
      induction k with
      | zero => rfl
      | succ k ih => simp [List.replicate_succ, ih]
    have hcost : 1 + (6 * m.bits.length + 12) + 1 + countCost ms =
        6 * m.bits.length + 14 + countCost ms := by omega
    rw [hcost] at hloop
    by_cases hz : m.bits = []
    · simp only [if_pos hz, hrep] at hloop
      simpa [countPositive, countCost, nonzeroCount, encNats, hz, List.replicate_add,
        List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hloop
    · simp only [if_neg hz, hrep] at hloop
      simpa [countPositive, countCost, nonzeroCount, encNats, hz, List.replicate_add,
        List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hloop



/-- The empty canonical digit string represents exactly zero. -/
theorem bits_empty_iff (m : ℕ) : m.bits = [] ↔ m = 0 := by
  constructor
  · intro h
    have hh : m.bits.length = 0 := by rw [h]; rfl
    rw [Nat.size_eq_bits_len, Nat.size_eq_zero] at hh
    exact hh
  · intro h
    subst m
    simp

/-- The unary count equals the number of nonzero source weights. -/
theorem nonzeroCount_eq_filter (xs : List ℕ) :
    nonzeroCount xs = (xs.filter (fun m => m ≠ 0)).length := by
  induction xs with
  | nil => rfl
  | cons m ms ih =>
    by_cases hm : m = 0 <;> simp [nonzeroCount, bits_empty_iff, hm, ih, Nat.add_comm]

/-- The full scan takes linear source steps in the actual encoded input size. -/
theorem countCost_le_encoded_length (xs : List ℕ) :
    countCost xs ≤ 14 * (encNats xs).length + 1 := by
  induction xs with
  | nil => simp [countCost, encNats]
  | cons m ms ih =>
    simp only [countCost, encNats, List.flatMap_cons, List.length_append, encNat,
      List.length_map, List.length_singleton] at *
    omega


end TwoAgentSched.TotalTotal.CountPositive
namespace TwoAgentSched.TotalTotal.CountPositive

open StackProgPortLift CookPvsNP.CanonicalBlockParser

/-- One scan iteration terminates on any input. It exposes the underlying
    parser run so a success/progress theorem can justify the outer loop. -/
theorem countBody_any (input status count : List BSym) :
    ∃ rest digits outstatus outcount parserSteps bodySteps,
      parseCanonicalBlockProg.Exec (CookPvsNP.CanonicalBlockParser.store input [] status)
        (CookPvsNP.CanonicalBlockParser.store rest digits outstatus) parserSteps ∧
      countBody.Exec (store4 input [] status count) (store4 rest [] outstatus outcount) bodySteps ∧
      rest.length ≤ input.length ∧ bodySteps ≤ 6 * input.length + 12 := by
  obtain ⟨rest, digits, outstatus, parserSteps, hp, hk, hd, hr⟩ :=
    CookPvsNP.CanonicalBlockParser.execution_and_bounds.2 input status
  let heads := fun k => (store4 rest digits outstatus count k).head?
  let outcount := if incrementTest heads then BSym.one :: count else count
  have hlift := parse_exec4 input [] status count rest digits outstatus parserSteps hp
  have hb : (StackProg.branch incrementTest (.act incrementAct) (.act keepAct)).Exec
      (store4 rest digits outstatus count) (store4 rest digits outstatus outcount) 2 := by
    cases ht : incrementTest heads with
    | false =>
      have ha : (StackProg.act keepAct).Exec (store4 rest digits outstatus count)
          (store4 rest digits outstatus count) 1 := by
        rw [← keep_step]
        exact StackProg.Exec.act _ _
      simpa [heads, outcount, ht] using StackProg.Exec.branchFalse (p := .act incrementAct) ht ha
    | true =>
      have ha : (StackProg.act incrementAct).Exec (store4 rest digits outstatus count)
          (store4 rest digits outstatus (.one :: count)) 1 := by
        rw [← increment_step]
        exact StackProg.Exec.act _ _
      simpa [heads, outcount, ht] using StackProg.Exec.branchTrue (q := .act keepAct) ht ha
  have hc := CookPvsNP.stack_transfer (1 : Fin 4) (fun _ => false) (store4 rest digits outstatus outcount)
  have hstore : transferStore (1 : Fin 4) (fun _ => false) (store4 rest digits outstatus outcount) =
      store4 rest [] outstatus outcount := by
    funext k
    fin_cases k <;> simp [transferStore, store4]
  rw [hstore] at hc
  have hseq := StackProg.Exec.seq hlift (StackProg.Exec.seq hb hc)
  refine ⟨rest, digits, outstatus, outcount, parserSteps, parserSteps + 3 * digits.length + 5,
    hp, ?_, hr, ?_⟩
  · simp only [store4] at hseq
    unfold countBody clearProg
    convert hseq using 1 <;> simp [store4] <;> omega
  · omega

end TwoAgentSched.TotalTotal.CountPositive

namespace TwoAgentSched.TotalTotal.CountPositive

open CookPvsNP.CanonicalBlockParser

/-- Assuming the parser's independently proved success-progress property, the
    count loop halts on every input with a quadratic source-step bound. -/
theorem countPositive_total_of_progress
    (progress : ∀ (input status rest digits markerTail : List BSym) (steps : ℕ),
      parseCanonicalBlockProg.Exec (CookPvsNP.CanonicalBlockParser.store input [] status)
        (CookPvsNP.CanonicalBlockParser.store rest digits (.one :: markerTail)) steps →
      rest.length < input.length)
    (input status count : List BSym) :
    ∃ (out : Fin 4 → List BSym) (steps : ℕ),
      countPositive.Exec (store4 input [] status count) out steps ∧
        steps ≤ 10 * (input.length + 1) ^ 2 := by
  have hloop : ∀ N : ℕ, ∀ input status count : List BSym, input.length ≤ N →
      ∃ (out : Fin 4 → List BSym) (steps : ℕ),
        countPositive.Exec (store4 input [] status count) out steps ∧
          steps ≤ 10 * (N + 1) ^ 2 := by
    intro N
    induction N with
    | zero =>
      intro input status count hlen
      have hempty : input = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst input
      have hfalse : continueTest (fun k => (store4 [] [] status count k).head?) = false := by
        simp [continueTest, store4]
      refine ⟨store4 [] [] status count, 1, ?_, by norm_num⟩
      simpa [countPositive] using
        (StackProg.Exec.loopFalse (test := continueTest) (p := countBody) hfalse)
    | succ N ih =>
      intro input status count hlen
      cases hg : continueTest (fun k => (store4 input [] status count k).head?) with
      | false =>
        refine ⟨store4 input [] status count, 1, ?_, ?_⟩
        · simpa [countPositive] using
            (StackProg.Exec.loopFalse (test := continueTest) (p := countBody) hg)
        · nlinarith
      | true =>
        obtain ⟨rest, digits, outstatus, outcount, parserSteps, bodySteps, hp, hb, hr, hcost⟩ :=
          countBody_any input status count
        by_cases hs : outstatus.head? = some .one
        · have hstrict : rest.length < input.length := by
            cases hst : outstatus with
            | nil => simp [hst] at hs
            | cons x xs =>
              have hx : x = BSym.one := by simpa [hst] using hs
              subst x
              rw [hst] at hp
              exact progress input status rest digits xs parserSteps hp
          have hrest : rest.length ≤ N := by omega
          obtain ⟨out, afterSteps, hafter, hbudget⟩ := ih rest outstatus outcount hrest
          have hrun := StackProg.Exec.loopTrue hg hb hafter
          refine ⟨out, 1 + bodySteps + 1 + afterSteps, ?_, ?_⟩
          · simpa [countPositive] using hrun
          · nlinarith
        · have hstop : continueTest (fun k => (store4 rest [] outstatus outcount k).head?) = false := by
            simp [continueTest, store4, hs]
          have hafter := StackProg.Exec.loopFalse (test := continueTest) (p := countBody) hstop
          have hrun := StackProg.Exec.loopTrue hg hb hafter
          refine ⟨store4 rest [] outstatus outcount, 1 + bodySteps + 1 + 1, ?_, ?_⟩
          · simpa [countPositive] using hrun
          · nlinarith
  exact hloop input.length input status count (Nat.le_refl _)

end TwoAgentSched.TotalTotal.CountPositive


namespace TwoAgentSched.TotalTotal.CountPositive

open CookPvsNP.CanonicalBlockParser

theorem countPositive_total (input status count : List BSym) :
    ∃ (out : Fin 4 → List BSym) (steps : ℕ),
      countPositive.Exec (store4 input [] status count) out steps ∧
        steps ≤ 10 * (input.length + 1) ^ 2 := by
  apply countPositive_total_of_progress
  intro input status rest digits markerTail steps h
  exact CookPvsNP.CanonicalBlockParser.success_progress_local
    input status rest digits markerTail steps h

end TwoAgentSched.TotalTotal.CountPositive


open TwoAgentSched.TotalTotal.CountPositive

theorem solution :
    (∀ (xs : List ℕ) (status count : List BSym), status.head? = some .one →
      ∃ steps : ℕ,
        countPositive.Exec (store4 (encNats xs) [] status count)
          (store4 [] [] (List.replicate (2 * xs.length) .one ++ status)
            (List.replicate (xs.filter (fun m => m ≠ 0)).length .one ++ count)) steps ∧
        steps ≤ 14 * (encNats xs).length + 1) ∧
    (∀ input status count : List BSym, ∃ (out : Fin 4 → List BSym) (steps : ℕ),
      countPositive.Exec (store4 input [] status count) out steps ∧
        steps ≤ 10 * (input.length + 1) ^ 2) := by
  constructor
  · intro xs status count hs
    refine ⟨countCost xs, ?_, countCost_le_encoded_length xs⟩
    simpa [nonzeroCount_eq_filter] using countPositive_encNats xs status count hs
  · exact countPositive_total

#print axioms solution
