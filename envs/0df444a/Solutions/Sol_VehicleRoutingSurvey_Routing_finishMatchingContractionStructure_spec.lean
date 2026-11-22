-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.finishMatchingContractionStructure_spec
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T16:20:53.652871+00:00
-- url     : https://prove2.me/submissions/71276fb8-0342-41bd-af3a-ada19b672140

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_ContractionStructure
import Theorems.Thm_VehicleRoutingSurvey_Routing_writeMatchingContractionCycle_spec

/-! matching/WeightedReadDeltaRAM.lean -/
section RppSource_WeightedReadDeltaRAM
namespace VehicleRoutingSurvey.Routing

def naturalDestination : ArithmeticInstruction → ℕ
  | .natAdd dst _ _ | .natSub dst _ _ | .natConst dst _ | .natLoad dst _ => dst
  | _ => 0

private theorem arithmeticStep_keeps_register {p : List ArithmeticInstruction}
    {s : ArithmeticState} {r : ℕ} (otherWrites : ∀ ins ∈ p, naturalDestination ins ≠ r) :
    (arithmeticStep p s).nr r = s.nr r := by
  by_cases halted : s.halted = true
  · simp [arithmeticStep, halted]
  cases fetch : p[s.pc]? with
  | none => simp [arithmeticStep, halted, fetch]
  | some ins =>
    have writes := otherWrites ins (List.mem_of_getElem? fetch)
    cases ins <;> simp (disch := omega) [arithmeticStep, halted, fetch, naturalDestination] at writes ⊢

theorem arithmeticRun_keeps_register {p : List ArithmeticInstruction}
    {r : ℕ} (otherWrites : ∀ ins ∈ p, naturalDestination ins ≠ r) (s : ArithmeticState) (steps : ℕ) :
    ((arithmeticStep p)^[steps] s).nr r = s.nr r := by
  induction steps with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', arithmeticStep_keeps_register otherWrites, ih]



theorem naturalDestination_ne_of_list {p : List ArithmeticInstruction} {r : ℕ}
    (written : List ℕ) (checked : p.all (fun ins => decide (naturalDestination ins ∈ written)) = true)
    (away : r ∉ written) : ∀ ins ∈ p, naturalDestination ins ≠ r := by
  intro ins present same
  apply away
  exact same ▸ of_decide_eq_true (List.all_eq_true.mp checked ins present)

theorem arithmeticRun_keeps_from_destination_list {p : List ArithmeticInstruction} {r : ℕ}
    (written : List ℕ) (checked : p.all (fun ins => decide (naturalDestination ins ∈ written)) = true)
    (away : r ∉ written) (s : ArithmeticState) (steps : ℕ) :
    ((arithmeticStep p)^[steps] s).nr r = s.nr r :=
  arithmeticRun_keeps_register (naturalDestination_ne_of_list written checked away) s steps



































end VehicleRoutingSurvey.Routing
end RppSource_WeightedReadDeltaRAM

/-! matching/MatchingEventDispatchRAM.lean -/
section RppSource_MatchingEventDispatchRAM
namespace VehicleRoutingSurvey.Routing



@[simp] theorem branchOnAtMost_length (x y : ℕ) (left right : List ArithmeticInstruction) :
    (branchOnAtMost x y left right).length = 2 + left.length + right.length := by
  simp [branchOnAtMost] <;> omega



theorem branchOnAtMost_left (x y : ℕ) (left right : List ArithmeticInstruction)
    {s t : ArithmeticState} {ticks : ℕ} (entry : s.pc = 0) (running : s.halted = false)
    (atMost : s.nr x ≤ s.nr y) (ran : BlockRuns left ticks s t) (live : t.halted = false) :
    BlockRuns (branchOnAtMost x y left right) (1 + ticks + 1) s
      {t with pc := (branchOnAtMost x y left right).length} := by
  let program := branchOnAtMost x y left right
  have enter : arithmeticStep program s = relocateState 1 s := by
    simp [program, branchOnAtMost, arithmeticStep, entry, running, atMost, relocateState]
  have body : (arithmeticStep program)^[ticks] (relocateState 1 s) = relocateState 1 t := by
    have executed := arithmeticIterate_relocate [.natBranch x y 1 (2 + left.length)] left
      ([.jump (2 + left.length + right.length)] ++ right.map (relocateInstruction (2 + left.length)))
      s ticks ran.inside
    simpa [program, branchOnAtMost, List.append_assoc, ran.run] using executed
  have afterLeft : (relocateState 1 t).pc = 1 + left.length := by simp [relocateState, ran.exit]
  have fetched : program[(relocateState 1 t).pc]? = some (.jump program.length) := by
    rw [afterLeft]
    let front : List ArithmeticInstruction := [.natBranch x y 1 (2 + left.length)] ++ left.map (relocateInstruction 1)
    let back : List ArithmeticInstruction :=
      [.jump (2 + left.length + right.length)] ++ right.map (relocateInstruction (2 + left.length))
    have frontLength : front.length = 1 + left.length := by simp [front, Nat.add_comm]
    have layout : program = front ++ back := by simp only [program, branchOnAtMost, front, back, List.append_assoc]
    have lengthAt : program.length = 2 + left.length + right.length := branchOnAtMost_length x y left right
    rw [lengthAt, layout, List.getElem?_append_right (by rw [frontLength])]
    simp [frontLength, back]
  have leave : arithmeticStep program (relocateState 1 t) = {t with pc := program.length} := by
    have stillRunning : (relocateState 1 t).halted = false := live
    unfold arithmeticStep
    simp only [stillRunning, Bool.false_eq_true, if_false, fetched]
    simp [relocateState, live]
  apply BlockRuns.of_running_exit
  · change (arithmeticStep program)^[1 + ticks + 1] s = {t with pc := program.length}
    rw [Function.iterate_succ_apply', Nat.add_comm 1 ticks, Function.iterate_add_apply, Function.iterate_one,
      enter, body, leave]
  · exact live
  · rfl

theorem branchOnAtMost_right (x y : ℕ) (left right : List ArithmeticInstruction)
    {s t : ArithmeticState} {ticks : ℕ} (entry : s.pc = 0) (running : s.halted = false)
    (larger : s.nr y < s.nr x) (ran : BlockRuns right ticks s t) (live : t.halted = false) :
    BlockRuns (branchOnAtMost x y left right) (1 + ticks) s
      {t with pc := (branchOnAtMost x y left right).length} := by
  let program := branchOnAtMost x y left right
  let front : List ArithmeticInstruction :=
    [.natBranch x y 1 (2 + left.length)] ++ left.map (relocateInstruction 1) ++ [.jump (2 + left.length + right.length)]
  have frontLength : front.length = 2 + left.length := by simp [front] <;> omega
  have enter : arithmeticStep program s = relocateState front.length s := by
    simp [program, branchOnAtMost, arithmeticStep, entry, running, not_le.mpr larger, relocateState, frontLength]
  have body : (arithmeticStep program)^[ticks] (relocateState front.length s) = relocateState front.length t := by
    have layout : program = front ++ right.map (relocateInstruction front.length) ++ [] := by
      rw [frontLength]
      simp [program, branchOnAtMost, front, List.append_assoc]
    rw [layout]
    simpa only [ran.run] using
      arithmeticIterate_relocate front right [] s ticks ran.inside
  apply BlockRuns.of_running_exit
  · rw [Nat.add_comm 1 ticks, Function.iterate_add_apply, Function.iterate_one, enter, body]
    simp [relocateState, frontLength, ran.exit]
  · exact live
  · rfl





end VehicleRoutingSurvey.Routing
end RppSource_MatchingEventDispatchRAM

/-! matching/MatchingContractRowsRAM.lean -/
section RppSource_MatchingContractRowsRAM
namespace VehicleRoutingSurvey.Routing













private structure AppendedTracedOuterRep (s t : ArithmeticState) (steps : ℕ) : Prop where
  run : BlockRuns appendTracedOuterRep steps s t
  running : t.halted = false
  count : t.nr 87 = s.nr 87 + (if tracedRepresentativeOuter s (s.nr 7) then 1 else 0)
  natEffect : t.nm = if tracedRepresentativeOuter s (s.nr 7) then
      Function.update s.nm (s.nr 86 + s.nr 87) (tracedRepresentative s (s.nr 7))
    else s.nm
  realEffect : t.rm = s.rm

private theorem appendTracedOuterRep_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) : ∃ t steps, steps ≤ 10 ∧ AppendedTracedOuterRep s t steps := by
  rcases lt_trichotomy (s.nm (s.nr 51 + s.nm (s.nr 18 + s.nr 7))) 1 with below | equal | above
  · let t := (arithmeticStep appendTracedOuterRep)^[6] s
    have effect : t.pc = appendTracedOuterRep.length ∧ t.halted = false ∧
        t.nr 87 = s.nr 87 ∧ t.nm = s.nm ∧ t.rm = s.rm := by
      simp [t, appendTracedOuterRep, arithmeticStep, entry, running, Function.iterate_succ_apply',
        one, below.le, not_le.mpr below]
    have notOuter : ¬ tracedRepresentativeOuter s (s.nr 7) := by
      simpa [tracedRepresentativeOuter, tracedRepresentative] using below.ne
    exact ⟨t, 6, by decide, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1,
      by simpa [notOuter] using effect.2.2.1, by simpa [notOuter] using effect.2.2.2.1, effect.2.2.2.2⟩
  · let t := (arithmeticStep appendTracedOuterRep)^[10] s
    have effect : t.pc = appendTracedOuterRep.length ∧ t.halted = false ∧ t.nr 87 = s.nr 87 + 1 ∧
        t.nm = Function.update s.nm (s.nr 86 + s.nr 87) (tracedRepresentative s (s.nr 7)) ∧ t.rm = s.rm := by
      simp [t, appendTracedOuterRep, arithmeticStep, entry, running, Function.iterate_succ_apply',
        one, equal, tracedRepresentative]
    have outer : tracedRepresentativeOuter s (s.nr 7) := by
      simpa only [tracedRepresentativeOuter, tracedRepresentative] using equal
    exact ⟨t, 10, le_rfl, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1,
      by simpa [outer] using effect.2.2.1, by simpa [outer] using effect.2.2.2.1, effect.2.2.2.2⟩
  · let t := (arithmeticStep appendTracedOuterRep)^[5] s
    have effect : t.pc = appendTracedOuterRep.length ∧ t.halted = false ∧
        t.nr 87 = s.nr 87 ∧ t.nm = s.nm ∧ t.rm = s.rm := by
      simp [t, appendTracedOuterRep, arithmeticStep, entry, running, Function.iterate_succ_apply',
        one, not_le.mpr above]
    have notOuter : ¬ tracedRepresentativeOuter s (s.nr 7) := by
      simpa [tracedRepresentativeOuter, tracedRepresentative] using above.ne'
    exact ⟨t, 5, by decide, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1,
      by simpa [notOuter] using effect.2.2.1, by simpa [notOuter] using effect.2.2.2.1, effect.2.2.2.2⟩





private theorem tracedOuterReps_succ (s : ArithmeticState) (i : ℕ) :
    tracedOuterReps s (i + 1) = tracedOuterReps s i ++
      (if tracedRepresentativeOuter s i then [tracedRepresentative s i] else []) := by
  by_cases outer : tracedRepresentativeOuter s i <;>
    simp [tracedOuterReps, List.range_succ, List.filter_append, outer]

private structure TraceOuterCollector (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 7 = i
  bases : ∀ r ∈ [9, 18, 19, 51, 86], s.nr r = initial.nr r
  count : s.nr 87 = initial.nr 87 + (tracedOuterReps initial i).length
  encoded : ∀ j < (tracedOuterReps initial i).length, s.nm (initial.nr 86 + initial.nr 87 + j) =
    (tracedOuterReps initial i)[j]?.getD 0
  earlier : ∀ a < initial.nr 86 + initial.nr 87, s.nm a = initial.nm a
  later : ∀ a, initial.nr 86 + initial.nr 87 + (tracedOuterReps initial i).length ≤ a → s.nm a = initial.nm a
  real : s.rm = initial.rm

/-- Pack the outer vertices of one trace prefix in their original order. Both the trace
and forest role entries stay readable below the destination range. -/
theorem collectTracedOuterReps_correct (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (valid : ∀ i < s.nr 19, tracedRepresentative s i < s.nr 55)
    (traceBefore : s.nr 18 + s.nr 19 ≤ s.nr 86)
    (roleBefore : s.nr 51 + s.nr 55 ≤ s.nr 86) :
    ∃ t steps, steps ≤ s.nr 19 * 13 + 2 ∧ BlockRuns collectTracedOuterReps steps s t ∧
      t.halted = false ∧ t.nr 87 = s.nr 87 + (tracedOuterReps s (s.nr 19)).length ∧
      (∀ j < (tracedOuterReps s (s.nr 19)).length, t.nm (s.nr 86 + s.nr 87 + j) =
        (tracedOuterReps s (s.nr 19))[j]?.getD 0) ∧
      (∀ a < s.nr 86 + s.nr 87, t.nm a = s.nm a) ∧
      (∀ a, s.nr 86 + t.nr 87 ≤ a → t.nm a = s.nm a) ∧ t.rm = s.rm := by
  have init : TraceOuterCollector s 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, by simp [tracedOuterReps], ?_, fun _ _ => rfl, fun _ _ => rfl, rfl⟩
    · intro r hr
      have different : r ≠ 7 := by simp at hr; omega
      exact Function.update_of_ne different _ _
    · simp [tracedOuterReps]
  have iterate (i : ℕ) (less : i < s.nr 19) (m : ArithmeticState) (before : TraceOuterCollector s i m) :
      ∃ t steps, steps ≤ 10 ∧ BlockRuns appendTracedOuterRep steps m t ∧ t.halted = false ∧
        TraceOuterCollector s (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    have mOne := (before.bases 9 (by decide)).trans one
    obtain ⟨t, ticks, short, out⟩ := appendTracedOuterRep_spec m before.entry before.running mOne
    have sameRep : tracedRepresentative m (m.nr 7) = tracedRepresentative s i := by
      rw [tracedRepresentative, before.bases 18 (by decide), before.index]
      exact before.earlier _ (by omega)
    have sameRole : tracedRepresentativeOuter m (m.nr 7) ↔ tracedRepresentativeOuter s i := by
      unfold tracedRepresentativeOuter
      have roleAddress : s.nr 51 + tracedRepresentative s i < s.nr 86 + s.nr 87 := by
        have v := valid i less
        omega
      rw [before.bases 51 (by decide), sameRep, before.earlier _ roleAddress]
    have reg (r : ℕ) (away : r ∉ [0, 6, 10, 11, 87]) : t.nr r = m.nr r := by
      rw [← out.run.run]
      apply arithmeticRun_keeps_register _ m ticks
      simp [appendTracedOuterRep, naturalDestination] at away ⊢ <;> omega
    let old := tracedOuterReps s i
    have listStep : tracedOuterReps s (i + 1) = old ++
        (if tracedRepresentativeOuter s i then [tracedRepresentative s i] else []) :=
      tracedOuterReps_succ s i
    have address : m.nr 86 + m.nr 87 = s.nr 86 + s.nr 87 + old.length := by
      simp only [before.bases 86 (by decide), before.count, old, Nat.add_assoc]
    refine ⟨t, ticks, short, out.run, out.running, rfl, out.running, ?_, ?_, ?_, ?_, ?_, ?_,
      out.realEffect.trans before.real⟩
    · simp [reg 7 (by decide), reg 9 (by decide), before.index, mOne]
    · intro r hr
      have diff : r ≠ 7 := by simp at hr; omega
      have away : r ∉ [0, 6, 10, 11, 87] := by simp at hr ⊢; omega
      exact (Function.update_of_ne diff _ _).trans ((reg r away).trans (before.bases r hr))
    · change t.nr 87 = s.nr 87 + (tracedOuterReps s (i + 1)).length
      rw [out.count, before.count, listStep]
      by_cases outer : tracedRepresentativeOuter s i <;> simp [sameRole, outer, old, Nat.add_assoc]
    · intro j limit
      change t.nm (s.nr 86 + s.nr 87 + j) = _
      rw [out.natEffect, address, sameRep, listStep]
      rw [listStep] at limit
      by_cases outer : tracedRepresentativeOuter s i
      · simp only [sameRole, outer, if_pos, List.length_append, List.length_cons, List.length_nil] at limit ⊢
        obtain previously | final := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ limit)
        · rw [Function.update_of_ne (show s.nr 86 + s.nr 87 + j ≠ s.nr 86 + s.nr 87 + old.length by omega),
            List.getElem?_append_left previously]
          exact before.encoded j previously
        · rw [final, Function.update_self, List.getElem?_append_right le_rfl, Nat.sub_self] <;> rfl
      · simpa [sameRole, outer] using before.encoded j (by simpa [outer] using limit)
    · intro a beforeScratch
      change t.nm a = _
      rw [out.natEffect, address]
      by_cases outer : tracedRepresentativeOuter s i
      · rw [if_pos (sameRole.mpr outer), Function.update_of_ne (by omega)]
        exact before.earlier a beforeScratch
      · rw [if_neg (fun marked => outer (sameRole.mp marked))]
        exact before.earlier a beforeScratch
    · intro a afterScratch
      change t.nm a = _
      rw [out.natEffect, address]
      rw [listStep] at afterScratch
      by_cases outer : tracedRepresentativeOuter s i
      · rw [if_pos (sameRole.mpr outer), Function.update_of_ne (by
          simp [outer] at afterScratch
          omega)]
        exact before.later a (by simp [outer, old] at afterScratch; omega)
      · rw [if_neg (fun marked => outer (sameRole.mp marked))]
        exact before.later a (by simpa [outer, old] using afterScratch)
  obtain ⟨last, ticks, done, short, run⟩ := countedLoopFromZero_bounded 9 7 19 (s.nr 19) 10
    appendTracedOuterRep (TraceOuterCollector s) entry running init
    (fun _ _ h => ⟨h.entry, h.running, h.index, h.bases 19 (by decide)⟩) iterate
  refine ⟨_, ticks, by omega, run, done.running, done.count, done.encoded, done.earlier, ?_, done.real⟩
  intro a high
  change s.nr 86 + last.nr 87 ≤ a at high
  exact done.later a (by rw [done.count] at high; omega)







theorem traceOuterRows_preserved {s m : ArithmeticState} {trace n : ℕ}
    (start : m.nr 18 = trace) (roles : m.nr 51 = s.nr 51)
    (traces : ∀ i < n, m.nm (trace + i) = s.nm (trace + i))
    (codes : ∀ i < n, m.nm (s.nr 51 + s.nm (trace + i)) = s.nm (s.nr 51 + s.nm (trace + i))) :
    tracedOuterReps m n = traceOuterRowsAt s trace n := by
  unfold tracedOuterReps traceOuterRowsAt
  have filters : ((List.range n).filter fun j => decide (tracedRepresentativeOuter m j)) =
      (List.range n).filter (fun j => decide (tracedRepresentativeOuter {s with nr := Function.update s.nr 18 trace} j)) := by
    apply List.filter_congr
    intro j inRange
    have inside := List.mem_range.mp inRange
    simp [tracedRepresentativeOuter, tracedRepresentative, start, roles, traces j inside, codes j inside]
  rw [filters]
  apply List.map_congr_left
  intro j enrolled
  have inside := List.mem_range.mp (List.mem_filter.mp enrolled).1
  simp [tracedRepresentative, start, traces j inside]

private theorem collectTracedOuterReps_keeps {s t : ArithmeticState} {ticks r : ℕ}
    (run : BlockRuns collectTracedOuterReps ticks s t) (safe : r ∉ [0, 6, 7, 10, 11, 87]) : t.nr r = s.nr r := by
  rw [← run.run]
  exact arithmeticRun_keeps_from_destination_list [0, 6, 7, 10, 11, 87] (by decide) safe s ticks

theorem collectAbsorbedOuterRows_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (leftBefore : s.nr 83 + s.nr 13 ≤ s.nr 86) (rightBefore : s.nr 84 + s.nr 14 ≤ s.nr 86)
    (roleBefore : s.nr 51 + s.nr 55 ≤ s.nr 86)
    (leftValid : ∀ j < s.nr 13, s.nm (s.nr 83 + j) < s.nr 55)
    (rightValid : ∀ j < s.nr 14, s.nm (s.nr 84 + j) < s.nr 55) :
    ∃ t ticks, ticks ≤ 13 * (s.nr 13 + s.nr 14) + 11 ∧ BlockRuns collectAbsorbedOuterRows ticks s t ∧
      t.halted = false ∧ t.nr 87 = (absorbedMatchingOuterRows s).length ∧
      (∀ j < (absorbedMatchingOuterRows s).length, t.nm (s.nr 86 + j) = (absorbedMatchingOuterRows s)[j]?.getD 0) ∧
      (∀ a, a < s.nr 86 ∨ s.nr 86 + t.nr 87 ≤ a → t.nm a = s.nm a) ∧ t.rm = s.rm ∧
      ∀ r, r ∉ [0, 6, 7, 10, 11, 18, 19, 23, 87] → t.nr r = s.nr r := by
  let firstCode : List ArithmeticInstruction :=
    [.natStore 86 12, .natConst 87 1, .natConst 23 0, .natAdd 18 83 23, .natAdd 19 13 23]
  let seeded := { s with
    pc := 5
    nm := Function.update s.nm (s.nr 86) (s.nr 12)
    nr := Function.update (Function.update (Function.update (Function.update s.nr 87 1) 23 0) 18 (s.nr 83)) 19 (s.nr 13) }
  have seed : BlockRuns firstCode 5 s seeded := by
    apply BlockRuns.of_running_exit
    · simp [firstCode, seeded, entry, running, arithmeticStep, Function.iterate_succ_apply']
    · exact running
    · rfl
  let a := {seeded with pc := 0}
  have a18 : a.nr 18 = s.nr 83 := by simp [a, seeded]
  have a19 : a.nr 19 = s.nr 13 := by simp [a, seeded]
  have aOne : a.nr 9 = 1 := by simpa [a, seeded] using one
  have aBefore (address : ℕ) (lower : address < s.nr 86) : a.nm address = s.nm address :=
    Function.update_of_ne (by omega) _ _
  have aTraces (j : ℕ) (before : j < s.nr 13) : a.nm (s.nr 83 + j) = s.nm (s.nr 83 + j) := aBefore _ (by omega)
  have aRoles (j : ℕ) (before : j < s.nr 13) : a.nm (s.nr 51 + s.nm (s.nr 83 + j)) = s.nm (s.nr 51 + s.nm (s.nr 83 + j)) :=
    aBefore _ (by have h := leftValid j before; omega)
  have aValid (j : ℕ) (before : j < a.nr 19) : tracedRepresentative a j < a.nr 55 := by
    rw [a19] at before
    have equal : a.nr 55 = s.nr 55 := by simp [a, seeded]
    rw [tracedRepresentative, a18, aTraces j before, equal]
    exact leftValid j before
  obtain ⟨left, leftTicks, leftBudget, leftRan, leftLive, leftCount, leftData, leftEarlier, leftLater, leftReal⟩ :=
    collectTracedOuterReps_correct a rfl running aOne aValid (by simpa [a18, a19, a, seeded] using leftBefore)
      (by simpa [a, seeded] using roleBefore)
  let b := {left with pc := 0}
  let switchCode : List ArithmeticInstruction := [.natAdd 18 84 23, .natAdd 19 14 23]
  let switched := {b with pc := 2, nr := Function.update (Function.update b.nr 18 (s.nr 84)) 19 (s.nr 14)}
  have rawKeeps (r : ℕ) (safe : r ∉ [0, 6, 7, 10, 11, 18, 19, 23, 87]) : b.nr r = s.nr r := by
    have pos := collectTracedOuterReps_keeps (r := r) leftRan (by simp at safe ⊢; omega)
    have aK : a.nr r = s.nr r := by
      have c18 : r ≠ 18 := by simp at safe; omega
      have c19 : r ≠ 19 := by simp at safe; omega
      have c23 : r ≠ 23 := by simp at safe; omega
      have c87 : r ≠ 87 := by simp at safe; omega
      simp [a, seeded, Function.update_of_ne c18, Function.update_of_ne c19, Function.update_of_ne c23,
        Function.update_of_ne c87]
    exact pos.trans aK
  have bZero : left.nr 23 = 0 := (collectTracedOuterReps_keeps leftRan (by decide)).trans (by simp [a, seeded])
  have switch : BlockRuns switchCode 2 b switched := by
    apply BlockRuns.of_running_exit
    · simp [switched, switchCode, b, leftLive, bZero, show left.nr 84 = s.nr 84 from rawKeeps 84 (by decide),
        show left.nr 14 = s.nr 14 from rawKeeps 14 (by decide), arithmeticStep, Function.iterate_succ_apply']
    · exact leftLive
    · rfl
  let c := {switched with pc := 0}
  have c18 : c.nr 18 = s.nr 84 := by simp [c, switched]
  have c19 : c.nr 19 = s.nr 14 := by simp [c, switched]
  have c55 : c.nr 55 = s.nr 55 := by simpa [c, switched] using rawKeeps 55 (by decide)
  have c51 : c.nr 51 = s.nr 51 := by simpa [c, switched] using rawKeeps 51 (by decide)
  have c86 : c.nr 86 = s.nr 86 := by simpa [c, switched] using rawKeeps 86 (by decide)
  have cOne : c.nr 9 = 1 := by simpa [c, switched] using (rawKeeps 9 (by decide)).trans one
  have aBase : a.nr 86 = s.nr 86 := by simp [a, seeded]
  have cBefore (address : ℕ) (lower : address < s.nr 86) : c.nm address = s.nm address := by
    have below : address < a.nr 86 + a.nr 87 := by rw [aBase]; omega
    exact (leftEarlier address below).trans (aBefore address lower)
  have cTraces (j : ℕ) (before : j < s.nr 14) : c.nm (s.nr 84 + j) = s.nm (s.nr 84 + j) := cBefore _ (by omega)
  have cRoles (j : ℕ) (before : j < s.nr 14) : c.nm (s.nr 51 + s.nm (s.nr 84 + j)) = s.nm (s.nr 51 + s.nm (s.nr 84 + j)) :=
    cBefore _ (by have h := rightValid j before; omega)
  have cValid (j : ℕ) (before : j < c.nr 19) : tracedRepresentative c j < c.nr 55 := by
    rw [c19] at before
    rw [tracedRepresentative, c18, cTraces j before, c55]
    exact rightValid j before
  obtain ⟨t, rightTicks, rightBudget, rightRan, rightLive, rightCount, rightData, rightEarlier, rightLater, rightReal⟩ :=
    collectTracedOuterReps_correct c rfl leftLive cOne cValid (by rwa [c18, c19, c86]) (by rwa [c51, c55, c86])
  have leftView : tracedOuterReps a (a.nr 19) = traceOuterRowsAt s (s.nr 83) (s.nr 13) := by
    rw [a19]
    exact traceOuterRows_preserved a18 (by simp [a, seeded]) aTraces aRoles
  have rightView : tracedOuterReps c (c.nr 19) = traceOuterRowsAt s (s.nr 84) (s.nr 14) := by
    rw [c19]
    exact traceOuterRows_preserved c18 c51 cTraces cRoles
  let earlier := [s.nr 12] ++ traceOuterRowsAt s (s.nr 83) (s.nr 13)
  have beforeCount : c.nr 87 = earlier.length := by
    have cLength : c.nr 87 = left.nr 87 := by simp [c, switched, b]
    rw [cLength, leftCount, leftView]
    change 1 + (traceOuterRowsAt s (s.nr 83) (s.nr 13)).length = earlier.length
    simp [earlier] <;> omega
  have count : t.nr 87 = (absorbedMatchingOuterRows s).length := by
    rw [rightCount, beforeCount, rightView]
    simp only [absorbedMatchingOuterRows, earlier, List.length_append, List.length_singleton] <;> omega
  have run : BlockRuns collectAbsorbedOuterRows (5 + (leftTicks + (2 + rightTicks))) s _ :=
    seed.append (leftRan.append (switch.append rightRan))
  refine ⟨_, _, ?_, run, rightLive, count, ?_, ?_, rightReal.trans leftReal, ?_⟩
  · rw [a19] at leftBudget
    rw [c19] at rightBudget
    omega
  · intro j within
    change t.nm _ = _
    change j < (earlier ++ traceOuterRowsAt s (s.nr 84) (s.nr 14)).length at within
    change t.nm _ = (earlier ++ traceOuterRowsAt s (s.nr 84) (s.nr 14))[j]?.getD 0
    by_cases inEarlier : j < earlier.length
    · rw [List.getElem?_append_left inEarlier]
      rw [rightEarlier _ (by rw [c86, beforeCount]; omega)]
      cases j with
      | zero =>
        have baseKept := leftEarlier (s.nr 86 + 0) (by simp [a, seeded])
        simpa [c, switched, b, earlier, a, seeded] using baseKept
      | succ j =>
        have jIn : j < (tracedOuterReps a (a.nr 19)).length := by
          rw [leftView]
          simp only [earlier, List.length_append, List.length_singleton] at inEarlier
          omega
        have slot := leftData j jIn
        rw [leftView] at slot
        have address : s.nr 86 + (j + 1) = s.nr 86 + 1 + j := by omega
        simpa [c, switched, b, earlier, a, seeded, address] using slot
    · have later : earlier.length ≤ j := Nat.le_of_not_gt inEarlier
      have jIn : j - earlier.length < (tracedOuterReps c (c.nr 19)).length := by
        rw [rightView]
        simp only [List.length_append] at within
        omega
      rw [List.getElem?_append_right later]
      have address : s.nr 86 + earlier.length + (j - earlier.length) = s.nr 86 + j := by omega
      simpa [c86, beforeCount, rightView, address] using rightData (j - earlier.length) jIn
  · intro address untouched
    change t.nm address = s.nm address
    rcases untouched with lower | greater
    · exact (rightEarlier address (by rw [c86]; omega)).trans (cBefore address lower)
    · change s.nr 86 + t.nr 87 ≤ address at greater
      have outer : c.nr 87 ≤ t.nr 87 := by omega
      have seededAddr : a.nr 86 = s.nr 86 := by simp [a, seeded]
      have leftPos : left.nr 87 ≤ t.nr 87 := outer
      have afterLeft : a.nr 86 + left.nr 87 ≤ address := by rw [seededAddr]; omega
      have no : address ≠ s.nr 86 := by
        have positive : 0 < t.nr 87 := by rw [count]; simp [absorbedMatchingOuterRows]
        omega
      have middle : c.nm address = a.nm address := leftLater address afterLeft
      have original : a.nm address = s.nm address := Function.update_of_ne no _ _
      exact (rightLater address (by rwa [c86])).trans (middle.trans original)
  · intro r safe
    rw [← run.run]
    exact arithmeticRun_keeps_from_destination_list [0, 6, 7, 10, 11, 18, 19, 23, 87]
      (by decide) safe s (5 + (leftTicks + (2 + rightTicks)))

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractRowsRAM

/-! matching/MatchingContractRepresentativesRAM.lean -/
section RppSource_MatchingContractRepresentativesRAM
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000











def matchingContractRepresentativeMemory (s : ArithmeticState) : ℕ → ℕ :=
  let i := s.nr 7
  let representative := originalTopRepresentative s i
  let remapped := if wasContractedRepresentative s representative then
    Function.update s.nm (s.nr 57 + i) (s.nr 12) else s.nm
  if newlyOuterOriginalInContraction s i then Function.update remapped (s.nr 88 + s.nr 99) i
    else remapped



theorem contractMatchingRepresentativeCell_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0)
    (roleBefore : s.nr 51 + s.nr 55 ≤ s.nr 57) (oldValid : originalTopRepresentative s (s.nr 7) < s.nr 55) :
    ∃ t steps, steps ≤ 13 ∧ BlockRuns contractMatchingRepresentativeCell steps s t ∧
      t.halted = false ∧ t.nm = matchingContractRepresentativeMemory s ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      t.nr 99 = s.nr 99 + (if newlyOuterOriginalInContraction s (s.nr 7) then 1 else 0) := by
  let origRep := s.nm (s.nr 57 + s.nr 7)
  by_cases absorbed : 0 < s.nm (s.nr 89 + origRep)
  · have mark : ¬ s.nm (s.nr 89 + origRep) ≤ 0 := Nat.not_le.mpr absorbed
    have different : s.nr 51 + origRep ≠ s.nr 57 + s.nr 7 := by
      have repValid : origRep < s.nr 55 := oldValid
      omega
    by_cases inner : 2 ≤ s.nm (s.nr 51 + origRep)
    · let t := (arithmeticStep contractMatchingRepresentativeCell)^[13] s
      have effect : t.pc = contractMatchingRepresentativeCell.length ∧ t.halted = false ∧
          t.nm = matchingContractRepresentativeMemory s ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
          t.nr 99 = s.nr 99 + (if newlyOuterOriginalInContraction s (s.nr 7) then 1 else 0) := by
        have flag : wasContractedRepresentative s (originalTopRepresentative s (s.nr 7)) := absorbed
        have new : newlyOuterOriginalInContraction s (s.nr 7) := ⟨flag, inner⟩
        have markAt : ¬s.nm (s.nr 89 + s.nm (s.nr 57 + s.nr 7)) ≤ 0 := mark
        have roleAt : 2 ≤ s.nm (s.nr 51 + s.nm (s.nr 57 + s.nr 7)) := inner
        have apart : s.nr 51 + s.nm (s.nr 57 + s.nr 7) ≠ s.nr 57 + s.nr 7 := different
        simp [t, contractMatchingRepresentativeCell, arithmeticStep, entry, running, one, zero, markAt, roleAt,
          Function.iterate_succ_apply', matchingContractRepresentativeMemory, flag, new, Function.update_of_ne apart]
      exact ⟨t, 13, le_rfl, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2⟩
    · let t := (arithmeticStep contractMatchingRepresentativeCell)^[10] s
      have effect : t.pc = contractMatchingRepresentativeCell.length ∧ t.halted = false ∧
          t.nm = matchingContractRepresentativeMemory s ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
          t.nr 99 = s.nr 99 + (if newlyOuterOriginalInContraction s (s.nr 7) then 1 else 0) := by
        have flag : wasContractedRepresentative s (originalTopRepresentative s (s.nr 7)) := absorbed
        have new : ¬newlyOuterOriginalInContraction s (s.nr 7) := fun h => inner h.2
        have markAt : ¬s.nm (s.nr 89 + s.nm (s.nr 57 + s.nr 7)) ≤ 0 := mark
        have roleAt : ¬2 ≤ s.nm (s.nr 51 + s.nm (s.nr 57 + s.nr 7)) := inner
        have apart : s.nr 51 + s.nm (s.nr 57 + s.nr 7) ≠ s.nr 57 + s.nr 7 := different
        simp [t, contractMatchingRepresentativeCell, arithmeticStep, entry, running, zero, markAt, roleAt,
          Function.iterate_succ_apply', matchingContractRepresentativeMemory, flag, new, Function.update_of_ne apart]
      exact ⟨t, 10, by decide, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2⟩
  · let t := (arithmeticStep contractMatchingRepresentativeCell)^[5] s
    have effect : t.pc = contractMatchingRepresentativeCell.length ∧ t.halted = false ∧
        t.nm = matchingContractRepresentativeMemory s ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
        t.nr 99 = s.nr 99 + (if newlyOuterOriginalInContraction s (s.nr 7) then 1 else 0) := by
      have flag : ¬wasContractedRepresentative s (originalTopRepresentative s (s.nr 7)) := absorbed
      have new : ¬newlyOuterOriginalInContraction s (s.nr 7) := fun h => flag h.1
      have mark : s.nm (s.nr 89 + s.nm (s.nr 57 + s.nr 7)) ≤ 0 := Nat.le_of_not_gt absorbed
      simp [t, contractMatchingRepresentativeCell, arithmeticStep, entry, running, zero, mark,
        Function.iterate_succ_apply', matchingContractRepresentativeMemory, flag, new]
    exact ⟨t, 5, by decide, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2⟩



def contractedOriginalsNewlyOuter (s : ArithmeticState) (count : ℕ) : List ℕ :=
  (List.range count).filter fun i => decide (newlyOuterOriginalInContraction s i)

private theorem contractedOriginalsNewlyOuter_succ (s : ArithmeticState) (i : ℕ) :
    contractedOriginalsNewlyOuter s (i + 1) = contractedOriginalsNewlyOuter s i ++
      (if newlyOuterOriginalInContraction s i then [i] else []) := by
  by_cases accepted : newlyOuterOriginalInContraction s i <;>
    simp [contractedOriginalsNewlyOuter, List.range_succ, List.filter_append, accepted]

private theorem contractedOriginalsNewlyOuter_length (s : ArithmeticState) (i : ℕ) :
    (contractedOriginalsNewlyOuter s i).length ≤ i := by
  unfold contractedOriginalsNewlyOuter
  simpa using List.length_filter_le (fun j => decide (newlyOuterOriginalInContraction s j)) (List.range i)

private structure ContractedRepresentativeScan (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  live : s.halted = false
  index : s.nr 7 = i
  registers : ∀ r, r ∉ [0, 6, 7, 10, 11, 23, 99] → s.nr r = initial.nr r
  zero : s.nr 23 = 0
  freshCount : s.nr 99 = (contractedOriginalsNewlyOuter initial i).length
  map : ∀ j < initial.nr 55, s.nm (initial.nr 57 + j) =
    if j < i ∧ wasContractedRepresentative initial (originalTopRepresentative initial j) then initial.nr 12
    else originalTopRepresentative initial j
  fresh : ∀ j < (contractedOriginalsNewlyOuter initial i).length,
    s.nm (initial.nr 88 + j) = (contractedOriginalsNewlyOuter initial i)[j]?.getD 0
  other : ∀ addr,
    (addr < initial.nr 57 ∨ initial.nr 57 + i ≤ addr) →
    (addr < initial.nr 88 ∨ initial.nr 88 + (contractedOriginalsNewlyOuter initial i).length ≤ addr) →
    s.nm addr = initial.nm addr
  real : s.rm = initial.rm
  realRegisters : s.rr = initial.rr

/-- The contraction remap consumes the original membership table once and packs the
vertices promoted from an inner child. The stage can charge neighbor scans to that list. -/
theorem contractMatchingRepresentativeBlock_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (roleBefore : s.nr 51 + s.nr 55 ≤ s.nr 57) (freshAfter : s.nr 57 + s.nr 55 ≤ s.nr 88)
    (markAfter : s.nr 88 + s.nr 55 ≤ s.nr 89)
    (oldValid : ∀ j < s.nr 55, originalTopRepresentative s j < s.nr 55) :
    ∃ t steps, steps ≤ 16 * s.nr 55 + 4 ∧ BlockRuns contractMatchingRepresentativeBlock steps s t ∧ t.halted = false ∧
      t.nr 99 = (contractedOriginalsNewlyOuter s (s.nr 55)).length ∧
      (∀ j < s.nr 55, t.nm (s.nr 57 + j) =
        if wasContractedRepresentative s (originalTopRepresentative s j) then s.nr 12
        else originalTopRepresentative s j) ∧
      (∀ j < (contractedOriginalsNewlyOuter s (s.nr 55)).length,
        t.nm (s.nr 88 + j) = (contractedOriginalsNewlyOuter s (s.nr 55))[j]?.getD 0) ∧
      (∀ addr, (addr < s.nr 57 ∨ s.nr 57 + s.nr 55 ≤ addr) →
        (addr < s.nr 88 ∨ s.nr 88 + t.nr 99 ≤ addr) → t.nm addr = s.nm addr) ∧
      t.rm = s.rm ∧ t.rr = s.rr := by
  let seeded := {s with pc := 2, nr := Function.update (Function.update s.nr 23 0) 99 0}
  have seed : BlockRuns [.natConst 23 0, .natConst 99 0] 2 s seeded := by
    apply BlockRuns.of_running_exit
    · simp [seeded, arithmeticStep, entry, running, Function.iterate_succ_apply']
    · exact running
    · rfl
  let start := {seeded with pc := 0}
  have init : ContractedRepresentativeScan s 0 {start with pc := 0, nr := Function.update start.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, by simp [start, seeded], by simp [start, seeded, contractedOriginalsNewlyOuter],
      ?_, ?_, fun _ _ _ => rfl, rfl, rfl⟩
    · intro r away
      have r7 : r ≠ 7 := by simp at away; omega
      have r23 : r ≠ 23 := by simp at away; omega
      have r99 : r ≠ 99 := by simp at away; omega
      simp [start, seeded, Function.update_of_ne r7, Function.update_of_ne r23, Function.update_of_ne r99]
    · intro j _
      simp [originalTopRepresentative, start, seeded]
    · simp [contractedOriginalsNewlyOuter]
  have iteration (i : ℕ) (h : i < s.nr 55) (m : ArithmeticState) (before : ContractedRepresentativeScan s i m) :
      ∃ t ticks, ticks ≤ 13 ∧ BlockRuns contractMatchingRepresentativeCell ticks m t ∧ t.halted = false ∧
        ContractedRepresentativeScan s (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    have table := before.registers 57 (by decide)
    have role := before.registers 51 (by decide)
    have size := before.registers 55 (by decide)
    have layout := before.registers 88 (by decide)
    have marks := before.registers 89 (by decide)
    have base := before.registers 12 (by decide)
    have addressRep : originalTopRepresentative m (m.nr 7) = originalTopRepresentative s i := by
      rw [originalTopRepresentative, table, before.index, before.map i h, if_neg (fun accepted => Nat.lt_irrefl i accepted.1)]
    have repWithin : originalTopRepresentative s i < s.nr 55 := oldValid i h
    have freshBound := contractedOriginalsNewlyOuter_length s i
    have markAt (r : ℕ) : m.nm (s.nr 89 + r) = s.nm (s.nr 89 + r) :=
      before.other _ (.inr (by omega)) (.inr (by omega))
    have roleAt : m.nm (s.nr 51 + originalTopRepresentative s i) = s.nm (s.nr 51 + originalTopRepresentative s i) :=
      before.other _ (.inl (by omega)) (.inl (by omega))
    have sameMark : wasContractedRepresentative m (originalTopRepresentative m (m.nr 7)) ↔
        wasContractedRepresentative s (originalTopRepresentative s i) := by
      simp [wasContractedRepresentative, marks, addressRep, markAt]
    have sameFresh : newlyOuterOriginalInContraction m (m.nr 7) ↔ newlyOuterOriginalInContraction s i := by
      simp [newlyOuterOriginalInContraction, sameMark, addressRep, role, roleAt, wasContractedRepresentative, marks, markAt]
    have sameMarkAt : wasContractedRepresentative m (originalTopRepresentative m i) ↔
        wasContractedRepresentative s (originalTopRepresentative s i) := by
      simpa only [before.index] using sameMark
    have sameFreshAt : newlyOuterOriginalInContraction m i ↔ newlyOuterOriginalInContraction s i := by
      simpa only [before.index] using sameFresh
    have mOne : m.nr 9 = 1 := (before.registers 9 (by decide)).trans one
    obtain ⟨t, ticks, cost, run, live, natural, real, realRegs, count⟩ := contractMatchingRepresentativeCell_spec m
      before.entry before.live mOne before.zero (by simpa [role, table, size] using roleBefore)
      (by rw [addressRep, size]; exact repWithin)
    have keeps (r : ℕ) (away : r ∉ [0, 6, 10, 11, 99]) : t.nr r = m.nr r := by
      rw [← run.run]
      exact arithmeticRun_keeps_from_destination_list [0, 6, 10, 11, 99] (by decide) away m ticks
    let old := contractedOriginalsNewlyOuter s i
    have newList : contractedOriginalsNewlyOuter s (i+1) = old ++
        (if newlyOuterOriginalInContraction s i then [i] else []) := contractedOriginalsNewlyOuter_succ s i
    have effect : t.nm =
        let remapped := if wasContractedRepresentative s (originalTopRepresentative s i) then
          Function.update m.nm (s.nr 57 + i) (s.nr 12) else m.nm
        if newlyOuterOriginalInContraction s i then Function.update remapped (s.nr 88 + old.length) i else remapped := by
      by_cases promoted : newlyOuterOriginalInContraction s i <;>
        by_cases marked : wasContractedRepresentative s (originalTopRepresentative s i) <;>
        simp [natural, matchingContractRepresentativeMemory, sameMarkAt, sameFreshAt, promoted, marked, table, base,
          before.index, layout, before.freshCount, old]
    have newCount : t.nr 99 = (contractedOriginalsNewlyOuter s (i + 1)).length := by
      rw [count, before.freshCount, newList]
      by_cases promoted : newlyOuterOriginalInContraction s i <;> simp [sameFresh, promoted, old]
    refine ⟨t, ticks, cost, run, live, rfl, live, ?_, ?_, ?_, newCount, ?_, ?_, ?_,
      real.trans before.real, realRegs.trans before.realRegisters⟩
    · simp [keeps 7 (by decide), keeps 9 (by decide), before.index, mOne]
    · intro r away
      have other : r ≠ 7 := by simp at away; omega
      have safe : r ∉ [0, 6, 10, 11, 99] := by simp at away ⊢; omega
      exact (Function.update_of_ne other _ _).trans ((keeps r safe).trans (before.registers r away))
    · exact (keeps 23 (by decide)).trans before.zero
    · intro j hj
      change t.nm (s.nr 57 + j) = _
      have far : s.nr 57 + j ≠ s.nr 88 + old.length := by omega
      by_cases markI : wasContractedRepresentative s (originalTopRepresentative s i)
      · by_cases same : j = i
        · subst j
          by_cases promoted : newlyOuterOriginalInContraction s i <;>
            simp [effect, markI, promoted, Function.update_of_ne far, Nat.lt_succ_self]
        · have earlier : j < i + 1 ↔ j < i := by omega
          have different : s.nr 57 + j ≠ s.nr 57 + i := by omega
          by_cases promoted : newlyOuterOriginalInContraction s i <;>
            simp [effect, markI, earlier, promoted, before.map j hj, Function.update_of_ne far, Function.update_of_ne different]
      · have never : ¬newlyOuterOriginalInContraction s i := fun marked => markI marked.1
        by_cases same : j = i
        · subst j
          simp [effect, never, markI, before.map i h]
        · have earlier : j < i + 1 ↔ j < i := by omega
          simp [effect, markI, never, earlier, before.map j hj]
    · intro j hj
      change t.nm (s.nr 88 + j) = _
      have far : s.nr 88 + j ≠ s.nr 57 + i := by omega
      rw [newList] at hj ⊢
      by_cases promoted : newlyOuterOriginalInContraction s i
      · simp only [if_pos promoted, List.length_append, List.length_cons, List.length_nil] at hj ⊢
        obtain earlier | same := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)
        · rw [List.getElem?_append_left earlier]
          have oldCell : s.nr 88 + j ≠ s.nr 88 + old.length := by omega
          simp [effect, promoted, promoted.1, Function.update_of_ne far, Function.update_of_ne oldCell,
            before.fresh j earlier, old]
        · rw [same, List.getElem?_append_right le_rfl, Nat.sub_self]
          simp [effect, promoted]
      · have earlier : j < old.length := by simpa [promoted] using hj
        by_cases marked : wasContractedRepresentative s (originalTopRepresentative s i) <;>
          simp [effect, promoted, marked, Function.update_of_ne far, before.fresh j earlier, old]
    · intro addr outsideMap outsideFresh
      change t.nm addr = s.nm addr
      have outsideOldMap : addr < s.nr 57 ∨ s.nr 57 + i ≤ addr := by omega
      have notRep : addr ≠ s.nr 57 + i := by omega
      rw [newList] at outsideFresh
      by_cases promoted : newlyOuterOriginalInContraction s i
      · simp [promoted] at outsideFresh
        have outsideOldFresh : addr < s.nr 88 ∨ s.nr 88 + old.length ≤ addr := by omega
        have notFresh : addr ≠ s.nr 88 + old.length := by omega
        simp [effect, promoted, promoted.1, before.other addr outsideOldMap outsideOldFresh,
          Function.update_of_ne notFresh, Function.update_of_ne notRep]
      · have outsideOldFresh : addr < s.nr 88 ∨ s.nr 88 + old.length ≤ addr := by simpa [promoted] using outsideFresh
        by_cases marked : wasContractedRepresentative s (originalTopRepresentative s i) <;>
          simp [effect, promoted, marked, before.other addr outsideOldMap outsideOldFresh, Function.update_of_ne notRep]
  obtain ⟨last, ticks, done, cost, completed⟩ := countedLoopFromZero_bounded 9 7 55 (s.nr 55) 13
    contractMatchingRepresentativeCell (ContractedRepresentativeScan s) (s := start) rfl running init
    (fun _ _ h => ⟨h.entry, h.live, h.index, h.registers 55 (by decide)⟩) iteration
  refine ⟨_, 2 + ticks, by omega, seed.append completed, done.live, done.freshCount, ?_, done.fresh, ?_, done.real, done.realRegisters⟩
  · intro j hj
    change last.nm (s.nr 57 + j) = _
    simpa only [hj, true_and] using done.map j hj
  · intro addr mapSpace freshSpace
    change addr < s.nr 88 ∨ s.nr 88 + last.nr 99 ≤ addr at freshSpace
    rw [done.freshCount] at freshSpace
    exact done.other addr mapSpace freshSpace

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractRepresentativesRAM

/-! matching/MatchingContractForestRAM.lean -/
section RppSource_MatchingContractForestRAM
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def hiddenContractionForestMemory (s : ArithmeticState) : ℕ → ℕ :=
  Function.update (Function.update (Function.update s.nm (s.nr 51 + s.nr 7) 0)
    (s.nr 52 + s.nr 7) (s.nr 55)) (s.nr 74 + s.nr 7) 0

theorem hideContractedForestRepresentative_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 23 = 0) :
    ∃ t, BlockRuns hideContractedForestRepresentative 6 s t ∧ t.halted = false ∧
      t.nm = hiddenContractionForestMemory s ∧ t.rm = s.rm ∧ t.rr = s.rr := by
  let t := (arithmeticStep hideContractedForestRepresentative)^[6] s
  have computed : t.pc = hideContractedForestRepresentative.length ∧ t.halted = false ∧
      t.nm = hiddenContractionForestMemory s ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, hideContractedForestRepresentative, hiddenContractionForestMemory, arithmeticStep,
      entry, running, zero, Function.iterate_succ_apply']
  exact ⟨t, BlockRuns.of_running_exit rfl computed.2.1 computed.1, computed.2⟩





theorem redirectContractedForestParent_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 23 = 0) :
    ∃ t steps, steps ≤ 10 ∧ BlockRuns redirectContractedForestParent steps s t ∧ t.halted = false ∧
      t.nm = (if survivingInnerParentEntersCycle s then Function.update s.nm (s.nr 52 + s.nr 7) (s.nr 12) else s.nm) ∧
      t.rm = s.rm ∧ t.rr = s.rr := by
  by_cases inner : 2 ≤ s.nm (s.nr 51 + s.nr 7)
  · by_cases marked : wasContractedRepresentative s (s.nm (s.nr 52 + s.nr 7))
    · have role : survivingInnerParentEntersCycle s := ⟨inner, marked⟩
      have visit : ¬s.nm (s.nr 89 + s.nm (s.nr 52 + s.nr 7)) ≤ 0 := Nat.not_le.mpr marked
      let t := (arithmeticStep redirectContractedForestParent)^[10] s
      have effect : t.pc = redirectContractedForestParent.length ∧ t.halted = false ∧
          t.nm = (if survivingInnerParentEntersCycle s then Function.update s.nm (s.nr 52 + s.nr 7) (s.nr 12) else s.nm) ∧
          t.rm = s.rm ∧ t.rr = s.rr := by
        simp [t, redirectContractedForestParent, arithmeticStep, entry, running, zero,
          Function.iterate_succ_apply', inner, visit, role]
      exact ⟨t, 10, le_rfl, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2⟩
    · have role : ¬survivingInnerParentEntersCycle s := fun h => marked h.2
      have skip : s.nm (s.nr 89 + s.nm (s.nr 52 + s.nr 7)) ≤ 0 := Nat.le_of_not_gt marked
      let t := (arithmeticStep redirectContractedForestParent)^[9] s
      have effect : t.pc = redirectContractedForestParent.length ∧ t.halted = false ∧
          t.nm = (if survivingInnerParentEntersCycle s then Function.update s.nm (s.nr 52 + s.nr 7) (s.nr 12) else s.nm) ∧
          t.rm = s.rm ∧ t.rr = s.rr := by
        simp [t, redirectContractedForestParent, arithmeticStep, entry, running, zero,
          Function.iterate_succ_apply', inner, skip, role]
      exact ⟨t, 9, by decide, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2⟩
  · have role : ¬survivingInnerParentEntersCycle s := fun h => inner h.1
    let t := (arithmeticStep redirectContractedForestParent)^[4] s
    have effect : t.pc = redirectContractedForestParent.length ∧ t.halted = false ∧
        t.nm = (if survivingInnerParentEntersCycle s then Function.update s.nm (s.nr 52 + s.nr 7) (s.nr 12) else s.nm) ∧
        t.rm = s.rm ∧ t.rr = s.rr := by
      simp [t, redirectContractedForestParent, arithmeticStep, entry, running,
        Function.iterate_succ_apply', inner, role]
    exact ⟨t, 4, by decide, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2⟩

def contractedMatchingForestCellMemory (s : ArithmeticState) : ℕ → ℕ :=
  if wasContractedRepresentative s (s.nr 7) ∧ s.nr 7 ≠ s.nr 12 then hiddenContractionForestMemory s
  else if survivingInnerParentEntersCycle s then Function.update s.nm (s.nr 52 + s.nr 7) (s.nr 12)
  else s.nm

theorem contractMatchingForestCell_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 23 = 0) :
    ∃ t steps, steps ≤ 17 ∧ BlockRuns contractMatchingForestCell steps s t ∧ t.halted = false ∧
      t.nm = contractedMatchingForestCellMemory s ∧ t.rm = s.rm ∧ t.rr = s.rr := by
  let fetched := { s with
    pc := 2
    nr := Function.update (Function.update s.nr 6 (s.nr 89 + s.nr 7)) 10 (s.nm (s.nr 89 + s.nr 7)) }
  have read : BlockRuns readContractionMask 2 s fetched := by
    apply BlockRuns.of_running_exit
    · simp [fetched, readContractionMask, arithmeticStep, entry, running, Function.iterate_succ_apply']
    · exact running
    · rfl
  let a := {fetched with pc := 0}
  have aZero : a.nr 23 = 0 := by simp [a, fetched, zero]
  have flag : a.nr 10 = s.nm (s.nr 89 + s.nr 7) := by simp [a, fetched]
  have index : a.nr 7 = s.nr 7 := by simp [a, fetched]
  have root : a.nr 12 = s.nr 12 := by simp [a, fetched]
  let keep := redirectContractedForestParent
  let hide := hideContractedForestRepresentative
  let compareBack := branchOnAtMost 12 7 keep hide
  let compareFront := branchOnAtMost 7 12 compareBack hide
  obtain ⟨retained, ticks, cost, retain, retainedLive, retainedNat, retainedReal, retainedRR⟩ :=
    redirectContractedForestParent_spec a rfl running aZero
  have safeRetain (notHidden : ¬(wasContractedRepresentative s (s.nr 7) ∧ s.nr 7 ≠ s.nr 12)) :
      retained.nm = contractedMatchingForestCellMemory s := by
    rw [contractedMatchingForestCellMemory, if_neg notHidden, retainedNat] <;> rfl
  obtain ⟨removed, remove, removedLive, removedNat, removedReal, removedRR⟩ :=
    hideContractedForestRepresentative_spec a rfl running aZero
  have safeRemove (hidden : wasContractedRepresentative s (s.nr 7) ∧ s.nr 7 ≠ s.nr 12) :
      removed.nm = contractedMatchingForestCellMemory s := by
    simpa [contractedMatchingForestCellMemory, a, fetched, hidden, hiddenContractionForestMemory] using removedNat
  by_cases marked : wasContractedRepresentative s (s.nr 7)
  · have hasMark : a.nr 23 < a.nr 10 := by rw [aZero, flag]; exact marked
    rcases lt_trichotomy (s.nr 7) (s.nr 12) with before | same | after
    · have back := branchOnAtMost_right 12 7 keep hide (s := a) rfl running
        (by simpa only [root, index] using before) remove removedLive
      have front := branchOnAtMost_left 7 12 compareBack hide (s := a) rfl running
        (by simpa only [root, index] using before.le) back removedLive
      have routed := branchOnAtMost_right 10 23 keep compareFront (s := a) rfl running hasMark front removedLive
      exact ⟨_, 2 + (1 + (1 + (1 + 6) + 1)), by decide, read.append routed,
        removedLive, safeRemove ⟨marked, before.ne⟩, removedReal, removedRR⟩
    · have back := branchOnAtMost_left 12 7 keep hide (s := a) rfl running
        (by simp [root, index, same]) retain retainedLive
      have front := branchOnAtMost_left 7 12 compareBack hide (s := a) rfl running
        (by simp [root, index, same]) back retainedLive
      have routed := branchOnAtMost_right 10 23 keep compareFront (s := a) rfl running hasMark front retainedLive
      exact ⟨_, 2 + (1 + (1 + (1 + ticks + 1) + 1)), by omega, read.append routed,
        retainedLive, safeRetain (fun h => h.2 same), retainedReal, retainedRR⟩
    · have front := branchOnAtMost_right 7 12 compareBack hide (s := a) rfl running
        (by simpa only [root, index] using after) remove removedLive
      have routed := branchOnAtMost_right 10 23 keep compareFront (s := a) rfl running hasMark front removedLive
      exact ⟨_, 2 + (1 + (1 + 6)), by decide, read.append routed,
        removedLive, safeRemove ⟨marked, after.ne'⟩, removedReal, removedRR⟩
  · have missing : a.nr 10 ≤ a.nr 23 := by rw [aZero, flag]; exact Nat.le_of_not_gt marked
    have routed := branchOnAtMost_left 10 23 keep compareFront (s := a) rfl running missing retain retainedLive
    exact ⟨_, 2 + (1 + ticks + 1), by omega, read.append routed,
      retainedLive, safeRetain (fun h => marked h.1), retainedReal, retainedRR⟩

def contractedMatchingForestMemory (s : ArithmeticState) : ℕ → (ℕ → ℕ)
  | 0 => s.nm
  | i + 1 => contractedMatchingForestCellMemory
      {s with nr := Function.update s.nr 7 i, nm := contractedMatchingForestMemory s i}

theorem contractedMatchingForestMemory_unchanged (s : ArithmeticState) (n address : ℕ)
    (role : address < s.nr 51 ∨ s.nr 51 + n ≤ address)
    (parent : address < s.nr 52 ∨ s.nr 52 + n ≤ address)
    (node : address < s.nr 74 ∨ s.nr 74 + n ≤ address) :
    contractedMatchingForestMemory s n address = s.nm address := by
  induction n with
  | zero => rfl
  | succ i ih =>
    have before := ih (by omega) (by omega) (by omega)
    have noRole : address ≠ s.nr 51 + i := by omega
    have noParent : address ≠ s.nr 52 + i := by omega
    have noNode : address ≠ s.nr 74 + i := by omega
    rw [contractedMatchingForestMemory, contractedMatchingForestCellMemory]
    split
    · simpa [hiddenContractionForestMemory, Function.update_of_ne noRole, Function.update_of_ne noParent,
        Function.update_of_ne noNode] using before
    · split
      · simpa [Function.update_of_ne noParent] using before
      · exact before

private structure ContractedForestScan (initial : ArithmeticState) (index : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  indexAt : s.nr 7 = index
  registers : ∀ r, r ∉ [0, 6, 7, 10, 11] → s.nr r = initial.nr r
  natural : s.nm = contractedMatchingForestMemory initial index
  real : s.rm = initial.rm
  realRegisters : s.rr = initial.rr

/-- Scan the compact forest once, hiding absorbed nodes and redirecting surviving parents. -/
theorem contractMatchingForestBlock_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0) :
    ∃ t steps, steps ≤ 20 * s.nr 55 + 2 ∧ BlockRuns contractMatchingForestBlock steps s t ∧
      t.halted = false ∧ t.nm = contractedMatchingForestMemory s (s.nr 55) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 7, 10, 11] → t.nr r = s.nr r := by
  have start : ContractedForestScan s 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, rfl, rfl, rfl⟩
    intro r away
    exact Function.update_of_ne (by simp at away; omega) 0 s.nr
  have iterate (i : ℕ) (_ : i < s.nr 55) (m : ArithmeticState) (h : ContractedForestScan s i m) :
      ∃ t steps, steps ≤ 17 ∧ BlockRuns contractMatchingForestCell steps m t ∧ t.halted = false ∧
        ContractedForestScan s (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    have mZero : m.nr 23 = 0 := (h.registers 23 (by decide)).trans zero
    have mOne : m.nr 9 = 1 := (h.registers 9 (by decide)).trans one
    obtain ⟨t, ticks, budget, run, live, natural, real, regs⟩ := contractMatchingForestCell_spec m h.entry h.running mZero
    have kept (r : ℕ) (away : r ∉ [0, 6, 10, 11]) : t.nr r = m.nr r := by
      rw [← run.run]
      exact arithmeticRun_keeps_from_destination_list [0, 6, 10, 11] (by decide) away m ticks
    refine ⟨t, ticks, budget, run, live, rfl, live, ?_, ?_, ?_, real.trans h.real, regs.trans h.realRegisters⟩
    · simp [kept 7 (by decide), kept 9 (by decide), h.indexAt, mOne]
    · intro r away
      have other : r ≠ 7 := by simp at away; omega
      have untouched : r ∉ [0, 6, 10, 11] := by simp at away ⊢; omega
      exact (Function.update_of_ne other _ _).trans ((kept r untouched).trans (h.registers r away))
    · change t.nm = contractedMatchingForestMemory s (i + 1)
      rw [natural, contractedMatchingForestMemory]
      have role := h.registers 51 (by decide)
      have parent := h.registers 52 (by decide)
      have size := h.registers 55 (by decide)
      have base := h.registers 12 (by decide)
      have registry := h.registers 74 (by decide)
      have mark := h.registers 89 (by decide)
      simp [contractedMatchingForestCellMemory, hiddenContractionForestMemory, survivingInnerParentEntersCycle,
        wasContractedRepresentative, role, parent, size, base, registry, mark, h.indexAt, h.natural] <;>
        split <;> simp_all
  obtain ⟨last, steps, done, cost, complete⟩ := countedLoopFromZero_bounded 9 7 55 (s.nr 55) 17
    contractMatchingForestCell (ContractedForestScan s) entry running start
    (fun _ _ h => ⟨h.entry, h.running, h.indexAt, h.registers 55 (by decide)⟩) iterate
  exact ⟨_, steps, by omega, complete, done.running, done.natural, done.real, done.realRegisters, done.registers⟩

theorem installNewTopMatchingBlossom_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns installNewTopMatchingBlossom 3 s t ∧ t.halted = false ∧
      t.nm = Function.update s.nm (s.nr 74 + s.nr 12) (s.nr 76) ∧ t.nr 76 = s.nr 76 + 1 ∧
      t.rm = s.rm := by
  let t := (arithmeticStep installNewTopMatchingBlossom)^[3] s
  have computed : t.pc = installNewTopMatchingBlossom.length ∧ t.halted = false ∧
      t.nm = Function.update s.nm (s.nr 74 + s.nr 12) (s.nr 76) ∧ t.nr 76 = s.nr 76 + 1 ∧ t.rm = s.rm := by
    simp [t, installNewTopMatchingBlossom, arithmeticStep, entry, running, one, Function.iterate_succ_apply']
  exact ⟨t, BlockRuns.of_running_exit rfl computed.2.1 computed.1, computed.2⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractForestRAM

/-! matching/MatchingContractMaskRAM.lean -/
section RppSource_MatchingContractMaskRAM
namespace VehicleRoutingSurvey.Routing

private def cycleMaskPassCell (mark : Bool) : List ArithmeticInstruction :=
  if mark then markCycleTraceRepresentative else clearCycleMark

private def cycleMaskLimit (mark : Bool) : ℕ := if mark then 19 else 55

def cycleMaskAddress (mark : Bool) (s : ArithmeticState) (i : ℕ) : ℕ :=
  s.nr 89 + (if mark then s.nm (s.nr 18 + i) else i)

def cycleMaskScanAddresses (mark : Bool) (s : ArithmeticState) (count : ℕ) : List ℕ :=
  (List.range count).map (cycleMaskAddress mark s)

private theorem cycleMaskPassCell_spec (mark : Bool) (s : ArithmeticState)
    (entry : s.pc = 0) (running : s.halted = false) (zero : s.nr 23 = 0) (one : s.nr 9 = 1) :
    ∃ t steps, steps ≤ 4 ∧ BlockRuns (cycleMaskPassCell mark) steps s t ∧ t.halted = false ∧
      t.nm = Function.update s.nm (cycleMaskAddress mark s (s.nr 7)) (if mark then 1 else 0) ∧ t.rm = s.rm ∧
      t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 10] → t.nr r = s.nr r := by
  have effects {t : ArithmeticState} {steps : ℕ} (run : BlockRuns (cycleMaskPassCell mark) steps s t)
      (r : ℕ) (safe : r ∉ [0, 6, 10]) : t.nr r = s.nr r := by
    rw [← run.run]
    have destinations : (cycleMaskPassCell mark).all (fun ins => decide (naturalDestination ins ∈ [0, 6, 10])) = true := by
      cases mark <;> decide
    exact arithmeticRun_keeps_from_destination_list _ destinations safe s steps
  cases mark
  · let t := {s with
      pc := 2
      nr := Function.update s.nr 6 (cycleMaskAddress false s (s.nr 7))
      nm := Function.update s.nm (cycleMaskAddress false s (s.nr 7)) 0 }
    have run : BlockRuns (cycleMaskPassCell false) 2 s t := by
      apply BlockRuns.of_running_exit
      · simp [t, cycleMaskPassCell, clearCycleMark, cycleMaskAddress, arithmeticStep, entry, running, zero,
          Function.iterate_succ_apply']
      · exact running
      · rfl
    exact ⟨t, 2, by decide, run, running, rfl, rfl, rfl, effects run⟩
  · let r := s.nm (s.nr 18 + s.nr 7)
    let t := {s with
      pc := 4
      nr := Function.update (Function.update s.nr 10 r) 6 (cycleMaskAddress true s (s.nr 7))
      nm := Function.update s.nm (cycleMaskAddress true s (s.nr 7)) 1 }
    have run : BlockRuns (cycleMaskPassCell true) 4 s t := by
      apply BlockRuns.of_running_exit
      · simp [t, r, cycleMaskPassCell, markCycleTraceRepresentative, cycleMaskAddress, arithmeticStep, entry, running, one,
          Function.iterate_succ_apply', Function.update_idem, Function.update_comm]
      · exact running
      · rfl
    exact ⟨t, 4, le_rfl, run, running, rfl, rfl, rfl, effects run⟩

private structure CycleMaskPass (s : ArithmeticState) (mark : Bool) (i : ℕ) (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  live : m.halted = false
  index : m.nr 7 = i
  registers : ∀ r, r ∉ [0, 6, 7, 10] → m.nr r = s.nr r
  natural : ∀ a, m.nm a = if a ∈ cycleMaskScanAddresses mark s i then (if mark then 1 else 0) else s.nm a
  real : m.rm = s.rm
  realRegisters : m.rr = s.rr

theorem cycleMaskPass_spec (mark : Bool) (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 23 = 0) (one : s.nr 9 = 1)
    (traceEarlier : mark = true → s.nr 18 + s.nr (cycleMaskLimit mark) ≤ s.nr 89) :
    ∃ t steps, steps ≤ 7 * s.nr (cycleMaskLimit mark) + 2 ∧
      BlockRuns (countedLoopFromZero 9 7 (cycleMaskLimit mark) (cycleMaskPassCell mark)) steps s t ∧ t.halted = false ∧
      (∀ a, t.nm a = if a ∈ cycleMaskScanAddresses mark s (s.nr (cycleMaskLimit mark)) then (if mark then 1 else 0) else s.nm a) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 7, 10] → t.nr r = s.nr r := by
  have init : CycleMaskPass s mark 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, by simp [cycleMaskScanAddresses], rfl, rfl⟩
    intro r safe
    exact Function.update_of_ne (by simp at safe; omega) _ _
  have step (i : ℕ) (hi : i < s.nr (cycleMaskLimit mark)) (m : ArithmeticState) (inv : CycleMaskPass s mark i m) :
      ∃ t steps, steps ≤ 4 ∧ BlockRuns (cycleMaskPassCell mark) steps m t ∧ t.halted = false ∧
        CycleMaskPass s mark (i+1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    have mOne := (inv.registers 9 (by decide)).trans one
    obtain ⟨t, steps, cost, run, live, memory, real, realRegisters, keeps⟩ :=
      cycleMaskPassCell_spec mark m inv.entry inv.live ((inv.registers 23 (by decide)).trans zero) mOne
    have atAddress : cycleMaskAddress mark m (m.nr 7) = cycleMaskAddress mark s i := by
      rw [cycleMaskAddress, cycleMaskAddress, inv.registers 89 (by decide), inv.index, inv.registers 18 (by decide)]
      by_cases writes : mark = true
      · have traceBound := traceEarlier writes
        have outside : s.nr 18 + i ∉ cycleMaskScanAddresses mark s i := by
          intro found
          obtain ⟨j, _, equal⟩ := List.mem_map.mp found
          unfold cycleMaskAddress at equal
          omega
        have same := (inv.natural (s.nr 18 + i)).trans (if_neg outside)
        simp [writes, same]
      · simp [writes]
    refine ⟨t, steps, cost, run, live, rfl, live, ?_, ?_, ?_, real.trans inv.real, realRegisters.trans inv.realRegisters⟩
    · simp [keeps 7 (by decide), keeps 9 (by decide), inv.index, mOne]
    · intro r safe
      have away : r ∉ [0, 6, 10] := by simp at safe ⊢; omega
      exact (Function.update_of_ne (by simp at safe; omega) _ _).trans ((keeps r away).trans (inv.registers r safe))
    · intro addr
      change t.nm addr = _
      rw [memory, atAddress]
      by_cases newly : addr = cycleMaskAddress mark s i
      · simp [cycleMaskScanAddresses, List.range_succ, newly]
      · rw [Function.update_of_ne newly, inv.natural]
        simp [cycleMaskScanAddresses, List.range_succ, newly]
  have countSafe : cycleMaskLimit mark ∉ [0, 6, 7, 10] := by cases mark <;> decide
  obtain ⟨t, steps, done, cost, run⟩ := countedLoopFromZero_bounded 9 7 (cycleMaskLimit mark) (s.nr (cycleMaskLimit mark))
    4 (cycleMaskPassCell mark) (CycleMaskPass s mark) (s := s) entry running init
    (fun _ _ inv => ⟨inv.entry, inv.live, inv.index, inv.registers _ countSafe⟩) step
  exact ⟨_, steps, by omega, run, done.live, done.natural, done.real, done.realRegisters, done.registers⟩



theorem markMatchingContractionCycle_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (leftEarlier : s.nr 83 + s.nr 13 ≤ s.nr 89) (rightEarlier : s.nr 84 + s.nr 14 ≤ s.nr 89) :
    ∃ t ticks, ticks ≤ 7 * (s.nr 55 + s.nr 13 + s.nr 14) + 13 ∧
      BlockRuns markMatchingContractionCycle ticks s t ∧ t.halted = false ∧
      (∀ a, t.nm a = if a ∈ matchingContractionMaskAddresses s then 1
        else if a ∈ cycleMaskScanAddresses false s (s.nr 55) then 0 else s.nm a) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 7, 10, 18, 19, 23] → t.nr r = s.nr r := by
  let zeroed := {s with pc := 1, nr := Function.update s.nr 23 0}
  have zero : BlockRuns [.natConst 23 0] 1 s zeroed := by
    apply BlockRuns.of_running_exit
    · simp [zeroed, entry, running, arithmeticStep]
    · exact running
    · rfl
  let a := {zeroed with pc := 0}
  have aOne : a.nr 9 = 1 := by simpa [a, zeroed] using one
  have aZero : a.nr 23 = 0 := by simp [a, zeroed]
  obtain ⟨clean, cleanTicks, cleanCost, clear, clearLive, clearNat, clearReal, clearRR, clearKeeps⟩ :=
    cycleMaskPass_spec false a rfl running aZero aOne (by simp)
  let b := {clean with pc := 0}
  have bFrame (r : ℕ) (safe : r ∉ [0, 6, 7, 10, 23]) : b.nr r = s.nr r := by
    have no : r ≠ 23 := by simp at safe; omega
    exact (clearKeeps r (by simp at safe ⊢; omega)).trans (by simp [a, zeroed, Function.update_of_ne no])
  have bOne : b.nr 9 = 1 := (bFrame 9 (by decide)).trans one
  have bZero : b.nr 23 = 0 := (clearKeeps 23 (by decide)).trans aZero
  let middle := { b with
    pc := 4
    nr := Function.update (Function.update (Function.update b.nr 6 (s.nr 89 + s.nr 12)) 18 (s.nr 83)) 19 (s.nr 13)
    nm := Function.update b.nm (s.nr 89 + s.nr 12) 1 }
  let leftSetup : List ArithmeticInstruction := [.natAdd 6 89 12, .natStore 6 9, .natAdd 18 83 23, .natAdd 19 13 23]
  have markBase : BlockRuns leftSetup 4 b middle := by
    apply BlockRuns.of_running_exit
    · simp [middle, leftSetup, arithmeticStep, b, clearLive, show clean.nr 89 = s.nr 89 from bFrame 89 (by decide),
        show clean.nr 12 = s.nr 12 from bFrame 12 (by decide), show clean.nr 83 = s.nr 83 from bFrame 83 (by decide),
        show clean.nr 13 = s.nr 13 from bFrame 13 (by decide), show clean.nr 23 = 0 from bZero, show clean.nr 9 = 1 from bOne,
        Function.iterate_succ_apply']
    · exact clearLive
    · rfl
  let c := {middle with pc := 0}
  have cleanView (i : ℕ) : b.nm i = if i ∈ cycleMaskScanAddresses false s (s.nr 55) then 0 else s.nm i := by
    simpa [cycleMaskScanAddresses, cycleMaskAddress, cycleMaskLimit, a, zeroed] using clearNat i
  have notCleared (i : ℕ) (below : i < s.nr 89) : i ∉ cycleMaskScanAddresses false s (s.nr 55) := by
    intro found
    obtain ⟨j, _, equal⟩ := List.mem_map.mp found
    simp [cycleMaskAddress] at equal
    omega
  have cMap (i : ℕ) (below : i < s.nr 89) : c.nm i = s.nm i := by
    change Function.update b.nm (s.nr 89 + s.nr 12) 1 i = _
    rw [Function.update_of_ne (by omega : i ≠ s.nr 89 + s.nr 12), cleanView, if_neg (notCleared i below)]
  have c89 : c.nr 89 = s.nr 89 := by simpa [c, middle] using bFrame 89 (by decide)
  have c18 : c.nr 18 = s.nr 83 := by simp [c, middle]
  have c19 : c.nr 19 = s.nr 13 := by simp [c, middle]
  have cOne : c.nr 9 = 1 := by simpa [c, middle] using bOne
  have cZero : c.nr 23 = 0 := by simpa [c, middle] using bZero
  obtain ⟨first, leftTicks, leftCost, leftRun, leftLive, leftNat, leftReal, leftRR, leftKeeps⟩ :=
    cycleMaskPass_spec true c rfl clearLive cZero cOne (by simp [cycleMaskLimit, c18, c19, c89, leftEarlier])
  have leftList : cycleMaskScanAddresses true c (c.nr 19) =
      (List.range (s.nr 13)).map (fun i => s.nr 89 + s.nm (s.nr 83 + i)) := by
    rw [cycleMaskScanAddresses, c19]
    apply List.map_congr_left
    intro i indexed
    have inside := List.mem_range.mp indexed
    simp [cycleMaskAddress, c89, c18, cMap (s.nr 83 + i) (by omega)]
  have firstMap (i : ℕ) (earlier : i < s.nr 89) : first.nm i = s.nm i := by
    have none : i ∉ cycleMaskScanAddresses true c (c.nr (cycleMaskLimit true)) := by
      change i ∉ cycleMaskScanAddresses true c (c.nr 19)
      rw [leftList]
      intro found
      obtain ⟨j, _, equal⟩ := List.mem_map.mp found
      omega
    exact (leftNat i).trans ((if_neg none).trans (cMap i earlier))
  let d := {first with pc := 0}
  have dBase (r : ℕ) (safe : r ∉ [0, 6, 7, 10, 18, 19, 23]) : d.nr r = s.nr r := by
    have a : r ≠ 6 := by simp at safe; omega
    have b : r ≠ 18 := by simp at safe; omega
    have cSafe : r ≠ 19 := by simp at safe; omega
    apply (leftKeeps r (by simp at safe ⊢; omega)).trans
    simpa [c, middle, Function.update_of_ne a, Function.update_of_ne b, Function.update_of_ne cSafe] using
      bFrame r (by simp at safe ⊢; omega)
  have dZero : d.nr 23 = 0 := (leftKeeps 23 (by decide)).trans cZero
  let placed := {d with pc := 2, nr := Function.update (Function.update d.nr 18 (s.nr 84)) 19 (s.nr 14)}
  have switch : BlockRuns [.natAdd 18 84 23, .natAdd 19 14 23] 2 d placed := by
    apply BlockRuns.of_running_exit
    · simp [placed, d, leftLive, show first.nr 23 = 0 from dZero, show first.nr 84 = s.nr 84 from dBase 84 (by decide),
        show first.nr 14 = s.nr 14 from dBase 14 (by decide), arithmeticStep, Function.iterate_succ_apply']
    · exact leftLive
    · rfl
  let e := {placed with pc := 0}
  have eOne : e.nr 9 = 1 := by simpa [e, placed] using (dBase 9 (by decide)).trans one
  have eZero : e.nr 23 = 0 := by simpa [e, placed] using dZero
  have e89 : e.nr 89 = s.nr 89 := by simpa [e, placed] using dBase 89 (by decide)
  have e18 : e.nr 18 = s.nr 84 := by simp [e, placed]
  have e19 : e.nr 19 = s.nr 14 := by simp [e, placed]
  have rightList : cycleMaskScanAddresses true e (e.nr 19) =
      (List.range (s.nr 14)).map (fun i => s.nr 89 + s.nm (s.nr 84 + i)) := by
    rw [cycleMaskScanAddresses, e19]
    apply List.map_congr_left
    intro i indexed
    have inside := List.mem_range.mp indexed
    have same : e.nm (s.nr 84 + i) = s.nm (s.nr 84 + i) := firstMap _ (by omega)
    simp [cycleMaskAddress, e89, e18, same]
  obtain ⟨t, rightTicks, rightCost, rightRun, rightLive, rightNat, rightReal, rightRR, rightKeeps⟩ :=
    cycleMaskPass_spec true e rfl leftLive eZero eOne (by simp [cycleMaskLimit, e18, e19, e89, rightEarlier])
  have run : BlockRuns markMatchingContractionCycle (1 + (cleanTicks + (4 + (leftTicks + (2 + rightTicks))))) s _ :=
    zero.append (clear.append (markBase.append (leftRun.append (switch.append rightRun))))
  refine ⟨_, _, ?_, run, rightLive, ?_, rightReal.trans (leftReal.trans clearReal), rightRR.trans (leftRR.trans clearRR), ?_⟩
  · change cleanTicks ≤ 7 * a.nr 55 + 2 at cleanCost
    change leftTicks ≤ 7 * c.nr 19 + 2 at leftCost
    change rightTicks ≤ 7 * e.nr 19 + 2 at rightCost
    rw [show a.nr 55 = s.nr 55 by simp [a, zeroed]] at cleanCost
    rw [c19] at leftCost
    rw [e19] at rightCost
    omega
  · intro i
    change t.nm i = _
    have leftValue : e.nm i = first.nm i := rfl
    have baseValue : c.nm i = Function.update b.nm (s.nr 89 + s.nr 12) 1 i := rfl
    rw [rightNat, leftValue, leftNat, baseValue]
    change (if i ∈ cycleMaskScanAddresses true e (e.nr 19) then 1 else
      if i ∈ cycleMaskScanAddresses true c (c.nr 19) then 1 else Function.update b.nm (s.nr 89 + s.nr 12) 1 i) = _
    rw [rightList, leftList]
    simp only [matchingContractionMaskAddresses, List.mem_cons, List.mem_append]
    by_cases base : i = s.nr 89 + s.nr 12
    · subst i; simp [Function.update_self]
    · rw [Function.update_of_ne base, cleanView]
      simp only [base, false_or]
      by_cases right : i ∈ (List.range (s.nr 14)).map (fun j => s.nr 89 + s.nm (s.nr 84 + j)) <;>
        by_cases left : i ∈ (List.range (s.nr 13)).map (fun j => s.nr 89 + s.nm (s.nr 83 + j)) <;> simp [left, right]
  · intro r safe
    have not18 : r ≠ 18 := by simp at safe; omega
    have not19 : r ≠ 19 := by simp at safe; omega
    exact (rightKeeps r (by simp at safe ⊢; omega)).trans
      (by simpa [e, placed, Function.update_of_ne not18, Function.update_of_ne not19] using dBase r safe)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractMaskRAM

/-! matching/MatchingContractForestRefinement.lean -/
section RppSource_MatchingContractForestRefinement
namespace VehicleRoutingSurvey.Routing

/-- The raw forest updates and the active registry ID cells have separate tables.
The cycle marks stay readable throughout the pass. -/
structure MatchingContractForestLayout (s : ArithmeticState) (n : ℕ) : Prop where
  size : s.nr 55 = n
  parent : s.nr 52 = s.nr 51 + n
  depth : s.nr 53 = s.nr 51 + n + n
  nodesAfter : s.nr 53 + n ≤ s.nr 74
  maskAfter : s.nr 74 + n ≤ s.nr 89

private def partialContractedForestRole {n : ℕ} (old next : AlternatingForestState (Fin n))
    (processed : ℕ) (v : Fin n) : AlternatingForestRole (Fin n) :=
  if v.val < processed then next.role v else old.role v

theorem contractedMatchingForestMemory_encodes {n : ℕ} {s : ArithmeticState}
    {forest : AlternatingForestState (Fin n)} (layout : MatchingContractForestLayout s n)
    (encoded : AlternatingForestMemory forest (s.nr 51) s.nm) (cycle : Finset (Fin n)) (base : Fin n)
    (baseAt : s.nr 12 = base.val)
    (marks : ∀ v : Fin n, wasContractedRepresentative s v.val ↔ v ∈ cycle) :
    AlternatingForestMemory (forest.contract cycle base) (s.nr 51) (contractedMatchingForestMemory s n) := by
  let next := forest.contract cycle base
  have depthBefore : s.nr 52 + n = s.nr 53 := by rw [layout.parent, layout.depth]
  have roleParent : s.nr 51 + n = s.nr 52 := layout.parent.symm
  have abc := layout.nodesAfter
  have mask := layout.maskAfter
  have markFixed (i : ℕ) (upto : i ≤ n) (v : Fin n) :
      wasContractedRepresentative {s with nr := Function.update s.nr 7 i, nm := contractedMatchingForestMemory s i} v.val
        ↔ v ∈ cycle := by
    change 0 < contractedMatchingForestMemory s i (s.nr 89 + v.val) ↔ _
    rw [contractedMatchingForestMemory_unchanged s i _ (.inr (by omega)) (.inr (by omega)) (.inr (by omega))]
    exact marks v
  have track (i : ℕ) (upto : i ≤ n) (v : Fin n) :
      contractedMatchingForestMemory s i (s.nr 51 + v.val) =
        alternatingRoleCode (partialContractedForestRole forest next i v) ∧
      contractedMatchingForestMemory s i (s.nr 52 + v.val) =
        alternatingParentCode (partialContractedForestRole forest next i v) := by
    induction i generalizing v with
    | zero =>
      exact ⟨by simpa [partialContractedForestRole, contractedMatchingForestMemory] using (encoded v).1,
        by simpa [partialContractedForestRole, contractedMatchingForestMemory, layout.parent] using (encoded v).2.1⟩
    | succ i ih =>
      have iLt : i < n := by omega
      have vLt := v.isLt
      let k : Fin n := ⟨i, iLt⟩
      let a := {s with nr := Function.update s.nr 7 i, nm := contractedMatchingForestMemory s i}
      have readBack : contractedMatchingForestMemory s (i+1) = contractedMatchingForestCellMemory a := rfl
      have earlier := ih (by omega) v
      have here := ih (by omega) k
      have kRole : a.nm (s.nr 51 + i) = alternatingRoleCode (forest.role k) := by
        simpa [a, k, partialContractedForestRole] using here.1
      have kParent : a.nm (s.nr 52 + i) = alternatingParentCode (forest.role k) := by
        simpa [a, k, partialContractedForestRole] using here.2
      have atMark : wasContractedRepresentative a i ↔ k ∈ cycle := markFixed i (by omega) k
      have hiddenTest : (wasContractedRepresentative a (a.nr 7) ∧ a.nr 7 ≠ a.nr 12) ↔ k ∈ cycle ∧ k ≠ base := by
        have different : i ≠ base.val ↔ k ≠ base := by
          constructor
          · rintro ne rfl
            exact ne rfl
          · intro ne equal
            exact ne (Fin.ext equal)
        simpa [a, baseAt, k] using and_congr atMark different
      by_cases own : v.val = i
      · have vAt : v = k := Fin.ext own
        subst v
        have now : partialContractedForestRole forest next (i+1) k = next.role k := by
          simp [partialContractedForestRole, k]
        rw [readBack, now, contractedMatchingForestCellMemory]
        by_cases hidden : k ∈ cycle ∧ k ≠ base
        · rw [if_pos (hiddenTest.mpr hidden)]
          simp (disch := omega) [a, k, hiddenContractionForestMemory, Function.update_apply, layout.size,
            next, AlternatingForestState.contract, hidden, alternatingRoleCode, alternatingParentCode]
        · rw [if_neg (fun h => hidden (hiddenTest.mp h))]
          have nextRole : next.role k = (match forest.role k with
              | .inner p => .inner (blossomRepresentative cycle base p)
              | other => other) := by
            simp [next, AlternatingForestState.contract, hidden] <;> cases forest.role k <;> rfl
          rw [nextRole]
          cases kind : forest.role k with
          | unlabelled =>
            have inner : ¬survivingInnerParentEntersCycle a := by
              intro check
              have tooSmall := check.1
              change 2 ≤ a.nm (s.nr 51 + i) at tooSmall
              simp [kRole, kind, alternatingRoleCode] at tooSmall
            simpa [k, if_neg inner, kind] using And.intro kRole kParent
          | outer p =>
            have inner : ¬survivingInnerParentEntersCycle a := by
              intro check
              have tooSmall := check.1
              change 2 ≤ a.nm (s.nr 51 + i) at tooSmall
              simp [kRole, kind, alternatingRoleCode] at tooSmall
            simpa [k, if_neg inner, kind] using And.intro kRole kParent
          | inner p =>
            have enters : survivingInnerParentEntersCycle a ↔ p ∈ cycle := by
              change (2 ≤ a.nm (s.nr 51 + i) ∧ wasContractedRepresentative a (a.nm (s.nr 52 + i))) ↔ _
              rw [kRole, kParent, kind]
              simpa [alternatingRoleCode, alternatingParentCode] using markFixed i (by omega) p
            by_cases absorbed : p ∈ cycle
            · rw [if_pos (enters.mpr absorbed)]
              have cross : s.nr 51 + i ≠ s.nr 52 + i := by omega
              have roleAt : contractedMatchingForestMemory s i (s.nr 51 + i) = 2 := by
                simpa [kind, alternatingRoleCode] using kRole
              simp [a, k, baseAt, blossomRepresentative, absorbed, Function.update_of_ne cross, alternatingRoleCode,
                alternatingParentCode, roleAt]
            · rw [if_neg (fun h => absorbed (enters.mp h))]
              simpa [k, kind, blossomRepresentative, absorbed] using And.intro kRole kParent
      · have same : partialContractedForestRole forest next (i+1) v = partialContractedForestRole forest next i v := by
          have eq : v.val < i + 1 ↔ v.val < i := by omega
          simp [partialContractedForestRole, eq]
        have changedRole (query : ℕ) (otherRole : query ≠ s.nr 51 + i) (otherParent : query ≠ s.nr 52 + i)
            (otherNode : query ≠ s.nr 74 + i) : contractedMatchingForestCellMemory a query = a.nm query := by
          unfold contractedMatchingForestCellMemory
          split
          · simpa [a, hiddenContractionForestMemory, Function.update_of_ne otherRole, Function.update_of_ne otherParent,
              Function.update_of_ne otherNode]
          · split
            · simpa [a, Function.update_of_ne otherParent]
            · rfl
        rw [readBack, same, changedRole _ (by omega) (by omega) (by omega),
          changedRole _ (by omega) (by omega) (by omega)]
        exact earlier
  intro v
  have hv := v.isLt
  have out := track n le_rfl v
  simp only [partialContractedForestRole, if_pos hv] at out
  refine ⟨out.1, by simpa only [layout.parent] using out.2, ?_⟩
  rw [show s.nr 51 + n + n + v.val = s.nr 53 + v.val by rw [layout.depth]]
  rw [contractedMatchingForestMemory_unchanged s n _ (.inr (by omega)) (.inr (by omega)) (.inl (by omega))]
  change s.nm (s.nr 53 + v.val) = forest.depth v
  simpa only [layout.depth] using (encoded v).2.2

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractForestRefinement

/-! matching/MatchingContractionPrefixView.lean -/
section RppSource_MatchingContractionPrefixView
namespace VehicleRoutingSurvey.Routing







theorem matchingContractionMaskAddresses_congr {s t : ArithmeticState}
    (fixed : ∀ r ∈ ([12, 13, 14, 83, 84, 89] : List ℕ), t.nr r = s.nr r)
    (traceL : ∀ j < s.nr 13, t.nm (s.nr 83+j) = s.nm (s.nr 83+j))
    (traceR : ∀ j < s.nr 14, t.nm (s.nr 84+j) = s.nm (s.nr 84+j)) :
    matchingContractionMaskAddresses t = matchingContractionMaskAddresses s := by
  have left : (List.range (s.nr 13)).map (fun j => s.nr 89+t.nm (s.nr 83+j)) =
      (List.range (s.nr 13)).map (fun j => s.nr 89+s.nm (s.nr 83+j)) := by
    apply List.map_congr_left
    intro j member
    rw [traceL j (List.mem_range.mp member)]
  have right : (List.range (s.nr 14)).map (fun j => s.nr 89+t.nm (s.nr 84+j)) =
      (List.range (s.nr 14)).map (fun j => s.nr 89+s.nm (s.nr 84+j)) := by
    apply List.map_congr_left
    intro j member
    rw [traceR j (List.mem_range.mp member)]
  simp only [matchingContractionMaskAddresses, fixed 12 (by decide), fixed 13 (by decide), fixed 14 (by decide),
    fixed 83 (by decide), fixed 84 (by decide), fixed 89 (by decide), left, right]

theorem absorbedMatchingOuterRows_congr {s t : ArithmeticState}
    (fixed : ∀ r ∈ ([12, 13, 14, 51, 83, 84] : List ℕ), t.nr r = s.nr r)
    (traceL : ∀ j < s.nr 13, t.nm (s.nr 83+j) = s.nm (s.nr 83+j))
    (traceR : ∀ j < s.nr 14, t.nm (s.nr 84+j) = s.nm (s.nr 84+j))
    (rolesL : ∀ j < s.nr 13,
      t.nm (s.nr 51+s.nm (s.nr 83+j)) = s.nm (s.nr 51+s.nm (s.nr 83+j)))
    (rolesR : ∀ j < s.nr 14,
      t.nm (s.nr 51+s.nm (s.nr 84+j)) = s.nm (s.nr 51+s.nm (s.nr 84+j))) :
    absorbedMatchingOuterRows t = absorbedMatchingOuterRows s := by
  have trace (start count : ℕ) (values : ∀ j < count, t.nm (start+j) = s.nm (start+j))
      (codes : ∀ j < count, t.nm (s.nr 51+s.nm (start+j)) = s.nm (s.nr 51+s.nm (start+j))) :
      traceOuterRowsAt t start count = traceOuterRowsAt s start count := by
    unfold traceOuterRowsAt
    apply traceOuterRows_preserved (m := {t with nr := Function.update t.nr 18 start})
    · simp
    · simpa using fixed 51 (by decide)
    · exact values
    · exact codes
  simp only [absorbedMatchingOuterRows, fixed 12 (by decide), fixed 13 (by decide), fixed 14 (by decide),
    fixed 83 (by decide), fixed 84 (by decide), trace _ _ traceL rolesL, trace _ _ traceR rolesR]



end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionPrefixView

/-! matching/MatchingContractionNodeScan.lean -/
section RppSource_MatchingContractionNodeScan
namespace VehicleRoutingSurvey.Routing

/-- The forest pass hides each absorbed nonbase node ID and preserves all
other IDs. The final installation subsequently writes the fresh ID at base. -/
theorem contractedMatchingForestMemory_nodes {s : ArithmeticState} {k : ℕ}
    (roleRoom : s.nr 51+k ≤ s.nr 74) (parentRoom : s.nr 52+k ≤ s.nr 74)
    (markRoom : s.nr 74+k ≤ s.nr 89) (v : Fin k) :
    contractedMatchingForestMemory s k (s.nr 74+v.val) =
      if wasContractedRepresentative s v.val ∧ v.val ≠ s.nr 12 then 0 else s.nm (s.nr 74+v.val) := by
  have track (i : ℕ) (bound : i ≤ k) :
      contractedMatchingForestMemory s i (s.nr 74+v.val) =
        if v.val < i ∧ wasContractedRepresentative s v.val ∧ v.val ≠ s.nr 12 then 0 else s.nm (s.nr 74+v.val) := by
    induction i with
    | zero => simp [contractedMatchingForestMemory]
    | succ i ih =>
      let a := {s with nr := Function.update s.nr 7 i,nm := contractedMatchingForestMemory s i}
      have test : wasContractedRepresentative a i ↔ wasContractedRepresentative s i := by
        change 0 < contractedMatchingForestMemory s i (s.nr 89+i) ↔ _
        rw [contractedMatchingForestMemory_unchanged s i _ (.inr (by omega)) (.inr (by omega)) (.inr (by omega))]
        rfl
      have index : a.nr 7 = i := by simp [a]
      have base : a.nr 12 = s.nr 12 := by simp [a]
      have old := ih (by omega)
      have step : contractedMatchingForestMemory s (i+1) = contractedMatchingForestCellMemory a := rfl
      rw [step,contractedMatchingForestCellMemory]
      by_cases hidden : wasContractedRepresentative s i ∧ i ≠ s.nr 12
      · have yes : wasContractedRepresentative a (a.nr 7) ∧ a.nr 7 ≠ a.nr 12 := by simpa only [index,base,test] using hidden
        rw [if_pos yes]
        by_cases here : v.val = i
        · simp [hiddenContractionForestMemory,a,here,hidden]
        · have missed : s.nr 74+v.val ≠ s.nr 74+i := by omega
          simp only [hiddenContractionForestMemory,a,Function.update_self,Function.update_of_ne (by decide : 74 ≠ 7),
            Function.update_of_ne (by decide : 52 ≠ 7),Function.update_of_ne (by decide : 51 ≠ 7),
            Function.update_of_ne missed,Function.update_of_ne (by omega : s.nr 74+v.val ≠ s.nr 52+i),
            Function.update_of_ne (by omega : s.nr 74+v.val ≠ s.nr 51+i),old]
          have same : v.val < i+1 ↔ v.val < i := by omega
          simp only [same]
      · have no : ¬(wasContractedRepresentative a (a.nr 7) ∧ a.nr 7 ≠ a.nr 12) := by simpa only [index,base,test] using hidden
        rw [if_neg no]
        have same : (v.val < i+1 ∧ wasContractedRepresentative s v.val ∧ v.val ≠ s.nr 12) ↔
            (v.val < i ∧ wasContractedRepresentative s v.val ∧ v.val ≠ s.nr 12) := by
          constructor
          · rintro ⟨hi,member,away⟩
            have diff : v.val ≠ i := fun eq => hidden (eq ▸ And.intro member away)
            exact ⟨by omega,member,away⟩
          · rintro ⟨hi,rest⟩; exact ⟨by omega,rest⟩
        simp only [same]
        split
        · simpa [a,Function.update_of_ne (by omega : s.nr 74+v.val ≠ s.nr 52+i)] using old
        · exact old
  simpa only [v.isLt,true_and] using track k le_rfl

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionNodeScan

/-! matching/MatchingNaturalZero.lean -/
section RppSource_MatchingNaturalZero
namespace VehicleRoutingSurvey.Routing

private def preservesNaturalZero (r : ℕ) (ins : ArithmeticInstruction) : Bool :=
  match ins with
  | .natConst port n => decide (port ≠ r ∨ n = 0)
  | _ => decide (naturalDestination ins ≠ r)

private theorem arithmeticStep_preservesNaturalZero {code : List ArithmeticInstruction} {r : ℕ}
    (allowed : code.all (preservesNaturalZero r) = true) (s : ArithmeticState) (zero : s.nr r = 0) :
    (arithmeticStep code s).nr r = 0 := by
  by_cases stopped : s.halted = true
  · simpa [arithmeticStep, stopped] using zero
  cases fetched : code[s.pc]? with
  | none => simpa [arithmeticStep, stopped, fetched] using zero
  | some ins =>
    have readable := List.all_eq_true.mp allowed ins (List.mem_of_getElem? fetched)
    cases ins <;>
      simp [preservesNaturalZero, naturalDestination, arithmeticStep, stopped, fetched, Function.update_apply, zero] at readable ⊢
    all_goals
      intro same
      subst r
      simp_all

theorem blockRuns_preservesNaturalZero {code : List ArithmeticInstruction} {r : ℕ} {s t : ArithmeticState}
    {ticks : ℕ} (allowed : code.all (preservesNaturalZero r) = true) (run : BlockRuns code ticks s t)
    (zero : s.nr r = 0) : t.nr r = 0 := by
  have stays (n : ℕ) : ((arithmeticStep code)^[n] s).nr r = 0 := by
    induction n with
    | zero => exact zero
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact arithmeticStep_preservesNaturalZero allowed _ ih
  rw [← run.run]
  exact stays ticks

end VehicleRoutingSurvey.Routing
end RppSource_MatchingNaturalZero

/-! matching/MatchingCycleSequence.lean -/
section RppSource_MatchingCycleSequence
namespace VehicleRoutingSurvey.Routing























































theorem writeMatchingContractionCycle_bound (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t steps, steps ≤ 26 * (s.nr 13 + s.nr 14) + 34 ∧ BlockRuns writeMatchingContractionCycle steps s t ∧
      t.halted = false ∧ t.nr 68 = s.nr 68 + 4 * matchingCycleChildCount s ∧
      (∀ a < s.nr 68, t.nm a = startMatchingCycleNat s a) ∧ t.rm = startMatchingCycleReal s ∧
      ∀ r, r ∉ [0, 6, 7, 10, 15, 16, 17, 18, 23, 68] → t.nr r = s.nr r := by
  obtain ⟨t, steps, budget, run, live, cursor, natural, real, registers, _⟩ :=
    writeMatchingContractionCycle_spec s entry running one
  exact ⟨t, steps, budget, run, live, cursor, natural, real, registers⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingCycleSequence

/-! matching/MatchingContractHandler.lean -/
section RppSource_MatchingContractHandler
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

































private theorem absorbedMatchingOuterRows_length_le (s : ArithmeticState) :
    (absorbedMatchingOuterRows s).length ≤ s.nr 13 + s.nr 14 + 1 := by
  unfold absorbedMatchingOuterRows traceOuterRowsAt tracedOuterReps
  simp only [List.length_append, List.length_singleton, List.length_map]
  have left := List.length_filter_le (fun j => decide (tracedRepresentativeOuter
    {s with nr := Function.update s.nr 18 (s.nr 83)} j)) (List.range (s.nr 13))
  have right := List.length_filter_le (fun j => decide (tracedRepresentativeOuter
    {s with nr := Function.update s.nr 18 (s.nr 84)} j)) (List.range (s.nr 14))
  simp only [List.length_range] at left right
  omega

set_option maxHeartbeats 1800000 in
 theorem finishMatchingContractionStructure_spec (s : ArithmeticState) (layout : MatchingContractionLayout s)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0) :
    ∃ t ticks, ticks ≤ 89 * s.nr 55 + 67 ∧ BlockRuns finishMatchingContractionStructure ticks s t ∧
      t.halted = false ∧ t.nr 87 ≤ s.nr 55 ∧
      (∀ a < s.nr 51, t.nm a = s.nm a) ∧ (∀ a < s.nr 62, t.rm a = s.rm a) ∧
      (∀ r, r ∉ [0, 6, 7, 10, 11, 15, 16, 17, 18, 19, 23, 68, 76, 87, 99] → t.nr r = s.nr r) ∧
      t.rm = startMatchingCycleReal s ∧
      (s.nr 52+s.nr 55 ≤ s.nr 86 → s.nr 74+s.nr 55 ≤ s.nr 86 → MatchingContractionPrefixView s t) := by
  obtain ⟨cycle, cycleTicks, cycleCost, cycleRun, cycleLive, _, cycleNat, cycleReal, cycleKeeps⟩ :=
    writeMatchingContractionCycle_bound s entry running one
  let a := {cycle with pc := 0}
  have aOne : a.nr 9 = 1 := (cycleKeeps 9 (by decide)).trans one
  have a85 : a.nr 89 = s.nr 89 := cycleKeeps 89 (by decide)
  have aL : a.nr 83 + a.nr 13 ≤ a.nr 89 := by
    rw [cycleKeeps 83 (by decide), cycleKeeps 13 (by decide), a85]
    have h₁ := layout.leftBefore
    have h₂ := layout.rowsBeforeFresh
    have h₃ := layout.freshBeforeMask
    omega
  have aR : a.nr 84 + a.nr 14 ≤ a.nr 89 := by
    rw [cycleKeeps 84 (by decide), cycleKeeps 14 (by decide), a85]
    have h₁ := layout.rightBefore
    have h₂ := layout.rowsBeforeFresh
    have h₃ := layout.freshBeforeMask
    omega
  have earlyCycle (addr : ℕ) (lower : addr < s.nr 68) (noStart : addr ≠ s.nr 77 + s.nr 76)
      (noCount : addr ≠ s.nr 78 + s.nr 76) : a.nm addr = s.nm addr := by
    rw [show a.nm addr = startMatchingCycleNat s addr from cycleNat addr lower]
    simp [startMatchingCycleNat, Function.update_of_ne noStart, Function.update_of_ne noCount]
  have protectedPointer : s.nr 86 ≤ s.nr 68 := by
    have h₁ := layout.rowsBeforeFresh
    have h₂ := layout.freshBeforeMask
    have h₃ := layout.maskBeforeRecords
    omega
  have aPre (addr : ℕ) (below : addr < s.nr 58) : a.nm addr = s.nm addr := by
    have after := layout.selectorsBeforeRecords
    have rows := layout.tablesBeforeRows
    exact earlyCycle addr (by omega) (by omega) (by omega)
  have aTraceL (j : ℕ) (hj : j < s.nr 13) : a.nm (s.nr 83 + j) = s.nm (s.nr 83 + j) := by
    obtain ⟨header, count, _⟩ := layout.recordHeadersBeforeTrace
    have left := layout.leftBefore
    exact earlyCycle _ (by omega) (by omega) (by omega)
  have aTraceR (j : ℕ) (hj : j < s.nr 14) : a.nm (s.nr 84 + j) = s.nm (s.nr 84 + j) := by
    obtain ⟨header, count, order⟩ := layout.recordHeadersBeforeTrace
    have right := layout.rightBefore
    exact earlyCycle _ (by omega) (by omega) (by omega)
  obtain ⟨marked, maskTicks, maskCost, mark, markLive, maskNat, maskReal, _, maskKeeps⟩ :=
    markMatchingContractionCycle_spec a rfl cycleLive aOne aL aR
  let b := {marked with pc := 0}
  have markEarlier (addr : ℕ) (below : addr < a.nr 89) : b.nm addr = a.nm addr := by
    have noClear : addr ∉ cycleMaskScanAddresses false a (a.nr 55) := by
      intro found
      obtain ⟨j, _, equal⟩ := List.mem_map.mp found
      simp [cycleMaskAddress] at equal
      omega
    have noMark : addr ∉ matchingContractionMaskAddresses a := by
      unfold matchingContractionMaskAddresses
      intro present
      rcases List.mem_cons.mp present with base | alternate
      · omega
      · rcases List.mem_append.mp alternate with left | right
        · obtain ⟨_, _, equal⟩ := List.mem_map.mp left
          omega
        · obtain ⟨_, _, equal⟩ := List.mem_map.mp right
          omega
    exact (maskNat addr).trans (by simp [noClear, noMark])
  have bFrame (r : ℕ) (safe : r ∉ [0, 6, 7, 10, 15, 16, 17, 18, 19, 23, 68]) : b.nr r = s.nr r :=
    (maskKeeps r (by simp at safe ⊢; omega)).trans (cycleKeeps r (by simp at safe ⊢; omega))
  have bOne : b.nr 9 = 1 := (bFrame 9 (by decide)).trans one
  have rowsEarlier : s.nr 86 ≤ a.nr 89 := by
    rw [a85]
    have h₁ := layout.rowsBeforeFresh
    have h₂ := layout.freshBeforeMask
    omega
  have lowL : b.nr 83 + b.nr 13 ≤ b.nr 86 := by
    rw [bFrame 83 (by decide), bFrame 13 (by decide), bFrame 86 (by decide)]
    exact layout.leftBefore
  have lowR : b.nr 84 + b.nr 14 ≤ b.nr 86 := by
    rw [bFrame 84 (by decide), bFrame 14 (by decide), bFrame 86 (by decide)]
    exact layout.rightBefore
  have lowRole : b.nr 51 + b.nr 55 ≤ b.nr 86 := by
    rw [bFrame 51 (by decide), bFrame 55 (by decide), bFrame 86 (by decide)]
    have h₁ := layout.roleEnd
    have h₂ := layout.representativeEnd
    have h₃ := layout.tablesBeforeRows
    omega
  have bValidL (j : ℕ) (hj : j < b.nr 13) : b.nm (b.nr 83 + j) < b.nr 55 := by
    rw [bFrame 13 (by decide)] at hj
    rw [bFrame 83 (by decide), bFrame 55 (by decide), markEarlier _ (by have h := layout.leftBefore; omega), aTraceL j hj]
    exact layout.leftValid j hj
  have bValidR (j : ℕ) (hj : j < b.nr 14) : b.nm (b.nr 84 + j) < b.nr 55 := by
    rw [bFrame 14 (by decide)] at hj
    rw [bFrame 84 (by decide), bFrame 55 (by decide), markEarlier _ (by have h := layout.rightBefore; omega), aTraceR j hj]
    exact layout.rightValid j hj
  obtain ⟨rows, rowTicks, rowCost, rowRun, rowLive, rowCount, rowCells, rowNat, rowReal, rowKeeps⟩ :=
    collectAbsorbedOuterRows_spec b rfl markLive bOne lowL lowR lowRole bValidL bValidR
  let c := {rows with pc := 0}
  have rowBound : c.nr 87 ≤ s.nr 55 := by
    have size := absorbedMatchingOuterRows_length_le b
    rw [bFrame 13 (by decide), bFrame 14 (by decide)] at size
    exact rowCount.trans_le (size.trans layout.cycleSize)
  have cFrame (r : ℕ) (safe : r ∉ [0, 6, 7, 10, 11, 15, 16, 17, 18, 19, 23, 68, 87]) : c.nr r = s.nr r :=
    (rowKeeps r (by simp at safe ⊢; omega)).trans (bFrame r (by simp at safe ⊢; omega))
  have c56 : c.nr 55 = s.nr 55 := cFrame 55 (by decide)
  have cOne : c.nr 9 = 1 := (cFrame 9 (by decide)).trans one
  have cRole : c.nr 51 + c.nr 55 ≤ c.nr 57 := by
    rw [cFrame 51 (by decide), c56, cFrame 57 (by decide)]
    exact layout.roleEnd
  have cFresh : c.nr 57 + c.nr 55 ≤ c.nr 88 := by
    rw [cFrame 57 (by decide), c56, cFrame 88 (by decide)]
    have reps := layout.representativeEnd
    have table := layout.tablesBeforeRows
    have scratch := layout.rowsBeforeFresh
    omega
  have cMark : c.nr 88 + c.nr 55 ≤ c.nr 89 := by
    rw [cFrame 88 (by decide), c56, cFrame 89 (by decide)]
    exact layout.freshBeforeMask
  have cPre (addr : ℕ) (lower : addr < s.nr 58) : c.nm addr = s.nm addr := by
    have belowRows : addr < s.nr 86 := lt_of_lt_of_le lower layout.tablesBeforeRows
    exact (rowNat addr (.inl (by rwa [bFrame 86 (by decide)]))).trans ((markEarlier addr (by omega)).trans (aPre addr lower))
  have cValid (j : ℕ) (inside : j < c.nr 55) : originalTopRepresentative c j < c.nr 55 := by
    rw [c56] at inside ⊢
    rw [originalTopRepresentative, cFrame 57 (by decide), cPre _ (by have h := layout.representativeEnd; omega)]
    exact layout.representativeValid j inside
  obtain ⟨reps, repTicks, repCost, repRun, repLive, freshCount, repCells, freshCells, repNat, repReal, _⟩ :=
    contractMatchingRepresentativeBlock_spec c rfl rowLive cOne cRole cFresh cMark cValid
  let d := {reps with pc := 0}
  have repKeeps (r : ℕ) (safe : r ∉ [0, 6, 7, 10, 11, 23, 99]) : d.nr r = c.nr r := by
    change reps.nr r = c.nr r
    rw [← repRun.run]
    exact arithmeticRun_keeps_from_destination_list [0, 6, 7, 10, 11, 23, 99] (by decide) safe c repTicks
  have dFrame (r : ℕ) (safe : r ∉ [0, 6, 7, 10, 11, 15, 16, 17, 18, 19, 23, 68, 87, 99]) : d.nr r = s.nr r :=
    (repKeeps r (by simp at safe ⊢; omega)).trans (cFrame r (by simp at safe ⊢; omega))
  have dOne : d.nr 9 = 1 := (dFrame 9 (by decide)).trans one
  have wholeEarlier : BlockRuns (appendBlock writeMatchingContractionCycle
        (appendBlock markMatchingContractionCycle (appendBlock collectAbsorbedOuterRows contractMatchingRepresentativeBlock)))
      (cycleTicks + (maskTicks + (rowTicks + repTicks))) s _ := cycleRun.append (mark.append (rowRun.append repRun))
  have dZero : d.nr 23 = 0 := by
    have stayed := blockRuns_preservesNaturalZero (r := 23) (by decide) wholeEarlier zero
    exact stayed
  obtain ⟨forest, forestTicks, forestCost, forestRun, forestLive, forestNat, forestReal, _, forestKeeps⟩ :=
    contractMatchingForestBlock_spec d rfl repLive dOne dZero
  let e := {forest with pc := 0}
  have eOne : e.nr 9 = 1 := (forestKeeps 9 (by decide)).trans dOne
  obtain ⟨t, install, installLive, installNat, installCount, installReal⟩ := installNewTopMatchingBlossom_spec e rfl forestLive eOne
  have run : BlockRuns finishMatchingContractionStructure
      (cycleTicks + (maskTicks + (rowTicks + (repTicks + (forestTicks + 3))))) s _ :=
    cycleRun.append (mark.append (rowRun.append (repRun.append (forestRun.append install))))
  have lastKeeps (r : ℕ) (away : r ∉ [0, 6, 76] := by decide) : t.nr r = e.nr r := by
    rw [← install.run]
    exact arithmeticRun_keeps_from_destination_list [0, 6, 76] (by decide) away e 3
  have runKeeps (r : ℕ) (safe : r ∉ [0, 6, 7, 10, 11, 15, 16, 17, 18, 19, 23, 68, 76, 87, 99] := by decide) :
      (relocateState writeMatchingContractionCycle.length
        (relocateState markMatchingContractionCycle.length
          (relocateState collectAbsorbedOuterRows.length
            (relocateState contractMatchingRepresentativeBlock.length
              (relocateState contractMatchingForestBlock.length t))))).nr r = s.nr r := by
    rw [← run.run]
    exact arithmeticRun_keeps_from_destination_list [0, 6, 7, 10, 11, 15, 16, 17, 18, 19, 23, 68, 76, 87, 99]
      (by decide) safe s _
  have retainCount : t.nr 87 = c.nr 87 :=
    (lastKeeps 87).trans ((forestKeeps 87 (by decide)).trans (repKeeps 87 (by decide)))
  refine ⟨_, _, ?_, run, installLive, retainCount.trans_le rowBound, ?_, ?_, (fun r safe => runKeeps r safe),
    installReal.trans (forestReal.trans (repReal.trans (rowReal.trans (maskReal.trans cycleReal)))), ?_⟩
  · rw [cycleKeeps 55 (by decide), cycleKeeps 13 (by decide), cycleKeeps 14 (by decide)] at maskCost
    rw [bFrame 13 (by decide), bFrame 14 (by decide)] at rowCost
    rw [c56] at repCost
    rw [dFrame 55 (by decide)] at forestCost
    have traceCount := layout.cycleSize
    omega
  · intro addr lower
    change t.nm addr = s.nm addr
    have role : addr < d.nr 51 := by rwa [dFrame 51 (by decide)]
    have parent : addr < d.nr 52 := by rw [dFrame 52 (by decide)]; exact lower.trans_le layout.roleAfter
    have node : addr < d.nr 74 := by rw [dFrame 74 (by decide)]; exact lower.trans_le layout.nodeTableAfter
    have eNode : e.nr 74 = d.nr 74 := forestKeeps 74 (by decide)
    have eBefore : addr < e.nr 74 := by rwa [eNode]
    have lastWrite : addr ≠ e.nr 74 + e.nr 12 := by omega
    rw [installNat, Function.update_of_ne lastWrite]
    change forest.nm addr = s.nm addr
    rw [forestNat, contractedMatchingForestMemory_unchanged d _ addr (.inl role) (.inl parent) (.inl node)]
    have originalRep : addr < c.nr 57 := by
      rw [cFrame 57 (by decide)]
      have h := layout.roleEnd
      omega
    have firstFree : addr < c.nr 88 := by
      have h := cFresh
      omega
    have leftOfCandidates : addr < s.nr 58 := by
      have h₁ := layout.roleEnd
      have h₂ := layout.representativeEnd
      omega
    exact (repNat addr (.inl originalRep) (.inl firstFree)).trans (cPre addr leftOfCandidates)
  · intro addr below
    have different : addr ≠ s.nr 75 + s.nr 76 := by have h := layout.nodeDualAfter; omega
    exact (congrFun (installReal.trans (forestReal.trans (repReal.trans (rowReal.trans (maskReal.trans cycleReal))))) addr).trans
      (Function.update_of_ne different _ _)
  · intro parentBefore nodesBefore
    have bTraceL (j : ℕ) (hj : j < s.nr 13) : b.nm (s.nr 83+j) = s.nm (s.nr 83+j) :=
      (markEarlier _ (by have h := layout.leftBefore; omega)).trans (aTraceL j hj)
    have bTraceR (j : ℕ) (hj : j < s.nr 14) : b.nm (s.nr 84+j) = s.nm (s.nr 84+j) :=
      (markEarlier _ (by have h := layout.rightBefore; omega)).trans (aTraceR j hj)
    have bRoleAt (v : ℕ) (hv : v < s.nr 55) : b.nm (s.nr 51+v) = s.nm (s.nr 51+v) := by
      have endRole := layout.roleEnd
      have endRep := layout.representativeEnd
      have floor := layout.tablesBeforeRows
      exact (markEarlier _ (by omega)).trans (aPre _ (by omega))
    have rowModel : absorbedMatchingOuterRows b = absorbedMatchingOuterRows s :=
      absorbedMatchingOuterRows_congr (fun r listed => bFrame r (by simp at listed ⊢; omega)) bTraceL bTraceR
        (fun j hj => bRoleAt _ (layout.leftValid j hj)) (fun j hj => bRoleAt _ (layout.rightValid j hj))
    have marks : matchingContractionMaskAddresses a = matchingContractionMaskAddresses s :=
      matchingContractionMaskAddresses_congr (fun r listed => cycleKeeps r (by simp at listed ⊢; omega)) aTraceL aTraceR
    have marker (v : ℕ) (hv : v < s.nr 55) : c.nm (s.nr 89+v) =
        if s.nr 89+v ∈ matchingContractionMaskAddresses s then 1 else 0 := by
      have bound : b.nr 86 + rows.nr 87 ≤ s.nr 89+v := by
        rw [bFrame 86 (by decide)]
        have layout1 := layout.rowsBeforeFresh
        have layout2 := layout.freshBeforeMask
        change c.nr 87 ≤ s.nr 55 at rowBound
        have lengthBound : rows.nr 87 ≤ s.nr 55 := rowBound
        omega
      change rows.nm _ = _
      rw [rowNat _ (Or.inr bound)]
      change marked.nm _ = _
      have disk : s.nr 89+v ∈ cycleMaskScanAddresses false a (a.nr 55) := by
        apply List.mem_map.mpr
        refine ⟨v, List.mem_range.mpr (by rw [cycleKeeps 55 (by decide)]; exact hv), ?_⟩
        simp [cycleMaskAddress, a85]
      simp only [maskNat, marks, if_pos disk]
    have freshModel : contractedOriginalsNewlyOuter c (c.nr 55) = contractionFreshOriginalsBefore s := by
      unfold contractedOriginalsNewlyOuter contractionFreshOriginalsBefore
      rw [c56]
      apply List.filter_congr
      intro j member
      have hj := List.mem_range.mp member
      have repSame : originalTopRepresentative c j = originalTopRepresentative s j := by
        simp only [originalTopRepresentative, cFrame 57 (by decide)]
        exact cPre _ (by have last := layout.representativeEnd; omega)
      have vlt := layout.representativeValid j hj
      have roleSame : c.nm (s.nr 51 + originalTopRepresentative s j) = s.nm (s.nr 51 + originalTopRepresentative s j) :=
        cPre _ (by have h := layout.roleEnd; have e := layout.representativeEnd; omega)
      simp only [newlyOuterOriginalInContraction, wasContractedRepresentative, repSame, cFrame 89 (by decide),
        cFrame 51 (by decide), marker _ vlt, roleSame]
      split <;> simp_all
    have later (addr : ℕ) (high : s.nr 86 ≤ addr) : t.nm addr = d.nm addr := by
      have roleEnd : d.nr 51 + d.nr 55 ≤ addr := by
        rw [dFrame 51 (by decide), dFrame 55 (by decide)]
        have h := layout.roleEnd
        have j := layout.representativeEnd
        have q := layout.tablesBeforeRows
        omega
      have parentEnd : d.nr 52 + d.nr 55 ≤ addr := by
        rw [dFrame 52 (by decide), dFrame 55 (by decide)]
        omega
      have registryEnd : d.nr 74 + d.nr 55 ≤ addr := by
        rw [dFrame 74 (by decide), dFrame 55 (by decide)]
        omega
      have node : addr ≠ e.nr 74 + e.nr 12 := by
        rw [forestKeeps 74 (by decide), forestKeeps 12 (by decide), dFrame 12 (by decide)]
        have base := layout.baseValid
        have size := dFrame 55 (by decide)
        omega
      rw [installNat, Function.update_of_ne node]
      change forest.nm addr = _
      rw [forestNat, contractedMatchingForestMemory_unchanged d _ addr (.inr roleEnd) (.inr parentEnd) (.inr registryEnd)]
    have freshBound : reps.nr 99 ≤ s.nr 55 := by
      rw [freshCount, freshModel]
      simpa only [contractionFreshOriginalsBefore, List.length_range] using
        (List.length_filter_le (fun j => decide (s.nr 89+originalTopRepresentative s j ∈ matchingContractionMaskAddresses s ∧
          2 ≤ s.nm (s.nr 51+originalTopRepresentative s j))) (List.range (s.nr 55)))
    have dMask (v : ℕ) (inside : v < s.nr 55) : d.nm (s.nr 89+v) =
        if s.nr 89+v ∈ matchingContractionMaskAddresses s then 1 else 0 := by
      have repEnd := layout.representativeEnd
      have high := layout.tablesBeforeRows
      have arrays := layout.rowsBeforeFresh
      have endAt := layout.freshBeforeMask
      change reps.nm _ = _
      rw [repNat _ (.inr (by rw [cFrame 57 (by decide),c56]; omega)) (.inr (by rw [cFrame 88 (by decide)]; omega))]
      exact marker _ inside
    have absorbs : t.nr 87 = (absorbedMatchingOuterRows s).length := retainCount.trans (rowCount.trans (congrArg List.length rowModel))
    have promotes : t.nr 99 = (contractionFreshOriginalsBefore s).length :=
      (lastKeeps 99).trans ((forestKeeps 99 (by decide)).trans (freshCount.trans (congrArg List.length freshModel)))
    refine ⟨?_,absorbs, promotes, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have cursor : t.nr 68 = cycle.nr 68 :=
        (lastKeeps 68).trans ((forestKeeps 68 (by decide)).trans ((repKeeps 68 (by decide)).trans
          ((rowKeeps 68 (by decide)).trans (maskKeeps 68 (by decide)))))
      have nextNode : t.nr 76 = s.nr 76+1 := installCount.trans (congrArg (·+1)
        ((forestKeeps 76 (by decide)).trans (dFrame 76 (by decide))))
      have topNode : t.nm (s.nr 74+s.nr 12) = s.nr 76 := by
        rw [installNat,forestKeeps 74 (by decide),forestKeeps 12 (by decide),
          dFrame 74 (by decide),dFrame 12 (by decide),Function.update_self]
        exact (forestKeeps 76 (by decide)).trans (dFrame 76 (by decide))
      refine ⟨s,cycle,cycleTicks,entry,running,one,rfl,fun _ _ => rfl,cycleRun,cursor,nextNode,topNode,
        installReal.trans (forestReal.trans (repReal.trans (rowReal.trans (maskReal.trans cycleReal)))),?_⟩
      intro addr nodeEnd parentEnd repEnd scratch
      change t.nm addr = a.nm addr
      have afterRole : s.nr 51+s.nr 55 ≤ addr := (layout.roleEnd.trans (Nat.le_add_right _ _)).trans repEnd
      have noNode : addr ≠ e.nr 74+e.nr 12 := by
        rw [forestKeeps 74 (by decide),forestKeeps 12 (by decide),dFrame 74 (by decide),dFrame 12 (by decide)]
        have h := layout.baseValid
        omega
      rw [installNat,Function.update_of_ne noNode]
      change forest.nm addr = a.nm addr
      rw [forestNat,contractedMatchingForestMemory_unchanged d _ addr
        (.inr (by rwa [dFrame 51 (by decide),dFrame 55 (by decide)]))
        (.inr (by rwa [dFrame 52 (by decide),dFrame 55 (by decide)]))
        (.inr (by rwa [dFrame 74 (by decide),dFrame 55 (by decide)]))]
      have rowsBound := layout.rowsBeforeFresh
      have freshEnd := layout.freshBeforeMask
      have rowCountBound : rows.nr 87 ≤ s.nr 55 := rowBound
      change reps.nm addr = a.nm addr
      rw [repNat addr (.inr (by rwa [cFrame 57 (by decide),c56]))
        (by rw [cFrame 88 (by decide)]; omega)]
      change rows.nm addr = a.nm addr
      rw [rowNat addr (by rw [bFrame 86 (by decide)]; omega)]
      rcases scratch with early | high
      · exact markEarlier addr (by rw [a85]; omega)
      · have noMask : addr ∉ matchingContractionMaskAddresses s := by
          simp only [matchingContractionMaskAddresses,List.cons_append,List.mem_cons,List.mem_append,List.mem_map,List.mem_range]
          rintro (atBase | ⟨j,hj,eq⟩ | ⟨j,hj,eq⟩)
          · have h := layout.baseValid; omega
          · have h := layout.leftValid j hj; omega
          · have h := layout.rightValid j hj; omega
        have noClear : addr ∉ cycleMaskScanAddresses false a (a.nr 55) := by
          intro member
          obtain ⟨j,hj,eq⟩ := List.mem_map.mp member
          have hj' := List.mem_range.mp hj
          rw [cycleKeeps 55 (by decide)] at hj'
          simp only [cycleMaskAddress,Bool.false_eq_true,if_false,a85] at eq
          omega
        exact (maskNat addr).trans (by simp only [marks,if_neg noMask,if_neg noClear])
    · intro j inside
      change j < t.nr 87 at inside
      change t.nm (t.nr 86+j) = _
      have tBase : t.nr 86 = s.nr 86 := runKeeps 86
      rw [tBase, later _ (by omega)]
      have high : c.nr 57 + c.nr 55 ≤ s.nr 86+j := by
        rw [cFrame 57 (by decide), c56]
        have repEnd := layout.representativeEnd
        have tables := layout.tablesBeforeRows
        omega
      have low : s.nr 86+j < c.nr 88 := by
        rw [cFrame 88 (by decide)]
        have ends := layout.rowsBeforeFresh
        have count : t.nr 87 ≤ s.nr 55 := retainCount.trans_le rowBound
        omega
      change reps.nm _ = _
      rw [repNat _ (.inr high) (.inl low), ← rowModel]
      have within : j < (absorbedMatchingOuterRows b).length := by rwa [retainCount, rowCount] at inside
      simpa only [bFrame 86 (by decide)] using rowCells j within
    · intro j inside
      change j < t.nr 99 at inside
      change t.nm (t.nr 88+j) = _
      have tBase : t.nr 88 = s.nr 88 := runKeeps 88
      have starts := layout.rowsBeforeFresh
      rw [tBase, later _ (by omega), ← freshModel]
      have within : j < (contractedOriginalsNewlyOuter c (c.nr 55)).length := by
        rwa [promotes, ← freshModel] at inside
      change reps.nm _ = _
      simpa only [cFrame 88 (by decide)] using freshCells j within

    · intro addr pastRep pastParent belowNode belowStart belowCount belowRows
      have role := layout.roleEnd
      have firstFree := layout.rowsBeforeFresh
      have node : addr ≠ e.nr 74 + e.nr 12 := by
        rw [forestKeeps 74 (by decide), dFrame 74 (by decide),forestKeeps 12 (by decide),dFrame 12 (by decide)]
        have baseValid := layout.baseValid
        omega
      change t.nm addr = s.nm addr
      rw [installNat, Function.update_of_ne node]
      change forest.nm addr = s.nm addr
      rw [forestNat, contractedMatchingForestMemory_unchanged d _ addr
        (.inr (by rw [dFrame 51 (by decide),dFrame 55 (by decide)]; omega))
        (.inr (by rwa [dFrame 52 (by decide),dFrame 55 (by decide)]))
        (by rwa [dFrame 74 (by decide),dFrame 55 (by decide)])]
      change reps.nm addr = _
      rw [repNat addr (.inr (by rwa [cFrame 57 (by decide),c56])) (.inl (by rw [cFrame 88 (by decide)]; omega))]
      change rows.nm addr = _
      rw [rowNat addr (.inl (by rwa [bFrame 86 (by decide)]))]
      exact (markEarlier addr (by omega)).trans (earlyCycle addr (by omega) (by omega) (by omega))
    · intro addr _ belowDual
      exact (congrFun (installReal.trans (forestReal.trans (repReal.trans (rowReal.trans (maskReal.trans cycleReal))))) addr).trans
        (Function.update_of_ne (by omega : addr ≠ s.nr 75+s.nr 76) _ _)
    · intro parentEnds nodeAfter j inside
      change t.nm (s.nr 57+j) = _
      have role := layout.roleEnd
      have noNode : s.nr 57+j ≠ e.nr 74 + e.nr 12 := by
        rw [forestKeeps 74 (by decide), dFrame 74 (by decide)]
        omega
      rw [installNat, Function.update_of_ne noNode]
      change forest.nm _ = _
      rw [forestNat, contractedMatchingForestMemory_unchanged d _ _
        (.inr (by rw [dFrame 51 (by decide),dFrame 55 (by decide)]; omega))
        (.inr (by rw [dFrame 52 (by decide),dFrame 55 (by decide)]; omega))
        (.inl (by rw [dFrame 74 (by decide)]; omega))]
      have r := repCells j (c56.symm ▸ inside)
      have same : originalTopRepresentative c j = originalTopRepresentative s j := by
        simp only [originalTopRepresentative, cFrame 57 (by decide)]
        exact cPre _ (by have endRep := layout.representativeEnd; omega)
      have repValid := layout.representativeValid j inside
      change reps.nm _ = _
      rw [cFrame 57 (by decide), same, cFrame 12 (by decide)] at r
      have actual : wasContractedRepresentative c (originalTopRepresentative s j) ↔
          s.nr 89+originalTopRepresentative s j ∈ matchingContractionMaskAddresses s := by
        change 0 < c.nm (c.nr 89+originalTopRepresentative s j) ↔ _
        rw [cFrame 89 (by decide),marker _ repValid]
        split <;> simp_all
      by_cases member : s.nr 89+originalTopRepresentative s j ∈ matchingContractionMaskAddresses s
      · simpa only [if_pos member,if_pos (actual.mpr member)] using r
      · simpa only [if_neg member,if_neg (actual.not.mpr member)] using r

    · intro repEnd parentEnd pointers counts j hj
      have id : e.nr 76 = s.nr 76 := (forestKeeps 76 (by decide)).trans (dFrame 76 (by decide))
      have entryNode : e.nr 74 = s.nr 74 := (forestKeeps 74 (by decide)).trans (dFrame 74 (by decide))
      have base : e.nr 12 = s.nr 12 := (forestKeeps 12 (by decide)).trans (dFrame 12 (by decide))
      change t.nm _ = _
      rw [installNat,entryNode,base,id]
      by_cases same : j = s.nr 12
      · simp [same]
      · rw [if_neg same,Function.update_of_ne (by omega : s.nr 74+j ≠ s.nr 74+s.nr 12)]
        change forest.nm _ = _
        rw [forestNat,dFrame 55 (by decide)]
        have role := layout.roleEnd
        have rowsEnd := layout.rowsBeforeFresh
        have freshEnd := layout.freshBeforeMask
        have markEnd := layout.maskBeforeRecords
        have raw := contractedMatchingForestMemory_nodes (s := d) (k := s.nr 55)
          (by rw [dFrame 51 (by decide), dFrame 74 (by decide)]; omega)
          (by rwa [dFrame 52 (by decide),dFrame 74 (by decide)])
          (by rw [dFrame 74 (by decide),dFrame 89 (by decide)]; omega) (⟨j,hj⟩ : Fin (s.nr 55))
        have original : d.nm (s.nr 74+j) = s.nm (s.nr 74+j) := by
          change reps.nm _ = _
          rw [repNat _ (.inr (by rw [cFrame 57 (by decide),c56]; omega)) (.inl (by rw [cFrame 88 (by decide)]; omega))]
          change rows.nm _ = _
          rw [rowNat _ (.inl (by rw [bFrame 86 (by decide)]; omega))]
          exact (markEarlier _ (by rw [a85]; omega)).trans (earlyCycle _ (by omega) (by omega) (by omega))
        have flag : wasContractedRepresentative d j ↔ s.nr 89+j ∈ matchingContractionMaskAddresses s := by
          change 0 < d.nm (d.nr 89+j) ↔ _
          rw [dFrame 89 (by decide),dMask j hj]
          split <;> simp_all
        by_cases hit : s.nr 89+j ∈ matchingContractionMaskAddresses s
        · simpa only [dFrame 74 (by decide),dFrame 12 (by decide),if_pos hit,
            if_pos (show wasContractedRepresentative d j ∧ j ≠ s.nr 12 from ⟨flag.mpr hit,same⟩)] using raw
        · have outside : ¬(wasContractedRepresentative d j ∧ j ≠ s.nr 12) := fun h => hit (flag.mp h.1)
          simpa only [dFrame 74 (by decide),dFrame 12 (by decide),if_neg hit,if_neg outside,original] using raw
    · intro j hj
      have low := layout.rowsBeforeFresh
      have high := layout.freshBeforeMask
      change t.nm _ = _
      rw [later _ (by omega)]
      exact dMask j hj
    · intro k size parent depth beforeRep beforeNode old base cycle baseAt encoded cycleMarks
      have roleEnd := layout.roleEnd
      have repEnd := layout.representativeEnd
      have markAfter := layout.freshBeforeMask
      have rowsStart := layout.tablesBeforeRows
      have rowsEnd := layout.rowsBeforeFresh
      have beforeForest (addr : ℕ) (low : addr < s.nr 57) : d.nm addr = s.nm addr := by
        have beforeRepresentatives : addr < c.nr 57 := by rwa [cFrame 57 (by decide)]
        have beforeFreshRows : addr < c.nr 88 :=
          beforeRepresentatives.trans_le ((Nat.le_add_right (c.nr 57) (c.nr 55)).trans cFresh)
        have beforeSelector : addr < s.nr 58 :=
          low.trans_le ((Nat.le_add_right (s.nr 57) (s.nr 55)).trans repEnd)
        exact (repNat addr (.inl beforeRepresentatives) (.inl beforeFreshRows)).trans
          (cPre addr beforeSelector)
      have dLayout : MatchingContractForestLayout d k := by
        refine ⟨(dFrame 55 (by decide)).trans size, ?_, ?_, ?_, ?_⟩
        · rwa [dFrame 52 (by decide), dFrame 51 (by decide)]
        · rwa [dFrame 53 (by decide), dFrame 51 (by decide)]
        · rw [dFrame 53 (by decide), dFrame 74 (by decide)]
          omega
        · rw [dFrame 74 (by decide), dFrame 89 (by decide)]
          omega
      have dForest : AlternatingForestMemory old (d.nr 51) d.nm := by
        intro v
        have vLt := v.isLt
        simp only [dFrame 51 (by decide), beforeForest _ (show s.nr 51+v.val < s.nr 57 by omega),
          beforeForest _ (show s.nr 51+k+v.val < s.nr 57 by omega),
          beforeForest _ (show s.nr 51+k+k+v.val < s.nr 57 by omega)]
        exact encoded v
      have dMarks (v : Fin k) : wasContractedRepresentative d v.val ↔ v ∈ cycle := by
        change 0 < reps.nm (d.nr 89+v.val) ↔ _
        have vLt : v.val < s.nr 55 := size.symm ▸ v.isLt
        rw [dFrame 89 (by decide)]
        change 0 < d.nm (s.nr 89+v.val) ↔ _
        rw [dMask _ vLt]
        by_cases member : v ∈ cycle <;> simp [cycleMarks v, member]
      have model := contractedMatchingForestMemory_encodes dLayout dForest cycle base
        ((dFrame 12 (by decide)).trans baseAt) dMarks
      have keep (addr : ℕ) (low : addr < s.nr 74) : t.nm addr = contractedMatchingForestMemory d k addr := by
        have outside : addr ≠ e.nr 74 + e.nr 12 := by rw [forestKeeps 74 (by decide), dFrame 74 (by decide)]; omega
        rw [installNat, Function.update_of_ne outside]
        change forest.nm addr = _
        rw [forestNat, dLayout.size]
      intro v
      have vLt := v.isLt
      have actual := model v
      rw [dFrame 51 (by decide)] at actual
      change t.nm _ = _ ∧ t.nm _ = _ ∧ t.nm _ = _
      rw [keep _ (by omega),keep _ (by omega),keep _ (by omega)]
      exact actual









end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractHandler

open VehicleRoutingSurvey.Routing SupplyChainTheory in
theorem solution : (fun {P : Prop} (_ : P) => P) (@VehicleRoutingSurvey.Routing.finishMatchingContractionStructure_spec) :=
  @VehicleRoutingSurvey.Routing.finishMatchingContractionStructure_spec
