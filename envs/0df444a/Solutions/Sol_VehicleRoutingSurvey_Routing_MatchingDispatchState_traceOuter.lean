-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.MatchingDispatchState.traceOuter
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T16:16:30.896941+00:00
-- url     : https://prove2.me/submissions/d8a1b5b0-39f3-4b07-bb24-6ec85afd8a7c

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_ContractionArm
import Batteries.Tactic.OpenPrivate

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









































end VehicleRoutingSurvey.Routing
end RppSource_WeightedReadDeltaRAM

/-! matching/AlternatingForestTrace.lean -/
section RppSource_AlternatingForestTrace
namespace VehicleRoutingSurvey.Routing









private theorem AlternatingForestState.traceParents_spec {α : Type*}
    {state : AlternatingForestState α} {mate : α → Option α} {tight : α → α → Prop}
    (valid : state.valid mate tight) {x : α} (marked : state.role x ≠ .unlabelled)
    {fuel : ℕ} (enough : state.depth x < fuel) :
    let trail := state.traceParents fuel x
    trail.head? = some x ∧ trail.Nodup ∧
      trail.IsChain (fun child p => (state.role child).parent = some p ∧ tight p child) ∧
      (∃ root, trail.getLast? = some root ∧ state.role root = .outer none ∧ mate root = none) ∧
      ∀ v ∈ trail, state.depth v ≤ state.depth x := by
  induction fuel generalizing x with
  | zero => omega
  | succ fuel ih =>
    have parentValid := AlternatingForestState.parent_valid valid marked
    cases parent : (state.role x).parent with
    | none =>
      try rw [parent] at parentValid
      dsimp only [traceParents]
      rw [parent]
      exact ⟨rfl, by simp, List.IsChain.singleton _,
        ⟨x, rfl, parentValid.1, parentValid.2⟩, by simp⟩
    | some p =>
      try rw [parent] at parentValid
      obtain ⟨pMarked, smaller, edge⟩ := parentValid
      have pEnough : state.depth p < fuel := by omega
      obtain ⟨headAt, distinct, chain, ⟨root, atEnd, rootRole, exposed⟩, bound⟩ := ih pMarked pEnough
      obtain ⟨rest, pFirst⟩ := List.head?_eq_some_iff.mp headAt
      have newDistinct : x ∉ state.traceParents fuel p := by
        intro present
        exact (not_le_of_gt smaller) (bound x present)
      dsimp only [traceParents]
      rw [parent]
      dsimp only
      refine ⟨rfl, List.nodup_cons.mpr ⟨newDistinct, distinct⟩, ?_, ⟨root, ?_, rootRole, exposed⟩, ?_⟩
      · rw [pFirst, List.isChain_cons_cons]
        exact ⟨⟨parent, edge⟩, by simpa only [pFirst] using chain⟩
      · simpa only [pFirst, List.getLast?_cons_cons] using atEnd
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | earlier
        · exact le_rfl
        · exact (bound v earlier).trans smaller.le

theorem AlternatingForestState.traceToRoot_spec {α : Type*} [Fintype α]
    {state : AlternatingForestState α} {mate : α → Option α} {tight : α → α → Prop}
    (valid : state.valid mate tight) {x : α} (marked : state.role x ≠ .unlabelled) :
    let trail := state.traceToRoot x
    trail.head? = some x ∧ trail.Nodup ∧ trail.length ≤ Fintype.card α ∧
      trail.IsChain (fun child p => (state.role child).parent = some p ∧ tight p child) ∧
      ∃ root, trail.getLast? = some root ∧ state.role root = .outer none ∧ mate root = none := by
  obtain ⟨headAt, distinct, chain, root, _⟩ :=
    AlternatingForestState.traceParents_spec valid marked (Nat.lt_succ_self _)
  exact ⟨headAt, distinct, distinct.length_le_card, chain, root⟩

end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestTrace

/-! matching/AlternatingForestAncestor.lean -/
section RppSource_AlternatingForestAncestor
namespace VehicleRoutingSurvey.Routing



private theorem markForestTrace_true {α : Type*} [DecidableEq α] {trace : List α} {v : α} :
    markForestTrace trace v = true ↔ v ∈ trace := by
  have marked (table : α → Bool) (xs : List α) :
      xs.foldl (fun cells x => Function.update cells x true) table v = true ↔
        table v = true ∨ v ∈ xs := by
    induction xs generalizing table with
    | nil => simp
    | cons head tail ih =>
      simp only [List.foldl_cons, ih, Function.update_apply, List.mem_cons]
      by_cases equal : v = head <;> simp [equal]
  simpa only [markForestTrace, Bool.false_eq_true, false_or] using marked (fun _ => false) trace



theorem firstSharedAncestor_eq_some_iff {α : Type*} [DecidableEq α]
    {left right : List α} {ancestor : α} : firstSharedAncestor left right = some ancestor ↔
    ancestor ∈ left ∧ ∃ before after, right = before ++ (ancestor :: after) ∧
      ∀ v ∈ before, v ∉ left := by
  rw [firstSharedAncestor, List.find?_eq_some_iff_append]
  have notMarked (v : α) : (!(markForestTrace left v)) = true ↔ v ∉ left := by
    rw [← markForestTrace_true]
    cases markForestTrace left v <;> decide
  simp only [markForestTrace_true, notMarked]

theorem firstSharedAncestor_eq_none_iff {α : Type*} [DecidableEq α] {left right : List α} :
    firstSharedAncestor left right = none ↔ ∀ v ∈ right, v ∉ left := by
  simp only [firstSharedAncestor, List.find?_eq_none, markForestTrace_true]





end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestAncestor

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

/-! matching/MatchingClassifyEventRAM.lean -/
section RppSource_MatchingClassifyEventRAM
namespace VehicleRoutingSurvey.Routing

def matchingEventIsCut (s : ArithmeticState) : Prop :=
  s.nr 55 ≤ (matchingOriginalGrowthEvent s).2









structure MatchingClassifiedEvent (s t : ArithmeticState) (steps : ℕ) : Prop where
  run : BlockRuns classifyMatchingSelectedEvent steps s t
  running : t.halted = false
  tag : t.nr 35 = matchingEventClass s
  identifier : t.nr 91 = s.nr 1
  endpoints : (t.nr 92, t.nr 93) = matchingOriginalGrowthEvent s
  edgeRepresentatives : ¬matchingEventIsCut s → t.nr 0 = matchingEventLeftRep s ∧ t.nr 2 = matchingEventRightRep s
  natural : t.nm = s.nm
  real : t.rm = s.rm
  realRegisters : t.rr = s.rr
  registers : ∀ r, r ∉ [0, 2, 6, 10, 11, 14, 35, 91, 92, 93] → t.nr r = s.nr r

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1400000 in
theorem classifyMatchingSelectedEvent_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t steps, steps ≤ 21 ∧ MatchingClassifiedEvent s t steps := by
  have pack {t : ArithmeticState} {steps : ℕ}
      (cost : steps ≤ 21) (run : BlockRuns classifyMatchingSelectedEvent steps s t)
      (live : t.halted = false) (tag : t.nr 35 = matchingEventClass s) (identifier : t.nr 91 = s.nr 1)
      (endpoints : (t.nr 92, t.nr 93) = matchingOriginalGrowthEvent s)
      (reps : ¬matchingEventIsCut s → t.nr 0 = matchingEventLeftRep s ∧ t.nr 2 = matchingEventRightRep s)
      (native : t.nm = s.nm) (real : t.rm = s.rm) (rr : t.rr = s.rr) :
      ∃ t steps, steps ≤ 21 ∧ MatchingClassifiedEvent s t steps := by
    refine ⟨t, steps, cost, run, live, tag, identifier, endpoints, reps, native, real, rr, ?_⟩
    intro r away
    rw [← run.run]
    apply arithmeticRun_keeps_register _ s steps
    simp [classifyMatchingSelectedEvent, naturalDestination] at away ⊢ <;> omega
  by_cases cut : s.nr 55 ≤ s.nm (s.nr 54 + ((s.nr 1 - 1) + (s.nr 1 - 1)) + 1)
  · let t := (arithmeticStep classifyMatchingSelectedEvent)^[11] s
    have out : t.pc = classifyMatchingSelectedEvent.length ∧ t.halted = false ∧
        t.nr 35 = matchingEventClass s ∧ t.nr 91 = s.nr 1 ∧ (t.nr 92, t.nr 93) = matchingOriginalGrowthEvent s ∧
        t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
      simp [t, classifyMatchingSelectedEvent, arithmeticStep, entry, running, one, Function.iterate_succ_apply',
        matchingEventClass, matchingOriginalGrowthEvent, cut]
    obtain ⟨exit, live, tag, id, edge, nat, real, rr⟩ := out
    refine pack (steps := 11) (by decide) (BlockRuns.of_running_exit rfl live exit) live tag id edge ?_ nat real rr
    intro impossible
    exact (impossible (by simpa [matchingEventIsCut, matchingOriginalGrowthEvent] using cut)).elim
  by_cases leftIdle : s.nm (s.nr 51 + matchingEventLeftRep s) = 0
  · have leftRaw := leftIdle
    dsimp [matchingEventLeftRep, matchingOriginalGrowthEvent] at leftRaw
    let t := (arithmeticStep classifyMatchingSelectedEvent)^[20] s
    have out : t.pc = classifyMatchingSelectedEvent.length ∧ t.halted = false ∧
        t.nr 35 = matchingEventClass s ∧ t.nr 91 = s.nr 1 ∧ (t.nr 92, t.nr 93) = matchingOriginalGrowthEvent s ∧
        (t.nr 0 = matchingEventLeftRep s ∧ t.nr 2 = matchingEventRightRep s) ∧
        t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
      simp [t, classifyMatchingSelectedEvent, arithmeticStep, entry, running, one, Function.iterate_succ_apply',
        matchingEventClass, matchingEventLeftRep, matchingEventRightRep, matchingOriginalGrowthEvent, cut, leftRaw]
    obtain ⟨exit, live, tag, id, edge, reps, nat, real, rr⟩ := out
    exact pack (steps := 20) (by decide) (BlockRuns.of_running_exit rfl live exit) live tag id edge (fun _ => reps) nat real rr
  · have leftRaw := leftIdle
    dsimp [matchingEventLeftRep, matchingOriginalGrowthEvent] at leftRaw
    by_cases rightIdle : s.nm (s.nr 51 + matchingEventRightRep s) = 0
    · have rightRaw := rightIdle
      dsimp [matchingEventRightRep, matchingOriginalGrowthEvent] at rightRaw
      let t := (arithmeticStep classifyMatchingSelectedEvent)^[21] s
      have out : t.pc = classifyMatchingSelectedEvent.length ∧ t.halted = false ∧
          t.nr 35 = matchingEventClass s ∧ t.nr 91 = s.nr 1 ∧ (t.nr 92, t.nr 93) = matchingOriginalGrowthEvent s ∧
          (t.nr 0 = matchingEventLeftRep s ∧ t.nr 2 = matchingEventRightRep s) ∧
          t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
        simp [t, classifyMatchingSelectedEvent, arithmeticStep, entry, running, one, Function.iterate_succ_apply',
          matchingEventClass, matchingEventLeftRep, matchingEventRightRep, matchingOriginalGrowthEvent, cut, leftRaw, rightRaw]
      obtain ⟨exit, live, tag, id, edge, reps, nat, real, rr⟩ := out
      exact pack (steps := 21) le_rfl (BlockRuns.of_running_exit rfl live exit) live tag id edge (fun _ => reps) nat real rr
    · have rightRaw := rightIdle
      dsimp [matchingEventRightRep, matchingOriginalGrowthEvent] at rightRaw
      let t := (arithmeticStep classifyMatchingSelectedEvent)^[21] s
      have out : t.pc = classifyMatchingSelectedEvent.length ∧ t.halted = false ∧
          t.nr 35 = matchingEventClass s ∧ t.nr 91 = s.nr 1 ∧ (t.nr 92, t.nr 93) = matchingOriginalGrowthEvent s ∧
          (t.nr 0 = matchingEventLeftRep s ∧ t.nr 2 = matchingEventRightRep s) ∧
          t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
        simp [t, classifyMatchingSelectedEvent, arithmeticStep, entry, running, one, Function.iterate_succ_apply',
          matchingEventClass, matchingEventLeftRep, matchingEventRightRep, matchingOriginalGrowthEvent, cut, leftRaw, rightRaw]
      obtain ⟨exit, live, tag, id, edge, reps, nat, real, rr⟩ := out
      exact pack (steps := 21) le_rfl (BlockRuns.of_running_exit rfl live exit) live tag id edge (fun _ => reps) nat real rr

end VehicleRoutingSurvey.Routing
end RppSource_MatchingClassifyEventRAM

/-! matching/AlternatingForestTraceRAM.lean -/
section RppSource_AlternatingForestTraceRAM
namespace VehicleRoutingSurvey.Routing



private def traceHeadCode {k : ℕ} (trail : List (Fin k)) : ℕ :=
  (trail.head?.map Fin.val).getD k

/-- `k` is the end marker. Every other parent code is a compact vertex. -/
def ForestParentChain {k : ℕ} (parent : Fin k → ℕ) : List (Fin k) → Prop
  | [] => True
  | x :: tail => parent x = traceHeadCode tail ∧ ForestParentChain parent tail



private def forestTraceAfterOne (s : ArithmeticState) : ArithmeticState :=
  let address := s.nr 52 + s.nr 2
  {s with
    pc := 0
    nr := Function.update (Function.update (Function.update s.nr 5 address)
      2 (s.nm address)) 4 (s.nr 4 + s.nr 6)
    nm := Function.update s.nm (s.nr 3 + s.nr 4) (s.nr 2)}

private theorem forestTraceAfterOne_exec {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (live : s.nr 2 < s.nr 55)
    (disjoint : s.nr 52 + s.nr 2 ≠ s.nr 3 + s.nr 4) :
    (arithmeticStep traceForestParentLoop)^[7] s = forestTraceAfterOne s := by
  simp [forestTraceAfterOne, traceForestParentLoop, arithmeticStep, entry, running,
    Function.iterate_succ_apply', not_le.mpr live, Function.update_of_ne disjoint]

private theorem forestTraceAfterOne_register {s : ArithmeticState} (r : ℕ)
    (cursor : r ≠ 2) (count : r ≠ 4) (scratch : r ≠ 5) :
    (forestTraceAfterOne s).nr r = s.nr r := by
  simp [forestTraceAfterOne, Function.update_of_ne cursor, Function.update_of_ne count,
    Function.update_of_ne scratch]

/-- Trace a parent chain with one output word per vertex. The loop stops
at the root's parent sentinel. It writes exactly the occupied output slice. -/
theorem traceForestParentLoop_correct {k : ℕ} {parent : Fin k → ℕ}
    (trail : List (Fin k)) (chain : ForestParentChain parent trail) {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (dimension : s.nr 55 = k)
    (one : s.nr 6 = 1) (cursor : s.nr 2 = traceHeadCode trail)
    (parents : ∀ v : Fin k, s.nm (s.nr 52 + v.val) = parent v)
    (separate : s.nr 52 + k ≤ s.nr 3) :
    ∃ t, BlockRuns traceForestParentLoop (7 * trail.length + 1) s t ∧
      t.halted = false ∧ t.nr 2 = k ∧ t.nr 4 = s.nr 4 + trail.length ∧
      ForestTraceArray t.nm (s.nr 3 + s.nr 4) trail ∧
      (∀ address, address < s.nr 3 + s.nr 4 ∨
        s.nr 3 + s.nr 4 + trail.length ≤ address → t.nm address = s.nm address) ∧
      (∀ r, r ≠ 2 → r ≠ 4 → r ≠ 5 → t.nr r = s.nr r) ∧
      t.rr = s.rr ∧ t.rm = s.rm := by
  induction trail generalizing s with
  | nil =>
    let t := {s with pc := 7}
    have done : s.nr 55 ≤ s.nr 2 := by rw [dimension, cursor]; rfl
    have runs : BlockRuns traceForestParentLoop 1 s t := by
      apply BlockRuns.of_running_exit
      · simp [t, traceForestParentLoop, arithmeticStep, entry, running, done]
      · exact running
      · rfl
    refine ⟨t, runs, running, cursor, by simp [t], ?_, fun _ _ => rfl,
      fun _ _ _ _ => rfl, rfl, rfl⟩
    intro _ impossible
    simp at impossible
  | cons x tail ih =>
    have xCode : s.nr 2 = x.val := cursor
    have live : s.nr 2 < s.nr 55 := by rw [xCode, dimension]; exact x.isLt
    have disjoint : s.nr 52 + s.nr 2 ≠ s.nr 3 + s.nr 4 := by omega
    let u := forestTraceAfterOne s
    have fixed := forestTraceAfterOne_register (s := s)
    have base : u.nr 3 = s.nr 3 := fixed 3 (by decide) (by decide) (by decide)
    have table : u.nr 52 = s.nr 52 := fixed 52 (by decide) (by decide) (by decide)
    have counter : u.nr 4 = s.nr 4 + 1 := by simp [u, forestTraceAfterOne, one]
    have next : u.nr 2 = traceHeadCode tail := by
      simpa [u, forestTraceAfterOne, xCode, parents x] using chain.1
    have retained (address : ℕ) (different : address ≠ s.nr 3 + s.nr 4) :
        u.nm address = s.nm address := by
      simp [u, forestTraceAfterOne, Function.update_of_ne different]
    have stillParents (v : Fin k) : u.nm (u.nr 52 + v.val) = parent v := by
      rw [table, retained _ (by have := v.isLt; omega), parents v]
    obtain ⟨t, runs, ready, ended, written, array, footprint, preserved, reals, realMemory⟩ :=
      ih chain.2 (s := u) rfl running ((fixed 55 (by decide) (by decide) (by decide)).trans dimension)
        ((fixed 6 (by decide) (by decide) (by decide)).trans one) next stillParents
        (by rwa [table, base])
    have doIt : BlockRuns traceForestParentLoop (7 * (x :: tail).length + 1) s t := by
      apply BlockRuns.of_running_exit
      · rw [show 7 * (x :: tail).length + 1 = (7 * tail.length + 1) + 7 by
          simp only [List.length_cons, Nat.mul_add, Nat.mul_one] <;> omega]
        rw [Function.iterate_add_apply, forestTraceAfterOne_exec entry running live disjoint]
        exact runs.run
      · exact ready
      · exact runs.exit
    refine ⟨t, doIt, ready, ended, by rw [written, counter, List.length_cons]; omega,
      ?_, ?_, ?_, reals, realMemory⟩
    · intro i within
      cases i with
      | zero =>
        rw [Nat.add_zero, footprint _ (.inl (by rw [base, counter]; omega))]
        simp [u, forestTraceAfterOne, xCode]
      | succ i =>
        have inTail : i < tail.length := by simpa using within
        have address : s.nr 3 + s.nr 4 + (i + 1) = u.nr 3 + u.nr 4 + i := by
          rw [base, counter]; omega
        simpa only [List.getElem_cons_succ, address] using array i inTail
    · intro address outside
      have noStore : address ≠ s.nr 3 + s.nr 4 := by
        simp only [List.length_cons] at outside
        omega
      have untouched : address < u.nr 3 + u.nr 4 ∨
          u.nr 3 + u.nr 4 + tail.length ≤ address := by
        rw [base, counter]
        simp only [List.length_cons] at outside
        omega
      exact (footprint address untouched).trans (retained address noStore)
    · intro r notCursor notCount notScratch
      exact (preserved r notCursor notCount notScratch).trans (fixed r notCursor notCount notScratch)

private theorem forestParentChain_of_root {k : ℕ} {forest : AlternatingForestState (Fin k)}
    (trail : List (Fin k)) {root : Fin k}
    (chain : trail.IsChain (fun child p => (forest.role child).parent = some p))
    (atEnd : trail.getLast? = some root) (endParent : (forest.role root).parent = none) :
    ForestParentChain (fun v => ((forest.role v).parent.map Fin.val).getD k) trail := by
  induction trail with
  | nil => trivial
  | cons x tail ih =>
    cases tail with
    | nil =>
      have equal : x = root := by simpa using atEnd
      simp [ForestParentChain, traceHeadCode, equal, endParent]
    | cons y rest =>
      rw [List.isChain_cons_cons] at chain
      exact ⟨by simp [traceHeadCode, chain.1], ih chain.2 (by simpa using atEnd)⟩

theorem AlternatingForestState.traceToRoot_parentChain {k : ℕ}
    {forest : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)}
    {tight : Fin k → Fin k → Prop} (valid : forest.valid mate tight) {x : Fin k}
    (marked : forest.role x ≠ .unlabelled) :
    ForestParentChain (fun v => ((forest.role v).parent.map Fin.val).getD k) (forest.traceToRoot x) := by
  obtain ⟨_, _, _, linked, root, endAt, rootRole, _⟩ := AlternatingForestState.traceToRoot_spec valid marked
  exact forestParentChain_of_root _ (linked.imp (fun _ _ h => h.1)) endAt
    (by simp [rootRole, AlternatingForestRole.parent])

theorem AlternatingForestMemory.parentCode {k : ℕ} {forest : AlternatingForestState (Fin k)}
    {base : ℕ} {memory : ℕ → ℕ} (encoding : AlternatingForestMemory forest base memory)
    (v : Fin k) : memory (base + k + v.val) = ((forest.role v).parent.map Fin.val).getD k := by
  have atParent := (encoding v).2.1
  cases role : forest.role v with
  | unlabelled => rw [role] at atParent; exact atParent
  | outer p =>
    rw [role] at atParent
    cases p <;> exact atParent
  | inner p => rw [role] at atParent; exact atParent

/-- Concrete parent tracing for the previously verified alternating-forest memory layout. -/
theorem traceForestParentLoop_traceToRoot {k : ℕ} {forest : AlternatingForestState (Fin k)}
    {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop} {x : Fin k}
    {base : ℕ} {s : ArithmeticState} (valid : forest.valid mate tight)
    (marked : forest.role x ≠ .unlabelled) (encoded : AlternatingForestMemory forest base s.nm)
    (entry : s.pc = 0) (running : s.halted = false) (dimension : s.nr 55 = k)
    (one : s.nr 6 = 1) (source : s.nr 2 = x.val) (table : s.nr 52 = base + k)
    (separate : s.nr 52 + k ≤ s.nr 3) :
    let trail := forest.traceToRoot x
    ∃ (t : ArithmeticState) (steps : ℕ), BlockRuns traceForestParentLoop steps s t ∧
      steps ≤ 7 * k + 1 ∧ t.halted = false ∧ t.nr 2 = k ∧ t.nr 4 = s.nr 4 + trail.length ∧
      ForestTraceArray t.nm (s.nr 3 + s.nr 4) trail ∧
      (∀ address, address < s.nr 3 + s.nr 4 ∨
        s.nr 3 + s.nr 4 + trail.length ≤ address → t.nm address = s.nm address) ∧
      (∀ r, r ≠ 2 → r ≠ 4 → r ≠ 5 → t.nr r = s.nr r) ∧
      t.rr = s.rr ∧ t.rm = s.rm := by
  intro trail
  obtain ⟨headAt, _, bounded, _, _⟩ := AlternatingForestState.traceToRoot_spec valid marked
  have limit : trail.length ≤ k := by simpa [trail] using bounded
  have starts : s.nr 2 = traceHeadCode trail := by simp [traceHeadCode, trail, source, headAt]
  have reads (v : Fin k) : s.nm (s.nr 52 + v.val) = ((forest.role v).parent.map Fin.val).getD k := by
    rw [table]
    exact encoded.parentCode v
  obtain ⟨t, ran, properties⟩ := traceForestParentLoop_correct trail
    (AlternatingForestState.traceToRoot_parentChain valid marked) entry running dimension one starts reads separate
  exact ⟨t, _, ran, by omega, properties⟩

end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestTraceRAM

/-! matching/MatchingForestTraceSetup.lean -/
section RppSource_MatchingForestTraceSetup
namespace VehicleRoutingSurvey.Routing

/-- The two trace arrays and the vertex-to-left-position array have one
word per compact vertex. -/
structure MatchingForestTraceStorage (k base : ℕ) (s : ArithmeticState) : Prop where
  left : s.nr 83 = base
  right : s.nr 84 = base + k
  marks : s.nr 85 = base + k + k







private theorem startMatchingForestTraceBlock_correct (source output : ℕ)
    {s : ArithmeticState} (entry : s.pc = 0) (running : s.halted = false)
    (small : source ≤ 1) (large : 50 ≤ output) :
    ∃ t, BlockRuns (startMatchingForestTraceBlock source output) 4 s t ∧ t.halted = false ∧
      t.nr 2 = s.nr source ∧ t.nr 3 = s.nr output ∧ t.nr 4 = 0 ∧ t.nr 6 = 1 ∧
      t.nm = s.nm ∧ t.rr = s.rr ∧ t.rm = s.rm ∧
      (∀ r, r ∉ [2, 3, 4, 6] → t.nr r = s.nr r) := by
  let t := (arithmeticStep (startMatchingForestTraceBlock source output))^[4] s
  have ready : t.halted = false := by
    simp [t, startMatchingForestTraceBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  have exit : t.pc = (startMatchingForestTraceBlock source output).length := by
    simp [t, startMatchingForestTraceBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  have source4 : source ≠ 4 := by omega
  have source6 : source ≠ 6 := by omega
  have output2 : output ≠ 2 := by omega
  have output4 : output ≠ 4 := by omega
  have output6 : output ≠ 6 := by omega
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [t, startMatchingForestTraceBlock, arithmeticStep, Function.iterate_succ_apply', entry, running,
      Function.update_of_ne source4, Function.update_of_ne source6]
  · simp [t, startMatchingForestTraceBlock, arithmeticStep, Function.iterate_succ_apply', entry, running,
      Function.update_of_ne output2, Function.update_of_ne output4, Function.update_of_ne output6]
  · simp [t, startMatchingForestTraceBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  · simp [t, startMatchingForestTraceBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  · simp [t, startMatchingForestTraceBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  · simp [t, startMatchingForestTraceBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  · simp [t, startMatchingForestTraceBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  · intro r away
    apply arithmeticRun_keeps_register _ s 4
    simp [startMatchingForestTraceBlock, naturalDestination] at away ⊢
    omega



private theorem publishMatchingForestTraceCountBlock_correct (destination : ℕ) {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns (publishMatchingForestTraceCountBlock destination) 2 s t ∧ t.halted = false ∧
      t.nr destination = s.nr 4 ∧ t.nm = s.nm ∧ t.rr = s.rr ∧ t.rm = s.rm ∧
      (∀ r, r ∉ [8, destination] → t.nr r = s.nr r) := by
  let t := (arithmeticStep (publishMatchingForestTraceCountBlock destination))^[2] s
  have ready : t.halted = false := by
    simp [t, publishMatchingForestTraceCountBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  have exit : t.pc = (publishMatchingForestTraceCountBlock destination).length := by
    simp [t, publishMatchingForestTraceCountBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_, ?_⟩
  · simp [t, publishMatchingForestTraceCountBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  · simp [t, publishMatchingForestTraceCountBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  · simp [t, publishMatchingForestTraceCountBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  · simp [t, publishMatchingForestTraceCountBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  · intro r away
    apply arithmeticRun_keeps_register _ s 2
    simp [publishMatchingForestTraceCountBlock, naturalDestination] at away ⊢
    omega



theorem writeMatchingForestTraceBlock_correct {k : ℕ} {forest : AlternatingForestState (Fin k)}
    {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop} {x : Fin k}
    {base : ℕ} {s : ArithmeticState} (source output destination : ℕ) (valid : forest.valid mate tight)
    (marked : forest.role x ≠ .unlabelled) (encoded : AlternatingForestMemory forest base s.nm)
    (entry : s.pc = 0) (running : s.halted = false) (dimension : s.nr 55 = k)
    (small : source ≤ 1) (large : 50 ≤ output) (start : s.nr source = x.val)
    (parents : s.nr 52 = base + k) (separate : base + k + k ≤ s.nr output) :
    let trail := forest.traceToRoot x
    ∃ (t : ArithmeticState) (steps : ℕ),
      BlockRuns (writeMatchingForestTraceBlock source output destination) steps s t ∧
      t.halted = false ∧ steps ≤ 7 * k + 7 ∧ t.nr destination = trail.length ∧
      ForestTraceArray t.nm (s.nr output) trail ∧
      (∀ address, address < s.nr output ∨
        s.nr output + trail.length ≤ address → t.nm address = s.nm address) ∧
      (∀ r, r ∉ [2, 3, 4, 5, 6, 8, destination] → t.nr r = s.nr r) ∧
      t.rr = s.rr ∧ t.rm = s.rm ∧ (destination ≠ 6 → t.nr 6 = 1) := by
  intro trail
  obtain ⟨a, sets, aReady, initialVertex, address, zero, one, initialMem, initialRR, initialRM, initialRegs⟩ :=
    startMatchingForestTraceBlock_correct source output entry running small large
  let before := {a with pc := 0}
  have aDimension : a.nr 55 = k := (initialRegs 55 (by decide)).trans dimension
  have aParents : a.nr 52 = base + k := (initialRegs 52 (by decide)).trans parents
  have aEncoded : AlternatingForestMemory forest base before.nm := by
    change AlternatingForestMemory forest base a.nm
    rwa [initialMem]
  obtain ⟨b, traceSteps, traced, traceBound, bReady, _, count, array, footprint, fixed, traceReals, traceRM⟩ :=
    traceForestParentLoop_traceToRoot (s := before) valid marked aEncoded rfl aReady aDimension
      one (initialVertex.trans start) aParents (by change a.nr 52 + k ≤ a.nr 3; rwa [aParents, address])
  let publishEntry := {b with pc := 0}
  obtain ⟨c, copied, cReady, length, finalMem, finalRR, finalRM, finalRegs⟩ :=
    publishMatchingForestTraceCountBlock_correct destination (s := publishEntry) rfl bReady
  have all := (sets.append traced).append copied
  have countAt : b.nr 4 = trail.length := by
    rw [count]; change a.nr 4 + _ = _; simp [zero, trail]
  have writeBase : before.nr 3 + before.nr 4 = s.nr output := by
    change a.nr 3 + a.nr 4 = _
    simp [address, zero]
  have finalArray : ForestTraceArray c.nm (s.nr output) trail := by
    rw [finalMem, ← writeBase]
    exact array
  refine ⟨_, _, all, cReady, by omega, length.trans countAt, finalArray, ?_, ?_,
    finalRR.trans (traceReals.trans initialRR), finalRM.trans (traceRM.trans initialRM), ?_⟩
  · intro p outside
    have kept := footprint p (by rwa [writeBase])
    exact (congrFun finalMem p).trans (kept.trans (congrFun initialMem p))
  · intro r away
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at away
    obtain ⟨not2, not3, not4, not5, not6, not8, notDestination⟩ := away
    exact (finalRegs r (by simp [not8, notDestination])).trans
      ((fixed r not2 not4 not5).trans (initialRegs r (by simp [not2, not3, not4, not6])))
  · intro distinct
    exact (finalRegs 6 (by simp [distinct.symm])).trans
      ((fixed 6 (by decide) (by decide) (by decide)).trans one)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingForestTraceSetup

/-! matching/AlternatingForestTraceIndex.lean -/
section RppSource_AlternatingForestTraceIndex
namespace VehicleRoutingSurvey.Routing

/-- For each vertex, store its index on the left trace, or `k` if absent. -/
structure ForestTraceIndexTable {k : ℕ} (memory : ℕ → ℕ) (base : ℕ) (left : List (Fin k)) : Prop where
  present : ∀ i, ∀ within : i < left.length, memory (base + left[i].val) = i
  absent : ∀ v : Fin k, v ∉ left → memory (base + v.val) = k





private def initializedForestTraceIndexCell (s : ArithmeticState) : ArithmeticState :=
  let address := s.nr 85 + s.nr 7
  {s with
    pc := 2
    nr := Function.update s.nr 5 address
    nm := Function.update s.nm address (s.nr 55)}

private theorem initializeForestTraceIndexCell_correct (s : ArithmeticState)
    (entry : s.pc = 0) (running : s.halted = false) :
    BlockRuns initializeForestTraceIndexCell 2 s (initializedForestTraceIndexCell s) := by
  apply BlockRuns.of_running_exit
  · simp [initializedForestTraceIndexCell, initializeForestTraceIndexCell, arithmeticStep,
      Function.iterate_succ_apply', entry, running]
  · exact running
  · rfl

private structure InitializeForestTraceIndexState (s : ArithmeticState) (i : ℕ)
    (t : ArithmeticState) : Prop where
  entry : t.pc = 0
  running : t.halted = false
  index : t.nr 7 = i
  fixed : ∀ r, r ≠ 5 → r ≠ 7 → t.nr r = s.nr r
  initialized : ∀ j < i, t.nm (s.nr 85 + j) = s.nr 55
  untouched : ∀ a, a < s.nr 85 ∨ s.nr 85 + i ≤ a → t.nm a = s.nm a
  realRegisters : t.rr = s.rr
  realMemory : t.rm = s.rm

theorem initializeForestTraceIndexBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1) :
    ∃ t, BlockRuns initializeForestTraceIndexBlock (1 + (s.nr 55 * 5 + 1)) s t ∧
      t.halted = false ∧ (∀ j < s.nr 55, t.nm (s.nr 85 + j) = s.nr 55) ∧
      (∀ a, a < s.nr 85 ∨ s.nr 85 + s.nr 55 ≤ a → t.nm a = s.nm a) ∧
      (∀ r, r ≠ 5 → r ≠ 7 → t.nr r = s.nr r) ∧ t.rr = s.rr ∧ t.rm = s.rm := by
  let inv := InitializeForestTraceIndexState s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, ?_, fun _ _ => rfl, rfl, rfl⟩
    · intro r _ different
      simp [Function.update_of_ne different]
    · intro _ impossible
      omega
  have control (i : ℕ) (m : ArithmeticState) (hm : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 55 = s.nr 55 :=
    ⟨hm.entry, hm.running, hm.index, hm.fixed 55 (by decide) (by decide)⟩
  have iterate (i : ℕ) (_ : i < s.nr 55) (m : ArithmeticState) (hm : inv i m) :
      ∃ u, BlockRuns initializeForestTraceIndexCell 2 m u ∧ u.halted = false ∧
        inv (i + 1) {u with pc := 0, nr := Function.update u.nr 7 (u.nr 7 + u.nr 6)} := by
    let u := initializedForestTraceIndexCell m
    have markBase := hm.fixed 85 (by decide) (by decide)
    have dimension := hm.fixed 55 (by decide) (by decide)
    have inc := (hm.fixed 6 (by decide) (by decide)).trans one
    have changed : u.nm = Function.update m.nm (s.nr 85 + i) (s.nr 55) := by
      simp [u, initializedForestTraceIndexCell, markBase, hm.index, dimension]
    refine ⟨u, initializeForestTraceIndexCell_correct m hm.entry hm.running, hm.running,
      rfl, hm.running, ?_, ?_, ?_, ?_, hm.realRegisters, hm.realMemory⟩
    · simp [u, initializedForestTraceIndexCell, hm.index, inc]
    · intro r notAddress notIndex
      simp [u, initializedForestTraceIndexCell, Function.update_of_ne notAddress,
        Function.update_of_ne notIndex, hm.fixed r notAddress notIndex]
    · intro j before
      change u.nm (s.nr 85 + j) = s.nr 55
      rw [changed]
      by_cases equal : j = i
      · simp [equal]
      · rw [Function.update_of_ne (by omega)]
        exact hm.initialized j (by omega)
    · intro a outside
      change u.nm a = s.nm a
      rw [changed, Function.update_of_ne (by omega)]
      exact hm.untouched a (by omega)
  obtain ⟨last, final, complete⟩ := countedLoopFromZero_correct 6 7 55 (s.nr 55) 2
    initializeForestTraceIndexCell inv entry running initial control iterate
  exact ⟨_, complete, final.running, final.initialized, final.untouched, final.fixed,
    final.realRegisters, final.realMemory⟩





private def indexedForestTraceCell (s : ArithmeticState) : ArithmeticState :=
  let readAddress := s.nr 83 + s.nr 7
  let vertex := s.nm readAddress
  let address := s.nr 85 + vertex
  {s with
    pc := 4
    nr := Function.update (Function.update (Function.update s.nr 5 readAddress) 8 vertex) 5 address
    nm := Function.update s.nm address (s.nr 7)}

private theorem indexForestTraceCell_correct (s : ArithmeticState)
    (entry : s.pc = 0) (running : s.halted = false) :
    BlockRuns indexForestTraceCell 4 s (indexedForestTraceCell s) := by
  apply BlockRuns.of_running_exit
  · simp [indexedForestTraceCell, indexForestTraceCell, arithmeticStep,
      Function.iterate_succ_apply', entry, running]
  · exact running
  · rfl

private structure IndexForestTraceState {k : ℕ} (s : ArithmeticState) (left : List (Fin k))
    (i : ℕ) (t : ArithmeticState) : Prop where
  entry : t.pc = 0
  running : t.halted = false
  index : t.nr 7 = i
  fixed : ∀ r, r ≠ 5 → r ≠ 7 → r ≠ 8 → t.nr r = s.nr r
  present : ∀ j, ∀ within : j < left.length, j < i → t.nm (s.nr 85 + left[j].val) = j
  absent : ∀ v : Fin k, (∀ j, ∀ within : j < left.length, j < i → left[j] ≠ v) →
    t.nm (s.nr 85 + v.val) = k
  untouched : ∀ a, a < s.nr 85 ∨ s.nr 85 + k ≤ a → t.nm a = s.nm a
  realRegisters : t.rr = s.rr
  realMemory : t.rm = s.rm

/-- Index the knots of a nodup trace in their path order. Neither parent trace
nor any other allocated table is modified. -/
theorem indexForestTraceBlock_correct {k : ℕ} {s : ArithmeticState} {left : List (Fin k)}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1)
    (count : s.nr 10 = left.length) (distinct : left.Nodup)
    (array : ForestTraceArray s.nm (s.nr 83) left) (separate : s.nr 83 + left.length ≤ s.nr 85)
    (empty : ∀ j < k, s.nm (s.nr 85 + j) = k) :
    ∃ t, BlockRuns indexForestTraceBlock (1 + (left.length * 7 + 1)) s t ∧
      t.halted = false ∧ ForestTraceIndexTable t.nm (s.nr 85) left ∧
      (∀ a, a < s.nr 85 ∨ s.nr 85 + k ≤ a → t.nm a = s.nm a) ∧
      (∀ r, r ≠ 5 → r ≠ 7 → r ≠ 8 → t.nr r = s.nr r) ∧ t.rr = s.rr ∧ t.rm = s.rm := by
  let inv := IndexForestTraceState s left
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, ?_, ?_, fun _ _ => rfl, rfl, rfl⟩
    · intro r _ different _
      simp [Function.update_of_ne different]
    · intro _ _ impossible
      omega
    · intro v _
      exact empty _ v.isLt
  have control (i : ℕ) (m : ArithmeticState) (hm : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 10 = left.length :=
    ⟨hm.entry, hm.running, hm.index, (hm.fixed 10 (by decide) (by decide) (by decide)).trans count⟩
  have iterate (i : ℕ) (within : i < left.length) (m : ArithmeticState) (hm : inv i m) :
      ∃ u, BlockRuns indexForestTraceCell 4 m u ∧ u.halted = false ∧
        inv (i + 1) {u with pc := 0, nr := Function.update u.nr 7 (u.nr 7 + u.nr 6)} := by
    let u := indexedForestTraceCell m
    have leftBase := hm.fixed 83 (by decide) (by decide) (by decide)
    have markBase := hm.fixed 85 (by decide) (by decide) (by decide)
    have inc := (hm.fixed 6 (by decide) (by decide) (by decide)).trans one
    have vertex : m.nm (s.nr 83 + i) = left[i].val :=
      (hm.untouched _ (.inl (by omega))).trans (array i within)
    have changed : u.nm = Function.update m.nm (s.nr 85 + left[i].val) i := by
      simp [u, indexedForestTraceCell, leftBase, markBase, hm.index, vertex]
    refine ⟨u, indexForestTraceCell_correct m hm.entry hm.running, hm.running,
      rfl, hm.running, ?_, ?_, ?_, ?_, ?_, hm.realRegisters, hm.realMemory⟩
    · simp [u, indexedForestTraceCell, hm.index, inc]
    · intro r notAddress notIndex notVertex
      simp [u, indexedForestTraceCell, Function.update_of_ne notAddress,
        Function.update_of_ne notIndex, Function.update_of_ne notVertex,
        hm.fixed r notAddress notIndex notVertex]
    · intro j inside before
      change u.nm (s.nr 85 + left[j].val) = j
      rw [changed]
      by_cases equal : j = i
      · subst j
        simp
      · have separates : left[j].val ≠ left[i].val := by
          intro same
          exact equal ((List.Nodup.getElem_inj_iff distinct).mp (Fin.ext same))
        rw [Function.update_of_ne (by omega)]
        exact hm.present j inside (by omega)
    · intro v missing
      have separateCode : left[i].val ≠ v.val := fun same => missing i within (by omega) (Fin.ext same)
      change u.nm (s.nr 85 + v.val) = k
      rw [changed, Function.update_of_ne (by omega)]
      exact hm.absent v (fun j hj earlier => missing j hj (by omega))
    · intro a outside
      have finite := left[i].isLt
      change u.nm a = s.nm a
      rw [changed, Function.update_of_ne (by omega)]
      exact hm.untouched a outside
  obtain ⟨last, final, complete⟩ := countedLoopFromZero_correct 6 7 10 left.length 4
    indexForestTraceCell inv entry running initial control iterate
  exact ⟨_, complete, final.running, ⟨fun i within => final.present i within within,
      fun v missing => final.absent v fun i within _ same => missing (same ▸ List.getElem_mem within)⟩,
    final.untouched, final.fixed, final.realRegisters, final.realMemory⟩

end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestTraceIndex

/-! matching/AlternatingForestAncestorRAM.lean -/
section RppSource_AlternatingForestAncestorRAM
namespace VehicleRoutingSurvey.Routing



private theorem firstSharedAncestor_cons_mem {k : ℕ} {left tail : List (Fin k)} {x : Fin k}
    (inside : x ∈ left) : firstSharedAncestor left (x :: tail) = some x :=
  firstSharedAncestor_eq_some_iff.mpr ⟨inside, [], tail, rfl, by simp⟩

private theorem firstSharedAncestor_cons_not_mem {k : ℕ} {left tail : List (Fin k)} {x : Fin k}
    (outside : x ∉ left) : firstSharedAncestor left (x :: tail) = firstSharedAncestor left tail := by
  cases found : firstSharedAncestor left tail with
  | none =>
    apply firstSharedAncestor_eq_none_iff.mpr
    intro y member
    rcases List.mem_cons.mp member with equal | interior
    · exact equal.symm ▸ outside
    · exact firstSharedAncestor_eq_none_iff.mp found y interior
  | some v =>
    obtain ⟨inside, before, after, split, noneBefore⟩ := firstSharedAncestor_eq_some_iff.mp found
    refine firstSharedAncestor_eq_some_iff.mpr ⟨inside, x :: before, after, ?_, ?_⟩
    · simp only [split, List.cons_append]
    · intro y member
      rcases List.mem_cons.mp member with equal | interior
      · exact equal.symm ▸ outside
      · exact noneBefore y interior



private def inspectedForestAncestor (s : ArithmeticState) (pc : ℕ) : ArithmeticState :=
  let readAddress := s.nr 84 + s.nr 14
  let vertex := s.nm readAddress
  let address := s.nr 85 + vertex
  {s with
    pc := pc
    nr := Function.update (Function.update (Function.update (Function.update s.nr 5 readAddress) 12 vertex)
      5 address) 13 (s.nm address)}

private theorem inspectForestAncestor_exec {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (remaining : s.nr 14 < s.nr 11) :
    (arithmeticStep findForestTraceSplitLoop)^[6] s = inspectedForestAncestor s
      (if s.nr 55 ≤ s.nm (s.nr 85 + s.nm (s.nr 84 + s.nr 14)) then 6 else 10) := by
  simp [inspectedForestAncestor, findForestTraceSplitLoop, arithmeticStep, entry, running,
    Function.iterate_succ_apply', not_le.mpr remaining]

private theorem inspectedForestAncestor_fixed {s : ArithmeticState} {pc : ℕ} (r : ℕ)
    (address : r ≠ 5) (candidate : r ≠ 12) (leftPosition : r ≠ 13) :
    (inspectedForestAncestor s pc).nr r = s.nr r := by
  simp [inspectedForestAncestor, Function.update_of_ne address, Function.update_of_ne candidate,
    Function.update_of_ne leftPosition]

/-- `right` is the unscanned suffix of the array, beginning at register 14.
Returns the exact earliest shared vertex and costs at most eight instructions
per remaining vertex, plus three for the terminating case. -/
theorem findForestTraceSplitLoop_correct {k : ℕ} (left right : List (Fin k))
    {s : ArithmeticState} (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 6 = 1) (zero : s.nr 8 = 0) (dimension : s.nr 55 = k)
    (leftCount : s.nr 10 = left.length) (rightCount : s.nr 11 = s.nr 14 + right.length)
    (bounded : left.length ≤ k)
    (rightArray : ForestTraceArray s.nm (s.nr 84 + s.nr 14) right)
    (marks : ForestTraceIndexTable s.nm (s.nr 85) left) :
    ∃ (t : ArithmeticState) (steps : ℕ) (shared : Option (Fin k)) (li ri : ℕ),
      BlockRuns findForestTraceSplitLoop steps s t ∧ t.halted = false ∧
      steps ≤ 8 * right.length + 3 ∧ ForestTraceSplit left right shared li ri ∧
      t.nr 12 = (shared.map Fin.val).getD k ∧ t.nr 13 = li ∧ t.nr 14 = s.nr 14 + ri ∧
      (∀ r, r ≠ 5 → r ≠ 12 → r ≠ 13 → r ≠ 14 → t.nr r = s.nr r) ∧
      t.nm = s.nm ∧ t.rr = s.rr ∧ t.rm = s.rm := by
  induction right generalizing s with
  | nil =>
    let t := {s with
      pc := 10
      nr := Function.update (Function.update s.nr 12 k) 13 left.length}
    have exhausted : s.nr 11 ≤ s.nr 14 := by simp [rightCount]
    have ran : BlockRuns findForestTraceSplitLoop 3 s t := by
      apply BlockRuns.of_running_exit
      · simp [t, findForestTraceSplitLoop, arithmeticStep, entry, running, exhausted,
          dimension, zero, leftCount, Function.iterate_succ_apply']
      · exact running
      · rfl
    have first : none = firstSharedAncestor left [] :=
      (firstSharedAncestor_eq_none_iff.mpr (by simp)).symm
    refine ⟨t, 3, none, left.length, 0, ran, running, by simp, ⟨first, rfl, rfl⟩,
      by simp [t], by simp [t], by simp [t], ?_, rfl, rfl, rfl⟩
    intro r _ candidate leftPosition _
    simp [t, Function.update_of_ne candidate, Function.update_of_ne leftPosition]
  | cons x tail ih =>
    have remaining : s.nr 14 < s.nr 11 := by simp only [List.length_cons] at rightCount; omega
    have vertex : s.nm (s.nr 84 + s.nr 14) = x.val := by
      have stored := rightArray 0 (by simp)
      change s.nm (s.nr 84 + s.nr 14 + 0) = x.val at stored
      simpa only [Nat.add_zero] using stored
    by_cases present : x ∈ left
    · obtain ⟨i, inside, equals⟩ := List.mem_iff_getElem.mp present
      have slot : s.nm (s.nr 85 + x.val) = i := by simpa [equals] using marks.present i inside
      have selected : ¬s.nr 55 ≤ i := by omega
      let t := inspectedForestAncestor s 10
      have ran : BlockRuns findForestTraceSplitLoop 6 s t := by
        apply BlockRuns.of_running_exit
        · simpa only [vertex, slot, if_neg selected] using inspectForestAncestor_exec entry running remaining
        · exact running
        · rfl
      refine ⟨t, 6, some x, i, 0, ran, running, ?_,
        ⟨(firstSharedAncestor_cons_mem present).symm, inside, by simp, equals, rfl⟩,
        ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
      · simp only [List.length_cons, Nat.mul_add, Nat.mul_one] <;> omega
      · simp [t, inspectedForestAncestor, vertex]
      · simp [t, inspectedForestAncestor, vertex, slot]
      · simp [t, inspectedForestAncestor]
      · intro r notAddress notCandidate notLeft _
        exact inspectedForestAncestor_fixed r notAddress notCandidate notLeft
    · have slot : s.nm (s.nr 85 + x.val) = k := marks.absent x present
      have skip : s.nr 55 ≤ k := dimension.le
      let m := inspectedForestAncestor s 6
      let u := {m with pc := 0, nr := Function.update m.nr 14 (s.nr 14 + 1)}
      have progressed : (arithmeticStep findForestTraceSplitLoop)^[8] s = u := by
        change (arithmeticStep findForestTraceSplitLoop)^[2 + 6] s = u
        rw [Function.iterate_add_apply, inspectForestAncestor_exec entry running remaining]
        simp only [vertex, slot, if_pos skip]
        simp [u, m, inspectedForestAncestor, findForestTraceSplitLoop, arithmeticStep, running,
          Function.iterate_succ_apply', one]
      have fixed (r : ℕ) (notAddress : r ≠ 5) (notCandidate : r ≠ 12)
          (notLeft : r ≠ 13) (notRight : r ≠ 14) : u.nr r = s.nr r := by
        simp only [u, Function.update_of_ne notRight]
        exact inspectedForestAncestor_fixed r notAddress notCandidate notLeft
      have index : u.nr 14 = s.nr 14 + 1 := by simp [u]
      have rightBase := fixed 84 (by decide) (by decide) (by decide) (by decide)
      have markBase := fixed 85 (by decide) (by decide) (by decide) (by decide)
      have nextArray : ForestTraceArray u.nm (u.nr 84 + u.nr 14) tail := by
        intro j within
        have address : u.nr 84 + u.nr 14 + j = s.nr 84 + s.nr 14 + (j + 1) := by
          rw [index, rightBase]; omega
        change s.nm (u.nr 84 + u.nr 14 + j) = tail[j].val
        rw [address]
        have stored := rightArray (j + 1) (by simpa using within)
        change s.nm (s.nr 84 + s.nr 14 + (j + 1)) = tail[j].val at stored
        exact stored
      have nextMarks : ForestTraceIndexTable u.nm (u.nr 85) left := by
        change ForestTraceIndexTable s.nm (u.nr 85) left
        rwa [markBase]
      have remainingCount : u.nr 11 = u.nr 14 + tail.length := by
        rw [fixed 11 (by decide) (by decide) (by decide) (by decide), index]
        simp only [List.length_cons] at rightCount
        omega
      obtain ⟨t, steps, shared, li, ri, found, live, bound, split, answer, atLeft, atRight,
        registers, natural, realRegs, reals⟩ := ih (s := u) rfl running
        ((fixed 6 (by decide) (by decide) (by decide) (by decide)).trans one)
        ((fixed 8 (by decide) (by decide) (by decide) (by decide)).trans zero)
        ((fixed 55 (by decide) (by decide) (by decide) (by decide)).trans dimension)
        ((fixed 10 (by decide) (by decide) (by decide) (by decide)).trans leftCount)
        remainingCount nextArray nextMarks
      have ran : BlockRuns findForestTraceSplitLoop (steps + 8) s t := by
        exact BlockRuns.of_running_exit
          (by rw [Function.iterate_add_apply, progressed]; exact found.run) live found.exit
      refine ⟨t, steps + 8, shared, li, ri + 1, ran, live, ?_, ?_, answer, atLeft,
        by rw [atRight, index]; omega,
        fun r h5 h12 h13 h14 => (registers r h5 h12 h13 h14).trans (fixed r h5 h12 h13 h14),
        natural, realRegs, reals⟩
      · simp only [List.length_cons, Nat.mul_add, Nat.mul_one] <;> omega
      · refine ⟨split.first.trans (firstSharedAncestor_cons_not_mem present).symm, ?_⟩
        cases shared with
        | none => exact ⟨split.positions.1, by simp [split.positions.2]⟩
        | some v =>
          obtain ⟨lp, rp, leftVertex, rightVertex⟩ := split.positions
          exact ⟨lp, by simpa using rp, leftVertex, rightVertex⟩





end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestAncestorRAM

/-! matching/MatchingForestTrace.lean -/
section RppSource_MatchingForestTrace
namespace VehicleRoutingSurvey.Routing



private theorem prepareForestSplitScanBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns prepareForestSplitScanBlock 2 s t ∧ t.halted = false ∧
      t.nr 8 = 0 ∧ t.nr 14 = 0 ∧ t.nm = s.nm ∧ t.rr = s.rr ∧ t.rm = s.rm ∧
      (∀ r, r ≠ 8 → r ≠ 14 → t.nr r = s.nr r) := by
  let t := (arithmeticStep prepareForestSplitScanBlock)^[2] s
  have ready : t.halted = false := by
    simp [t, prepareForestSplitScanBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  have final : t.pc = prepareForestSplitScanBlock.length := by
    simp [t, prepareForestSplitScanBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  refine ⟨t, BlockRuns.of_running_exit rfl ready final, ready, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | intro r not8 not14
      simp [t, prepareForestSplitScanBlock, arithmeticStep, Function.iterate_succ_apply', entry, running,
        Function.update_of_ne not8, Function.update_of_ne not14]
    | simp [t, prepareForestSplitScanBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]





theorem MatchingForestTraceResult.ancestorGuard {k : ℕ} {forest : AlternatingForestState (Fin k)}
    {u v : Fin k} {base : ℕ} {s t : ArithmeticState}
    (result : MatchingForestTraceResult forest u v base s t) :
    k ≤ t.nr 12 ↔ forest.commonAncestor u v = none := by
  rw [result.shared]
  cases forest.commonAncestor u v with
  | none => simp
  | some x => simp [not_le.mpr x.isLt]

/-- Trace two outer endpoints and decide whether a tight edge connects them
inside one tree or across two trees, in linear arithmetic-RAM time. -/
theorem traceMatchingForestBlock_correct {k : ℕ} {forest : AlternatingForestState (Fin k)}
    {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop}
    {u v : Fin k} {uParent vParent : Option (Fin k)} {base forestBase : ℕ} {s : ArithmeticState}
    (valid : forest.valid mate tight) (uOuter : forest.role u = .outer uParent)
    (vOuter : forest.role v = .outer vParent) (encoding : AlternatingForestMemory forest forestBase s.nm)
    (storage : MatchingForestTraceStorage k base s) (apart : forestBase + k + k + k ≤ base)
    (parents : s.nr 52 = forestBase + k) (dimension : s.nr 55 = k)
    (uArg : s.nr 0 = u.val) (vArg : s.nr 1 = v.val) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ (t : ArithmeticState) (steps : ℕ), BlockRuns traceMatchingForestBlock steps s t ∧
      t.halted = false ∧ steps ≤ 34 * k + 23 ∧ MatchingForestTraceResult forest u v base s t := by
  let lhs := forest.traceToRoot u
  let rhs := forest.traceToRoot v
  have uMarked : forest.role u ≠ .unlabelled := by simp [uOuter]
  have vMarked : forest.role v ≠ .unlabelled := by simp [vOuter]
  obtain ⟨_, lhsDistinct, lhsCard, _, _⟩ := AlternatingForestState.traceToRoot_spec valid uMarked
  obtain ⟨_, _, rhsCard, _, _⟩ := AlternatingForestState.traceToRoot_spec valid vMarked
  have lhsBound : lhs.length ≤ k := by simpa [lhs] using lhsCard
  have rhsBound : rhs.length ≤ k := by simpa [rhs] using rhsCard
  have leftEnd : s.nr 83 + lhs.length ≤ s.nr 84 := by rw [storage.left, storage.right]; omega
  have rightEnd : s.nr 84 + rhs.length ≤ s.nr 85 := by rw [storage.right, storage.marks]; omega
  have indexEnd : s.nr 85 + k = base + 3 * k := by rw [storage.marks]; omega
  obtain ⟨l, leftSteps, leftRun, lReady, leftBound, lCount, leftArray, lFootprint, lRegs, lRR, lRM, _⟩ :=
    writeMatchingForestTraceBlock_correct 0 83 10 valid uMarked encoding entry running dimension
      (by decide) (by decide) uArg parents (by rw [storage.left]; omega)
  let re := {l with pc := 0}
  have lRight : l.nr 84 = s.nr 84 := lRegs 84 (by decide)
  have lMark : l.nr 85 = s.nr 85 := lRegs 85 (by decide)
  have lDim : l.nr 55 = k := (lRegs 55 (by decide)).trans dimension
  have lEncoding : AlternatingForestMemory forest forestBase re.nm := by
    intro x
    have validIndex := x.isLt
    have kept : ∀ a < base, l.nm a = s.nm a := by
      intro a h
      apply lFootprint a
      exact .inl (by rwa [storage.left])
    change l.nm (forestBase + x.val) = _ ∧ l.nm (forestBase + k + x.val) = _ ∧
      l.nm (forestBase + k + k + x.val) = _
    rw [kept (forestBase + x.val) (by omega), kept (forestBase + k + x.val) (by omega),
      kept (forestBase + k + k + x.val) (by omega)]
    exact encoding x
  obtain ⟨r, rightSteps, rightRun, rReady, rightBound, rCount, rightArray, rFootprint, rRegs, rRR, rRM, oneAt⟩ :=
    writeMatchingForestTraceBlock_correct 1 84 11 valid vMarked (s := re) lEncoding rfl lReady lDim
      (by decide) (by decide) ((lRegs 1 (by decide)).trans vArg)
      ((lRegs 52 (by decide)).trans parents) (by change _ ≤ l.nr 84; rw [lRight, storage.right]; omega)
  have rLeft : r.nr 83 = s.nr 83 := (rRegs 83 (by decide)).trans (lRegs 83 (by decide))
  have rRight : r.nr 84 = s.nr 84 := (rRegs 84 (by decide)).trans lRight
  have rMark : r.nr 85 = s.nr 85 := (rRegs 85 (by decide)).trans lMark
  have rDim : r.nr 55 = k := (rRegs 55 (by decide)).trans lDim
  have rOne : r.nr 6 = 1 := oneAt (by decide)
  have keptLeft : ForestTraceArray r.nm (s.nr 83) lhs := by
    intro i within
    exact (rFootprint _ (.inl (by change _ < l.nr 84; rw [lRight]; omega))).trans
      (leftArray i within)
  let ze := {r with pc := 0}
  obtain ⟨z, initRun, zReady, zSentinel, zFootprint, zRegs, zRR, zRM⟩ :=
    initializeForestTraceIndexBlock_correct (s := ze) rfl rReady rOne
  have zLeft : z.nr 83 = s.nr 83 := (zRegs 83 (by decide) (by decide)).trans rLeft
  have zRight : z.nr 84 = s.nr 84 := (zRegs 84 (by decide) (by decide)).trans rRight
  have zMark : z.nr 85 = s.nr 85 := (zRegs 85 (by decide) (by decide)).trans rMark
  have zDim : z.nr 55 = k := (zRegs 55 (by decide) (by decide)).trans rDim
  have zOne : z.nr 6 = 1 := (zRegs 6 (by decide) (by decide)).trans rOne
  have leftTrimmed : ForestTraceArray z.nm (z.nr 83) lhs := by
    intro i within
    rw [zLeft]
    exact (zFootprint _ (.inl (by change _ < r.nr 85; rw [rMark]; omega))).trans (keptLeft i within)
  let me := {z with pc := 0}
  have initialMarks (i : ℕ) (hi : i < k) : me.nm (me.nr 85 + i) = k := by
    change z.nm (z.nr 85 + i) = k
    have saved := zSentinel i (show i < r.nr 55 by rwa [rDim])
    change z.nm (r.nr 85 + i) = r.nr 55 at saved
    rw [zMark, ← rMark]
    exact saved.trans rDim
  obtain ⟨m, markRun, mReady, marks, mFootprint, mRegs, mRR, mRM⟩ :=
    indexForestTraceBlock_correct (s := me) rfl zReady zOne
      ((zRegs 10 (by decide) (by decide)).trans ((rRegs 10 (by decide)).trans lCount))
      lhsDistinct leftTrimmed (by change z.nr 83 + lhs.length ≤ z.nr 85; rw [zLeft, zMark]; omega)
      initialMarks
  have mOne : m.nr 6 = 1 := (mRegs 6 (by decide) (by decide) (by decide)).trans zOne
  have mDim : m.nr 55 = k := (mRegs 55 (by decide) (by decide) (by decide)).trans zDim
  have mRight : m.nr 84 = s.nr 84 := (mRegs 84 (by decide) (by decide) (by decide)).trans zRight
  have mMark : m.nr 85 = z.nr 85 := mRegs 85 (by decide) (by decide) (by decide)
  have mCountLeft : m.nr 10 = lhs.length :=
    (mRegs 10 (by decide) (by decide) (by decide)).trans ((zRegs 10 (by decide) (by decide)).trans
      ((rRegs 10 (by decide)).trans lCount))
  have mCountRight : m.nr 11 = rhs.length :=
    (mRegs 11 (by decide) (by decide) (by decide)).trans ((zRegs 11 (by decide) (by decide)).trans rCount)
  have stillLeft : ForestTraceArray m.nm (s.nr 83) lhs := by
    intro i within
    exact (mFootprint _ (.inl (by change _ < z.nr 85; rw [zMark]; omega))).trans
      (by simpa only [zLeft] using leftTrimmed i within)
  have stillRight : ForestTraceArray m.nm (s.nr 84) rhs := by
    intro i within
    have saved := rightArray i within
    change r.nm (l.nr 84 + i) = rhs[i].val at saved
    rw [lRight] at saved
    exact (mFootprint _ (.inl (by change _ < z.nr 85; rw [zMark]; omega))).trans
      ((zFootprint _ (.inl (by change _ < r.nr 85; rw [rMark]; omega))).trans
        saved)
  let pe := {m with pc := 0}
  obtain ⟨p, prepares, pReady, pZero, pIndex, pMem, pRR, pRM, pRegs⟩ :=
    prepareForestSplitScanBlock_correct (s := pe) rfl mReady
  let fe := {p with pc := 0}
  have pLeftCount : p.nr 10 = lhs.length := (pRegs 10 (by decide) (by decide)).trans mCountLeft
  have pRightCount : p.nr 11 = rhs.length := (pRegs 11 (by decide) (by decide)).trans mCountRight
  have findArray : ForestTraceArray fe.nm (fe.nr 84 + fe.nr 14) rhs := by
    change ForestTraceArray p.nm (p.nr 84 + p.nr 14) rhs
    rw [pMem, pIndex, Nat.add_zero, pRegs 84 (by decide) (by decide), mRight]
    exact stillRight
  have findMarks : ForestTraceIndexTable fe.nm (fe.nr 85) lhs := by
    change ForestTraceIndexTable p.nm (p.nr 85) lhs
    rw [pMem, pRegs 85 (by decide) (by decide), mMark]
    exact marks
  obtain ⟨f, findSteps, shared, li, ri, findRun, ready, findBound, split, code, leftPrefix, rightPrefix,
      fRegs, fMem, fRR, fRM⟩ := findForestTraceSplitLoop_correct lhs rhs (s := fe) rfl pReady
    ((pRegs 6 (by decide) (by decide)).trans mOne) pZero ((pRegs 55 (by decide) (by decide)).trans mDim)
    pLeftCount (by change p.nr 11 = p.nr 14 + _; simp [pIndex, pRightCount]) lhsBound findArray findMarks
  have splitKind : shared = forest.commonAncestor u v := split.first
  have resultPrefixRight : f.nr 14 = ri := by rw [rightPrefix]; change p.nr 14 + ri = ri; simp [pIndex]
  have naturalAfter : f.nm = m.nm := fMem.trans pMem
  have all := (((((leftRun.append rightRun).append initRun).append markRun).append prepares).append findRun)
  refine ⟨_, _, all, ready, ?_, ?_⟩
  · change leftSteps + rightSteps + (1 + (r.nr 55 * 5 + 1)) +
      (1 + (lhs.length * 7 + 1)) + 2 + findSteps ≤ 34 * k + 23
    rw [rDim]
    omega
  · constructor
    · exact (fRegs 10 (by decide) (by decide) (by decide) (by decide)).trans pLeftCount
    · exact (fRegs 11 (by decide) (by decide) (by decide) (by decide)).trans pRightCount
    · simpa only [relocateState, naturalAfter] using stillLeft
    · simpa only [relocateState, naturalAfter] using stillRight
    · exact code.trans (congrArg (fun x : Option (Fin k) => (x.map Fin.val).getD k) splitKind)
    · change ForestTraceSplit lhs rhs (forest.commonAncestor u v) (f.nr 13) (f.nr 14)
      rw [leftPrefix, resultPrefixRight, ← splitKind]
      exact split
    · intro a beforeOrAfter
      have lOutside : a < s.nr 83 ∨ s.nr 83 + lhs.length ≤ a := by rw [storage.left]; omega
      have rOutside : a < l.nr 84 ∨ l.nr 84 + rhs.length ≤ a := by rw [lRight, storage.right]; omega
      have zOutside : a < r.nr 85 ∨ r.nr 85 + r.nr 55 ≤ a := by rw [rMark, rDim, indexEnd, storage.marks]; omega
      have mOutside : a < z.nr 85 ∨ z.nr 85 + k ≤ a := by rw [zMark, indexEnd, storage.marks]; omega
      exact (congrFun naturalAfter a).trans ((mFootprint a mOutside).trans
        ((zFootprint a zOutside).trans ((rFootprint a rOutside).trans (lFootprint a lOutside))))
    · intro reg away
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at away
      obtain ⟨n2, n3, n4, n5, n6, n7, n8, n10, n11, n12, n13, n14⟩ := away
      exact (fRegs reg n5 n12 n13 n14).trans ((pRegs reg n8 n14).trans ((mRegs reg n5 n7 n8).trans
        ((zRegs reg n5 n7).trans ((rRegs reg (by simp [n2, n3, n4, n5, n6, n8, n11])).trans
          (lRegs reg (by simp [n2, n3, n4, n5, n6, n8, n10]))))))
    · exact fRR.trans (pRR.trans (mRR.trans (zRR.trans (rRR.trans lRR))))
    · exact fRM.trans (pRM.trans (mRM.trans (zRM.trans (rRM.trans lRM))))

end VehicleRoutingSurvey.Routing
end RppSource_MatchingForestTrace

/-! matching/MatchingTraceDispatch.lean -/
section RppSource_MatchingTraceDispatch
open private putTracedOuterEndpoints VehicleRoutingSurvey.Routing.putTracedOuterEndpoints from Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
namespace VehicleRoutingSurvey.Routing





private def resolvedMatchingOuterState (s : ArithmeticState) : ArithmeticState :=
  { s with
    pc := 6
    nr := Function.update (Function.update (Function.update s.nr 36 0) 1 (s.nr 91))
      35 (if s.nr 55 ≤ s.nr 12 then 3 else 1) }

private theorem resolveMatchingOuterTag_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    ∃ steps ≤ 5, BlockRuns resolveMatchingOuterTag steps s (resolvedMatchingOuterState s) := by
  by_cases different : s.nr 55 ≤ s.nr 12
  · refine ⟨4, by decide, ?_⟩
    apply BlockRuns.of_running_exit
    · simp [resolveMatchingOuterTag, resolvedMatchingOuterState, arithmeticStep, entry, running,
        Function.iterate_succ_apply', different]
    · exact running
    · rfl
  · refine ⟨5, le_rfl, ?_⟩
    apply BlockRuns.of_running_exit
    · simp [resolveMatchingOuterTag, resolvedMatchingOuterState, arithmeticStep, entry, running,
        Function.iterate_succ_apply', different]
    · exact running
    · rfl



private def readyMatchingOuterTrace (s : ArithmeticState) : ArithmeticState :=
  {s with pc := 2, nr := Function.update (Function.update s.nr 14 0) 1 (s.nr 2)}

private theorem putTracedOuterEndpoints_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) : BlockRuns putTracedOuterEndpoints 2 s (readyMatchingOuterTrace s) := by
  apply BlockRuns.of_running_exit
  · simp [putTracedOuterEndpoints, readyMatchingOuterTrace, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · exact running
  · rfl



/-- Both representatives are outer. Return the two traces and the exact contraction
or augmentation tag, preserving the selected ID and witness registers. -/
theorem resolveMatchingOuterEvent_spec {k : ℕ} {forest : AlternatingForestState (Fin k)}
    {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop}
    {u v : Fin k} {uParent vParent : Option (Fin k)} {base forestBase : ℕ}
    (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false)
    (valid : forest.valid mate tight) (uOuter : forest.role u = .outer uParent)
    (vOuter : forest.role v = .outer vParent) (encoding : AlternatingForestMemory forest forestBase s.nm)
    (scratch : MatchingForestTraceStorage k base s) (apart : forestBase + k + k + k ≤ base)
    (parentBase : s.nr 52 = forestBase + k) (dimension : s.nr 55 = k)
    (uArg : s.nr 0 = u.val) (vArg : s.nr 2 = v.val) :
    ∃ t steps, BlockRuns resolveMatchingOuterEvent steps s t ∧ t.halted = false ∧
      steps ≤ 34 * k + 30 ∧ MatchingResolvedOuter forest u v base s t := by
  let prepared := {readyMatchingOuterTrace s with pc := 0}
  have first := putTracedOuterEndpoints_spec s entry running
  have readyRegs (r : ℕ) (differentOne : r ≠ 1) (differentTemp : r ≠ 14) :
      prepared.nr r = s.nr r := by
    simp [prepared, readyMatchingOuterTrace, Function.update_of_ne differentOne, Function.update_of_ne differentTemp]
  have traceStorage : MatchingForestTraceStorage k base prepared :=
    ⟨(readyRegs 83 (by decide) (by decide)).trans scratch.left,
      (readyRegs 84 (by decide) (by decide)).trans scratch.right,
      (readyRegs 85 (by decide) (by decide)).trans scratch.marks⟩
  have actualV : prepared.nr 1 = v.val := by simp [prepared, readyMatchingOuterTrace, vArg]
  obtain ⟨middle, traceSteps, traceRun, live, bound, trace⟩ :=
    traceMatchingForestBlock_correct (s := prepared) valid uOuter vOuter encoding traceStorage apart
      ((readyRegs 52 (by decide) (by decide)).trans parentBase)
      ((readyRegs 55 (by decide) (by decide)).trans dimension)
      ((readyRegs 0 (by decide) (by decide)).trans uArg) actualV rfl running
  let classified := {middle with pc := 0}
  obtain ⟨finishSteps, small, finish⟩ := resolveMatchingOuterTag_spec classified rfl live
  have joined := first.append (traceRun.append finish)
  have dim : middle.nr 55 = k := (trace.registers 55 (by decide)).trans
    ((readyRegs 55 (by decide) (by decide)).trans dimension)
  have outerTag : (if middle.nr 55 ≤ middle.nr 12 then 3 else 1) =
      if forest.commonAncestor u v = none then 3 else 1 := by
    rw [dim]
    by_cases disjoint : forest.commonAncestor u v = none
    · simp [(trace.ancestorGuard).mpr disjoint, disjoint]
    · have together : ¬k ≤ middle.nr 12 := fun guessed => disjoint (trace.ancestorGuard.mp guessed)
      simp [together, disjoint]
  refine ⟨_, 2 + (traceSteps + finishSteps), joined, live, by omega, ?_⟩
  constructor
  · simpa [classified, resolvedMatchingOuterState, relocateState] using outerTag
  · change middle.nr 91 = s.nr 91
    exact (trace.registers 91 (by decide)).trans (readyRegs 91 (by decide) (by decide))
  · simp [classified, resolvedMatchingOuterState, relocateState]
  · simpa [classified, resolvedMatchingOuterState, relocateState] using trace.leftCount
  · simpa [classified, resolvedMatchingOuterState, relocateState] using trace.rightCount
  · simpa [classified, resolvedMatchingOuterState, relocateState, readyRegs 83 (by decide) (by decide)] using trace.left
  · simpa [classified, resolvedMatchingOuterState, relocateState, readyRegs 84 (by decide) (by decide)] using trace.right
  · simpa [classified, resolvedMatchingOuterState, relocateState] using trace.shared
  · simpa [classified, resolvedMatchingOuterState, relocateState] using trace.split
  · exact trace.natural
  · intro r away
    have traceFixed : r ∉ [2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14] := by simp at away ⊢; omega
    have a : r ≠ 1 := by simp at away; omega
    have b : r ≠ 14 := by simp at away; omega
    have c : r ≠ 35 := by simp at away; omega
    have d : r ≠ 36 := by simp at away; omega
    simpa [classified, resolvedMatchingOuterState, relocateState, Function.update_of_ne a,
      Function.update_of_ne c, Function.update_of_ne d] using (trace.registers r traceFixed).trans (readyRegs r a b)
  · exact trace.realRegisters
  · exact trace.realMemory



private def matchingDispatchTagged (s : ArithmeticState) : ArithmeticState :=
  {s with pc := 3, nr := Function.update (Function.update (Function.update s.nr 36 0) 37 1) 38 2}

private theorem initMatchingDispatchTags_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) : BlockRuns initMatchingDispatchTags 3 s (matchingDispatchTagged s) := by
  apply BlockRuns.of_running_exit
  · simp [initMatchingDispatchTags, matchingDispatchTagged, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · exact running
  · rfl







private theorem MatchingResolvedOuter.copy_pc {k : ℕ} {forest : AlternatingForestState (Fin k)}
    {u v : Fin k} {base : ℕ} {s t p : ArithmeticState}
    (trace : MatchingResolvedOuter forest u v base s t) (nat : p.nr = t.nr)
    (memory : p.nm = t.nm) (real : p.rm = t.rm) (registers : p.rr = t.rr) :
    MatchingResolvedOuter forest u v base s p := by
  constructor
  · simpa only [nat] using trace.tag
  · simpa only [nat] using trace.selected
  · simpa only [nat] using trace.zero
  · simpa only [nat] using trace.leftCount
  · simpa only [nat] using trace.rightCount
  · simpa only [memory] using trace.left
  · simpa only [memory] using trace.right
  · simpa only [nat] using trace.shared
  · simpa only [nat] using trace.split
  · simpa only [memory] using trace.natural
  · simpa only [nat] using trace.registers
  · exact registers.trans trace.realRegisters
  · exact real.trans trace.realMemory

theorem classifyAndTraceMatchingEvent_outer {k : ℕ} {forest : AlternatingForestState (Fin k)}
    {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop}
    {u v : Fin k} {uParent vParent : Option (Fin k)} {base forestBase : ℕ}
    (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (outerClass : matchingEventClass s = 1)
    (valid : forest.valid mate tight) (uOuter : forest.role u = .outer uParent)
    (vOuter : forest.role v = .outer vParent) (encoding : AlternatingForestMemory forest forestBase s.nm)
    (scratch : MatchingForestTraceStorage k base s) (apart : forestBase + k + k + k ≤ base)
    (parentBase : s.nr 52 = forestBase + k) (dimension : s.nr 55 = k)
    (uArg : matchingEventLeftRep s = u.val) (vArg : matchingEventRightRep s = v.val) :
    ∃ t steps, steps ≤ 34 * k + 57 ∧ BlockRuns classifyAndTraceMatchingEvent steps s t ∧ t.halted = false ∧
      t.nr 36 = 0 ∧ t.nr 37 = 1 ∧ t.nr 38 = 2 ∧ t.nr 1 = s.nr 1 ∧
      t.nr 91 = s.nr 1 ∧ (t.nr 92, t.nr 93) = matchingOriginalGrowthEvent s ∧
      (∀ a, a < base ∨ base + 3 * k ≤ a → t.nm a = s.nm a) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ r ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 35, 36, 37, 38, 91, 92, 93],
        t.nr r = s.nr r) ∧
      ∃ ready, ready.nr 83 = s.nr 83 ∧ ready.nr 84 = s.nr 84 ∧ MatchingResolvedOuter forest u v base ready t := by
  obtain ⟨detected, firstSteps, firstCost, cls⟩ := classifyMatchingSelectedEvent_spec s entry running one
  let leading := {detected with pc := 0}
  let tagged := matchingDispatchTagged leading
  let p := {tagged with pc := 0}
  have set := initMatchingDispatchTags_spec leading rfl cls.running
  have pTag : p.nr 35 = 1 := by simpa [p, tagged, matchingDispatchTagged, leading, outerClass] using cls.tag
  have pZero : p.nr 36 = 0 := by simp [p, tagged, matchingDispatchTagged]
  have pUnit : p.nr 37 = 1 := by simp [p, tagged, matchingDispatchTagged]
  have pTwo : p.nr 38 = 2 := by simp [p, tagged, matchingDispatchTagged]
  have live : p.halted = false := cls.running
  have noCut : ¬matchingEventIsCut s := by
    intro cut
    have alternate : matchingEventClass s = 2 := if_pos cut
    omega
  have pFixed (r : ℕ) (away : r ∉ [0, 2, 6, 10, 11, 14, 35, 36, 37, 38, 91, 92, 93]) : p.nr r = s.nr r := by
    have a : r ≠ 36 := by simp at away; omega
    have b : r ≠ 37 := by simp at away; omega
    have c : r ≠ 38 := by simp at away; omega
    have old : r ∉ [0, 2, 6, 10, 11, 14, 35, 91, 92, 93] := by simp at away ⊢; omega
    simpa [p, tagged, matchingDispatchTagged, leading, Function.update_of_ne a, Function.update_of_ne b, Function.update_of_ne c]
      using cls.registers r old
  have pInputU : p.nr 0 = u.val := by
    simpa [p, tagged, matchingDispatchTagged, leading] using (cls.edgeRepresentatives noCut).1.trans uArg
  have pInputV : p.nr 2 = v.val := by
    simpa [p, tagged, matchingDispatchTagged, leading] using (cls.edgeRepresentatives noCut).2.trans vArg
  have pScratch : MatchingForestTraceStorage k base p :=
    ⟨(pFixed 83 (by decide)).trans scratch.left, (pFixed 84 (by decide)).trans scratch.right,
      (pFixed 85 (by decide)).trans scratch.marks⟩
  have pEncoding : AlternatingForestMemory forest forestBase p.nm := cls.natural.symm ▸ encoding
  obtain ⟨out, traceSteps, ran, traceLive, cost, resolved⟩ := resolveMatchingOuterEvent_spec p rfl live
    valid uOuter vOuter pEncoding pScratch apart ((pFixed 52 (by decide)).trans parentBase)
    ((pFixed 55 (by decide)).trans dimension) pInputU pInputV
  have inBranch := branchOnAtMost_right 35 36 [] resolveMatchingOuterEvent (s := p) rfl live (by omega) ran traceLive
  have branch := branchOnAtMost_left 35 37 _ [] (s := p) rfl live (by omega) inBranch traceLive
  have all := cls.run.append (set.append branch)
  have pId : p.nr 91 = s.nr 1 := by simpa [p, tagged, matchingDispatchTagged, leading] using cls.identifier
  have pEdge : (p.nr 92, p.nr 93) = matchingOriginalGrowthEvent s := by
    simpa [p, tagged, matchingDispatchTagged, leading] using cls.endpoints
  refine ⟨_, firstSteps + (3 + (1 + (1 + traceSteps) + 1)), by omega,
    all, traceLive, resolved.zero, (resolved.registers 37 (by decide)).trans pUnit, (resolved.registers 38 (by decide)).trans pTwo,
    resolved.selected.trans pId, (resolved.registers 91 (by decide)).trans pId, ?_, ?_,
    resolved.realMemory.trans cls.real, resolved.realRegisters.trans cls.realRegisters, ?_, ?_⟩
  · change (out.nr 92, out.nr 93) = matchingOriginalGrowthEvent s
    rw [resolved.registers 92 (by decide), resolved.registers 93 (by decide)]
    exact pEdge
  · intro addr outside
    exact (resolved.natural addr outside).trans (congrFun cls.natural addr)
  · intro r hr
    have traceKeep : r ∉ [1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 35, 36] := by simp at hr ⊢; omega
    have detectKeep : r ∉ [0, 2, 6, 10, 11, 14, 35, 36, 37, 38, 91, 92, 93] := by simp at hr ⊢; omega
    exact (resolved.registers r traceKeep).trans (pFixed r detectKeep)
  · exact ⟨p, pFixed 83 (by decide), pFixed 84 (by decide), resolved.copy_pc rfl rfl rfl rfl⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingTraceDispatch

/-! matching/MatchingDispatchTraceFrame.lean -/
section RppSource_MatchingDispatchTraceFrame
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory















/-- Class one uses the actual outer trace to choose between contraction and
augmentation. Retain the original endpoints and the resulting trace arrays. -/
theorem MatchingDispatchState.traceOuter {k i : ℕ} {cost : Fin k → Fin k → ℝ}
    {original s : ArithmeticState} (before : MatchingDispatchState cost original i s)
    (entry : s.pc = 0) (live : s.halted = false) (outer : matchingEventClass s = 1) :
    ∃ a b : Fin k, before.selected.event = .edge s(a,b) ∧ before.part.blocks.block a ≠ before.part.blocks.block b ∧
      ∃ pa pb, before.forest.role (before.part.representative a) = .outer pa ∧
        before.forest.role (before.part.representative b) = .outer pb ∧
        ∃ t ticks, ticks ≤ 34*k+57 ∧ BlockRuns classifyAndTraceMatchingEvent ticks s t ∧ t.halted = false ∧
          t.nr 36 = 0 ∧ t.nr 37 = 1 ∧ t.nr 38 = 2 ∧ t.nr 1 = s.nr 1 ∧
          (t.nr 92,t.nr 93) = (a.val,b.val) ∧
          (∀ x, x < s.nr 83 ∨ s.nr 83+3*k ≤ x → t.nm x = s.nm x) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
          (∀ r, r = 9 ∨ r = 20 ∨ r = 21 ∨ (30 ≤ r ∧ r ≤ 34) ∨
            (39 ≤ r ∧ r ≤ 90) ∨ 100 ≤ r → t.nr r = s.nr r) ∧
          ∃ ready, ready.nr 83 = s.nr 83 ∧ ready.nr 84 = s.nr 84 ∧
            MatchingResolvedOuter before.forest (before.part.representative a) (before.part.representative b)
              (s.nr 83) ready t := by
  have details := before.selected.kind
  cases type : before.selected.event with
  | cut B =>
    rw [type] at details
    obtain ⟨_, _, _, tag, _⟩ := details
    omega
  | edge e =>
    rw [type] at details
    obtain ⟨a,b,words,rfl,separate,left,right,roles⟩ := details
    simp only [before.part.representativeOf_block] at left right roles
    rcases roles with ⟨_,pa,pb,ha,hb⟩ | ⟨growth,_⟩
    · have apart : s.nr 51+k+k+k ≤ s.nr 83 := by
        have rep := before.storage.warm.representativesAfter
        have cand := before.storage.warm.candidatesAfter
        have pairs := before.storage.warm.pairsAfter
        have nodes := before.storage.nodes
        have headers := before.storage.starts
        have lengths := before.storage.lengths
        have trace := before.storage.traceLeft
        omega
      have scratch : MatchingForestTraceStorage k (s.nr 83) s :=
        ⟨rfl, before.storage.traceRight, by rw [before.storage.traceMarks,before.storage.traceRight]⟩
      obtain ⟨t,ticks,limit,run,running,zero,one,two,id,_,ends,natural,real,rr,regs,trace⟩ :=
        classifyAndTraceMatchingEvent_outer s entry live before.one outer before.search.valid ha hb before.selected.dual.roles
          scratch apart before.storage.warm.parents before.selected.dual.dimension left right
      exact ⟨a,b,rfl,separate,pa,pb,ha,hb,t,ticks,limit,run,running,zero,one,two,id,ends.trans words,
        natural,real,rr,(fun r used => regs r (by simp; omega)),trace⟩
    · omega




end VehicleRoutingSurvey.Routing
end RppSource_MatchingDispatchTraceFrame

open VehicleRoutingSurvey.Routing SupplyChainTheory in
theorem solution : (fun {P : Prop} (_ : P) => P) (@VehicleRoutingSurvey.Routing.MatchingDispatchState.traceOuter) :=
  @VehicleRoutingSurvey.Routing.MatchingDispatchState.traceOuter
