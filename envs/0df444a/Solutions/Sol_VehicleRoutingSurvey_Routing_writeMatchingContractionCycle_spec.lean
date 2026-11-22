-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.writeMatchingContractionCycle_spec
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T16:12:39.45104+00:00
-- url     : https://prove2.me/submissions/1cd38826-cd12-4510-bf6a-92148ffb8bc0

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_ContractionStructure

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

/-! matching/MatchingCycleRecordRAM.lean -/
section RppSource_MatchingCycleRecordRAM
namespace VehicleRoutingSurvey.Routing





def writeMatchingCycleChild (memory : ℕ → ℕ) (address : ℕ) (child : MatchingCycleChild) : ℕ → ℕ :=
  Function.update
    (Function.update (Function.update (Function.update memory address child.representative)
      (address + 1) child.node) (address + 2) child.endpointA) (address + 3) child.endpointB

theorem writeMatchingCycleChild_lower (memory : ℕ → ℕ) (address : ℕ) (child : MatchingCycleChild)
    (a : ℕ) (low : a < address) : writeMatchingCycleChild memory address child a = memory a := by
  simp (disch := omega) [writeMatchingCycleChild, Function.update_of_ne]



def currentMatchingCycleChild (s : ArithmeticState) : MatchingCycleChild :=
  ⟨s.nr 15, s.nm (s.nr 74 + s.nr 15), s.nr 16, s.nr 17⟩



theorem appendMatchingCycleChild_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns appendMatchingCycleChild 10 s t ∧ t.halted = false ∧
      t.nr 68 = s.nr 68 + 4 ∧ t.nm = writeMatchingCycleChild s.nm (s.nr 68) (currentMatchingCycleChild s) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 10, 68] → t.nr r = s.nr r := by
  let t := (arithmeticStep appendMatchingCycleChild)^[10] s
  have effect : t.pc = appendMatchingCycleChild.length ∧ t.halted = false ∧ t.nr 68 = s.nr 68 + 4 ∧
      t.nm = writeMatchingCycleChild s.nm (s.nr 68) (currentMatchingCycleChild s) ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    have plusTwo : s.nr 68 + 1 + 1 = s.nr 68 + 2 := by omega
    have plusThree : s.nr 68 + 1 + 1 + 1 = s.nr 68 + 3 := by omega
    have plusFour : s.nr 68 + 1 + 1 + 1 + 1 = s.nr 68 + 4 := by omega
    simp [t, arithmeticStep, appendMatchingCycleChild, entry, running, one, Function.iterate_succ_apply',
      writeMatchingCycleChild, currentMatchingCycleChild, plusTwo, plusThree, plusFour]
  refine ⟨t, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1,
    effect.2.2.1, effect.2.2.2.1, effect.2.2.2.2.1, effect.2.2.2.2.2, ?_⟩
  intro r away
  apply arithmeticRun_keeps_register
  simp [appendMatchingCycleChild, naturalDestination] at away ⊢ <;> omega









theorem startMatchingCycleRecord_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns startMatchingCycleRecord 9 s t ∧ t.halted = false ∧
      t.nm = startMatchingCycleNat s ∧ t.rm = startMatchingCycleReal s ∧
      ∀ r, r ∉ [0, 6, 10] → t.nr r = s.nr r := by
  let t := (arithmeticStep startMatchingCycleRecord)^[9] s
  have effect : t.pc = startMatchingCycleRecord.length ∧ t.halted = false ∧
      t.nm = startMatchingCycleNat s ∧ t.rm = startMatchingCycleReal s := by
    simp [t, arithmeticStep, startMatchingCycleRecord, entry, running, one, Function.iterate_succ_apply',
      startMatchingCycleNat, startMatchingCycleReal, matchingCycleChildCount]
  refine ⟨t, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1,
    effect.2.2.1, effect.2.2.2, ?_⟩
  intro r away
  apply arithmeticRun_keeps_register
  simp [startMatchingCycleRecord, naturalDestination] at away ⊢ <;> omega



theorem matchingCycleChildAt_write (memory : ℕ → ℕ) (address : ℕ) (child : MatchingCycleChild) :
    matchingCycleChildAt (writeMatchingCycleChild memory address child) address = child := by
  cases child
  simp (disch := omega) [matchingCycleChildAt, writeMatchingCycleChild, Function.update_of_ne]











end VehicleRoutingSurvey.Routing
end RppSource_MatchingCycleRecordRAM

/-! matching/MatchingCycleSequence.lean -/
section RppSource_MatchingCycleSequence
namespace VehicleRoutingSurvey.Routing

private theorem readParentCycleWitness_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (child : ℕ) (reverse : Bool) :
    let t := (arithmeticStep (readParentCycleWitness child reverse))^[5] s
    let edge := matchingForestWitnessAt s.nm (s.nr 90) (s.nr child)
    BlockRuns (readParentCycleWitness child reverse) 5 s t ∧ t.halted = false ∧
      (t.nr 16, t.nr 17) = (if reverse then edge.swap else edge) ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
  let t := (arithmeticStep (readParentCycleWitness child reverse))^[5] s
  let edge := matchingForestWitnessAt s.nm (s.nr 90) (s.nr child)
  have effect : t.pc = (readParentCycleWitness child reverse).length ∧ t.halted = false ∧
      (t.nr 16, t.nr 17) = (if reverse then edge.swap else edge) ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    cases reverse <;>
      simp [t, edge, readParentCycleWitness, arithmeticStep, entry, running, one, matchingForestWitnessAt,
        forestWitnessAddress, Function.iterate_succ_apply']
  exact ⟨BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2⟩











theorem leftMatchingCycleChild_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns leftMatchingCycleChild 17 s t ∧ t.halted = false ∧ t.nr 68 = s.nr 68 + 4 ∧
      t.nm = writeMatchingCycleChild s.nm (s.nr 68) (leftCycleRecordAt s (s.nr 7)) ∧ t.rm = s.rm := by
  let loaded := { s with
    pc := 2
    nr := Function.update (Function.update s.nr 6 (s.nr 83 + s.nr 7)) 15 (leftCycleRepresentativeAt s (s.nr 7)) }
  have first : BlockRuns readLeftCycleRepresentative 2 s loaded := by
    apply BlockRuns.of_running_exit
    · simp [loaded, readLeftCycleRepresentative, arithmeticStep, entry, running,
        leftCycleRepresentativeAt, Function.iterate_succ_apply']
    · exact running
    · rfl
  let a := {loaded with pc := 0}
  let witness := (arithmeticStep (readParentCycleWitness 15 true))^[5] a
  have aOne : a.nr 9 = 1 := by simpa [a, loaded] using one
  obtain ⟨second, live, edge, natural, real, _⟩ := readParentCycleWitness_spec a rfl running aOne 15 true
  let b := {witness with pc := 0}
  have bFixed (r : ℕ) (fixed : r ∉ [0, 6, 16, 17]) : b.nr r = a.nr r := by
    apply arithmeticRun_keeps_register _ a 5
    simp [readParentCycleWitness, naturalDestination] at fixed ⊢ <;> omega
  have bOne : b.nr 9 = 1 := (bFixed 9 (by decide)).trans aOne
  obtain ⟨out, third, outLive, cursor, packed, realAfter, _, _⟩ := appendMatchingCycleChild_spec b rfl live bOne
  have bCursor : b.nr 68 = s.nr 68 := by simpa [a, loaded] using bFixed 68 (by decide)
  have bNative : b.nm = s.nm := natural
  have bRole : b.nr 74 = s.nr 74 := by simpa [a, loaded] using bFixed 74 (by decide)
  have bRepresentative : b.nr 15 = leftCycleRepresentativeAt s (s.nr 7) := by
    simpa [a, loaded] using bFixed 15 (by decide)
  have bEdge : (b.nr 16, b.nr 17) =
      (matchingForestWitnessAt s.nm (s.nr 90) (leftCycleRepresentativeAt s (s.nr 7))).swap := by
    change (b.nr 16, b.nr 17) = (matchingForestWitnessAt a.nm (a.nr 90) (a.nr 15)).swap at edge
    have aNat : a.nm = s.nm := rfl
    have aWitness : a.nr 90 = s.nr 90 := by simp [a, loaded]
    have aRepresentative : a.nr 15 = leftCycleRepresentativeAt s (s.nr 7) := by simp [a, loaded]
    rwa [aNat, aWitness, aRepresentative] at edge
  refine ⟨_, first.append (second.append third), outLive, cursor.trans (congrArg (· + 4) bCursor), ?_, realAfter.trans real⟩
  change out.nm = _
  rw [packed, bNative, bCursor]
  have child : currentMatchingCycleChild b = leftCycleRecordAt s (s.nr 7) := by
    simp only [currentMatchingCycleChild, leftCycleRecordAt, bRepresentative, bNative, bRole,
      show b.nr 16 = (matchingForestWitnessAt s.nm (s.nr 90) (leftCycleRepresentativeAt s (s.nr 7))).2 from congrArg Prod.fst bEdge,
      show b.nr 17 = (matchingForestWitnessAt s.nm (s.nr 90) (leftCycleRepresentativeAt s (s.nr 7))).1 from congrArg Prod.snd bEdge]
  rw [child]

private def cycleSuccessorWitness (s : ArithmeticState) (index : ℕ) : ℕ × ℕ :=
  if s.nr index = 0 then (s.nr 93, s.nr 92)
  else matchingForestWitnessAt s.nm (s.nr 90) (rightCycleRepresentativeAt s (s.nr index - 1))

private theorem chooseCycleSuccessor_spec (index : ℕ) (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0) :
    ∃ t steps, steps ≤ 9 ∧ BlockRuns (chooseCycleSuccessor index) steps s t ∧ t.halted = false ∧
      (t.nr 16, t.nr 17) = cycleSuccessorWitness s index ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      ∀ r, r ∉ [0, 6, 16, 17, 18] → t.nr r = s.nr r := by
  have keeps {t : ArithmeticState} {steps : ℕ} (run : BlockRuns (chooseCycleSuccessor index) steps s t)
      (r : ℕ) (safe : r ∉ [0, 6, 16, 17, 18]) : t.nr r = s.nr r := by
    rw [← run.run]
    have permitted : (chooseCycleSuccessor index).all
        (fun instruction => decide (naturalDestination instruction ∈ [0, 6, 16, 17, 18])) = true := by
      unfold chooseCycleSuccessor
      simp [branchOnAtMost, appendBlock, copyClosingCycleWitness, readCycleSuccessor, readParentCycleWitness,
        naturalDestination, relocateInstruction]
    exact arithmeticRun_keeps_from_destination_list _ permitted safe s steps
  by_cases closing : s.nr index = 0
  · let t := {s with pc := 2, nr := Function.update (Function.update s.nr 16 (s.nr 93)) 17 (s.nr 92)}
    have write : BlockRuns copyClosingCycleWitness 2 s t := by
      apply BlockRuns.of_running_exit
      · simp [t, copyClosingCycleWitness, entry, running, zero, arithmeticStep, Function.iterate_succ_apply']
      · exact running
      · rfl
    have run := branchOnAtMost_left index 23 copyClosingCycleWitness
      (appendBlock (readCycleSuccessor index) (readParentCycleWitness 18 false)) entry running
      (by rw [closing, zero]) write running
    exact ⟨_, 4, by decide, run, running, by simp [t, cycleSuccessorWitness, closing], rfl, rfl, keeps run⟩
  · let vertex := rightCycleRepresentativeAt s (s.nr index - 1)
    let a := {s with
      pc := 3
      nr := Function.update (Function.update s.nr 6 (s.nr 84 + (s.nr index - 1))) 18 vertex }
    have load : BlockRuns (readCycleSuccessor index) 3 s a := by
      apply BlockRuns.of_running_exit
      · simp [a, vertex, readCycleSuccessor, rightCycleRepresentativeAt, entry, running, one, arithmeticStep,
          Function.iterate_succ_apply']
      · exact running
      · rfl
    let b := {a with pc := 0}
    have bOne : b.nr 9 = 1 := by simpa [b, a] using one
    obtain ⟨looked, ready, oriented, natural, real, _⟩ := readParentCycleWitness_spec b rfl running bOne 18 false
    have run := branchOnAtMost_right index 23 copyClosingCycleWitness
      (appendBlock (readCycleSuccessor index) (readParentCycleWitness 18 false)) entry running
      (by rw [zero]; omega) (load.append looked) ready
    refine ⟨_, 9, le_rfl, run, ready, ?_, natural, real, keeps run⟩
    simpa [b, a, cycleSuccessorWitness, closing, vertex, relocateState] using oriented

private theorem appendCycleSuccessor_spec (index : ℕ) (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0) :
    ∃ t steps, steps ≤ 19 ∧ BlockRuns (appendBlock (chooseCycleSuccessor index) appendMatchingCycleChild) steps s t ∧
      t.halted = false ∧ t.nr 68 = s.nr 68 + 4 ∧
      t.nm = writeMatchingCycleChild s.nm (s.nr 68) ⟨s.nr 15, s.nm (s.nr 74 + s.nr 15),
        (cycleSuccessorWitness s index).1, (cycleSuccessorWitness s index).2⟩ ∧ t.rm = s.rm := by
  obtain ⟨witness, steps, cost, chosen, live, edge, natSame, realSame, kept⟩ :=
    chooseCycleSuccessor_spec index s entry running one zero
  let a := {witness with pc := 0}
  have unit : a.nr 9 = 1 := (kept 9 (by decide)).trans one
  obtain ⟨t, written, ready, advanced, natural, real, _, _⟩ := appendMatchingCycleChild_spec a rfl live unit
  refine ⟨_, steps + 10, by omega, chosen.append written, ready,
    advanced.trans (congrArg (· + 4) (kept 68 (by decide))), ?_, real.trans realSame⟩
  change t.nm = _
  rw [natural]
  have stable : a.nm = s.nm := natSame
  have cursor : a.nr 68 = s.nr 68 := kept 68 (by decide)
  have role : a.nr 74 = s.nr 74 := kept 74 (by decide)
  have vertex : a.nr 15 = s.nr 15 := kept 15 (by decide)
  have e1 : a.nr 16 = (cycleSuccessorWitness s index).1 := congrArg Prod.fst edge
  have e2 : a.nr 17 = (cycleSuccessorWitness s index).2 := congrArg Prod.snd edge
  simp [currentMatchingCycleChild, stable, cursor, role, vertex, e1, e2]

theorem commonMatchingCycleChild_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0) :
    ∃ t steps, steps ≤ 20 ∧ BlockRuns commonMatchingCycleChild steps s t ∧ t.halted = false ∧
      t.nr 68 = s.nr 68 + 4 ∧ t.nm = writeMatchingCycleChild s.nm (s.nr 68) (commonCycleRecord s) ∧ t.rm = s.rm := by
  let a := {s with pc := 1, nr := Function.update s.nr 15 (s.nr 12)}
  have copy : BlockRuns [.natAdd 15 12 23] 1 s a := by
    apply BlockRuns.of_running_exit
    · simp [a, entry, running, zero, arithmeticStep]
    · exact running
    · rfl
  let b := {a with pc := 0}
  have unit : b.nr 9 = 1 := by simpa [a, b] using one
  have z : b.nr 23 = 0 := by simpa [a, b] using zero
  obtain ⟨t, steps, cost, write, ready, cursor, natural, real⟩ := appendCycleSuccessor_spec 14 b rfl running unit z
  refine ⟨_, 1 + steps, by omega, copy.append write, ready, cursor, ?_, real⟩
  change t.nm = _
  simpa [b, a, cycleSuccessorWitness, rightCycleRepresentativeAt, commonCycleRecord] using natural

theorem rightMatchingCycleChild_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0) :
    ∃ t steps, steps ≤ 23 ∧ BlockRuns rightMatchingCycleChild steps s t ∧ t.halted = false ∧
      t.nr 68 = s.nr 68 + 4 ∧ t.nm = writeMatchingCycleChild s.nm (s.nr 68) (rightCycleRecordAt s (s.nr 7)) ∧ t.rm = s.rm := by
  let backwards := s.nr 14 - (s.nr 7 + 1)
  let address := s.nr 84 + backwards
  let a := {s with
    pc := 4
    nr := Function.update (Function.update (Function.update s.nr 18 backwards) 6 address) 15 (s.nm address) }
  have copy : BlockRuns readRightCycleRepresentative 4 s a := by
    apply BlockRuns.of_running_exit
    · simp [a, address, backwards, readRightCycleRepresentative, entry, running, one, arithmeticStep,
        Function.iterate_succ_apply']
    · exact running
    · rfl
  let b := {a with pc := 0}
  have unit : b.nr 9 = 1 := by simpa [a, b] using one
  have z : b.nr 23 = 0 := by simpa [a, b] using zero
  obtain ⟨t, steps, cost, write, ready, cursor, natural, real⟩ := appendCycleSuccessor_spec 18 b rfl running unit z
  refine ⟨_, 4 + steps, by omega, copy.append write, ready, cursor, ?_, real⟩
  change t.nm = _
  simpa [b, a, cycleSuccessorWitness, rightCycleRepresentativeAt, rightCycleRecordAt, address, backwards] using natural

private def cycleSideCode (right : Bool) : List ArithmeticInstruction :=
  if right then rightMatchingCycleChild else leftMatchingCycleChild

private def cycleSideCount (right : Bool) : ℕ := if right then 14 else 13

def contractionSideRecordAt (right : Bool) (s : ArithmeticState) (i : ℕ) : MatchingCycleChild :=
  if right then rightCycleRecordAt s i else leftCycleRecordAt s i



private theorem cycleRecordWitness_unchanged {s m : ArithmeticState} (ready : MatchingCycleReadSafety s)
    (base : m.nr 90 = s.nr 90) (prior : ∀ a < s.nr 68, m.nm a = s.nm a) (v : ℕ) (hv : v < s.nr 55) :
    matchingForestWitnessAt m.nm (m.nr 90) v = matchingForestWitnessAt s.nm (s.nr 90) v := by
  have addr := ready.witnesses
  rw [base]
  change (m.nm (s.nr 90 + (v + v)), m.nm (s.nr 90 + (v + v) + 1)) =
    (s.nm (s.nr 90 + (v + v)), s.nm (s.nr 90 + (v + v) + 1))
  rw [prior _ (by omega), prior _ (by omega)]

private theorem cycleSideRecord_unchanged (right : Bool) {s m : ArithmeticState} {i : ℕ}
    (ready : MatchingCycleReadSafety s) (inside : i < s.nr (cycleSideCount right))
    (same : ∀ r, r ∉ [0, 6, 7, 10, 15, 16, 17, 18, 23, 68] → m.nr r = s.nr r)
    (earlier : ∀ a < s.nr 68, m.nm a = s.nm a) :
    contractionSideRecordAt right m i = contractionSideRecordAt right s i := by
  have currentNode (v : ℕ) (hv : v < s.nr 55) : m.nm (m.nr 74 + v) = s.nm (s.nr 74 + v) := by
    have bound := ready.node
    rw [same 74 (by decide), earlier _ (by omega)]
  cases right
  · have length : i < s.nr 13 := inside
    have left : leftCycleRepresentativeAt m i = leftCycleRepresentativeAt s i := by
      have bound := ready.left
      rw [leftCycleRepresentativeAt, same 83 (by decide), earlier _ (by omega)] <;> rfl
    have v := ready.leftValid i length
    have witness := cycleRecordWitness_unchanged ready (same 90 (by decide)) earlier _ v
    simp only [contractionSideRecordAt, Bool.false_eq_true, if_false, leftCycleRecordAt, left,
      currentNode _ v, witness]
  · have length : i < s.nr 14 := inside
    have rightRead (j : ℕ) (hj : j < s.nr 14) : rightCycleRepresentativeAt m j = rightCycleRepresentativeAt s j := by
      have bound := ready.right
      rw [rightCycleRepresentativeAt, same 84 (by decide), earlier _ (by omega)] <;> rfl
    let j := s.nr 14 - (i + 1)
    have jBound : j < s.nr 14 := by dsimp [j]; omega
    have pBound : j - 1 < s.nr 14 := by omega
    have backAt : m.nr 14 - (i+1) = j := by rw [same 14 (by decide)] <;> rfl
    have sourceBack : s.nr 14 - (i+1) = j := rfl
    have witness := cycleRecordWitness_unchanged ready (same 90 (by decide)) earlier _ (ready.rightValid _ pBound)
    simp only [contractionSideRecordAt, if_true, rightCycleRecordAt, backAt, sourceBack,
      rightRead _ jBound, currentNode _ (ready.rightValid _ jBound), rightRead _ pBound,
      witness, same 92 (by decide), same 93 (by decide)]

theorem MatchingCycleReadSafety.appended {s m : ArithmeticState} (input : MatchingCycleReadSafety s)
    (cursor : s.nr 68 ≤ m.nr 68) (same : ∀ r ∈ [12, 13, 14, 55, 74, 83, 84, 90], m.nr r = s.nr r)
    (earlier : ∀ a < s.nr 68, m.nm a = s.nm a) : MatchingCycleReadSafety m := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [same 83 (by decide), same 13 (by decide)]
    exact input.left.trans cursor
  · rw [same 84 (by decide), same 14 (by decide)]
    exact input.right.trans cursor
  · rw [same 74 (by decide), same 55 (by decide)]
    exact input.node.trans cursor
  · rw [same 90 (by decide), same 55 (by decide)]
    exact input.witnesses.trans cursor
  · intro j hj
    rw [same 13 (by decide)] at hj
    have pos := input.left
    rw [leftCycleRepresentativeAt, same 83 (by decide), same 55 (by decide), earlier _ (by omega)]
    exact input.leftValid j hj
  · intro j hj
    rw [same 14 (by decide)] at hj
    have pos := input.right
    rw [rightCycleRepresentativeAt, same 84 (by decide), same 55 (by decide), earlier _ (by omega)]
    exact input.rightValid j hj
  · rw [same 12 (by decide), same 55 (by decide)]
    exact input.baseValid

theorem commonCycleRecord_unchanged {s m : ArithmeticState} (input : MatchingCycleReadSafety s)
    (same : ∀ r ∈ [12, 14, 74, 84, 90, 92, 93], m.nr r = s.nr r)
    (earlier : ∀ a < s.nr 68, m.nm a = s.nm a) : commonCycleRecord m = commonCycleRecord s := by
  have node : m.nm (s.nr 74 + s.nr 12) = s.nm (s.nr 74 + s.nr 12) := earlier _ (by
    have h₁ := input.node
    have h₂ := input.baseValid
    omega)
  by_cases empty : s.nr 14 = 0
  · simp [commonCycleRecord, same 12 (by decide), same 14 (by decide), same 74 (by decide),
      same 92 (by decide), same 93 (by decide), node, empty]
  · have pred : s.nr 14 - 1 < s.nr 14 := by omega
    have last : rightCycleRepresentativeAt m (s.nr 14 - 1) = rightCycleRepresentativeAt s (s.nr 14 - 1) := by
      have after := input.right
      rw [rightCycleRepresentativeAt, same 84 (by decide), earlier _ (by omega)] <;> rfl
    have witness := cycleRecordWitness_unchanged input (same 90 (by decide)) earlier _ (input.rightValid _ pred)
    simp [commonCycleRecord, same 12 (by decide), same 14 (by decide), same 74 (by decide), last, witness, node, empty]

private theorem cycleSideCode_spec (right : Bool) (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0) :
    ∃ t steps, steps ≤ 23 ∧ BlockRuns (cycleSideCode right) steps s t ∧ t.halted = false ∧
      t.nr 68 = s.nr 68 + 4 ∧ t.nm = writeMatchingCycleChild s.nm (s.nr 68) (contractionSideRecordAt right s (s.nr 7)) ∧
      t.rm = s.rm := by
  cases right
  · obtain ⟨t, run, next, cursor, packed, real⟩ := leftMatchingCycleChild_spec s entry running one
    exact ⟨t, 17, by decide, run, next, cursor, packed, real⟩
  · exact rightMatchingCycleChild_spec s entry running one zero

structure MatchingCycleSideScan (s : ArithmeticState) (right : Bool) (i : ℕ) (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  live : m.halted = false
  index : m.nr 7 = i
  bases : ∀ r, r ∉ [0, 6, 7, 10, 15, 16, 17, 18, 68] → m.nr r = s.nr r
  cursor : m.nr 68 = s.nr 68 + 4 * i
  earlier : ∀ a < s.nr 68, m.nm a = s.nm a
  real : m.rm = s.rm
  records : ∀ j < i, MatchingCycleReadSafety s →
    matchingCycleChildAt m.nm (s.nr 68 + 4 * j) = contractionSideRecordAt right s j

private theorem cycleSideCode_keeps (right : Bool) {s t : ArithmeticState} {steps r : ℕ}
    (run : BlockRuns (cycleSideCode right) steps s t)
    (safe : r ∉ [0, 6, 10, 15, 16, 17, 18, 68]) : t.nr r = s.nr r := by
  rw [← run.run]
  have included : (cycleSideCode right).all
      (fun ins => decide (naturalDestination ins ∈ [0, 6, 10, 15, 16, 17, 18, 68])) = true := by
    cases right <;> decide
  exact arithmeticRun_keeps_from_destination_list _ included safe s steps

/-- The cycle writer visits each trace cell once. All data up to its start
cursor remain available, and the newly written region is consecutive. -/
theorem writeMatchingCycleSide_bound (right : Bool) (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0) :
    ∃ t steps, steps ≤ 26 * s.nr (cycleSideCount right) + 2 ∧
      BlockRuns (countedLoopFromZero 9 7 (cycleSideCount right) (cycleSideCode right)) steps s t ∧
      MatchingCycleSideScan s right (s.nr (cycleSideCount right)) {t with pc := 0} := by
  have start : MatchingCycleSideScan s right 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, by simp, fun _ _ => rfl, rfl, ?_⟩
    · intro r safe
      exact Function.update_of_ne (by simp at safe; omega) _ _
    · intro j impossible
      exact (Nat.not_lt_zero j impossible).elim
  have countSafe : cycleSideCount right ∉ [0, 6, 7, 10, 15, 16, 17, 18, 68] := by cases right <;> decide
  have next (i : ℕ) (inside : i < s.nr (cycleSideCount right)) (m : ArithmeticState) (inv : MatchingCycleSideScan s right i m) :
      ∃ t steps, steps ≤ 23 ∧ BlockRuns (cycleSideCode right) steps m t ∧ t.halted = false ∧
        MatchingCycleSideScan s right (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    have mOne := (inv.bases 9 (by decide)).trans one
    have mZero := (inv.bases 23 (by decide)).trans zero
    obtain ⟨t, steps, budget, run, live, advanced, natural, real⟩ := cycleSideCode_spec right m inv.entry inv.live mOne mZero
    refine ⟨t, steps, budget, run, live, rfl, live, ?_, ?_, ?_, ?_, real.trans inv.real, ?_⟩
    · simp [cycleSideCode_keeps right run (r := 7) (by decide), cycleSideCode_keeps right run (r := 9) (by decide),
        inv.index, mOne]
    · intro r safe
      have outside : r ≠ 7 := by simp at safe; omega
      exact (Function.update_of_ne outside _ _).trans
        ((cycleSideCode_keeps right run (by simp at safe ⊢; omega)).trans (inv.bases r safe))
    · change t.nr 68 = _
      rw [advanced, inv.cursor]
      omega
    · intro a lower
      change t.nm a = _
      have before : a < m.nr 68 := by rw [inv.cursor]; omega
      rw [natural, writeMatchingCycleChild_lower _ _ _ _ before]
      exact inv.earlier a lower
    · intro j hj safety
      change matchingCycleChildAt t.nm (s.nr 68 + 4 * j) = _
      obtain old | last := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)
      · have sameSlot (offset : ℕ) (word : offset < 4) : t.nm (s.nr 68 + 4 * j + offset) =
            m.nm (s.nr 68 + 4 * j + offset) := by
            have below : s.nr 68 + 4 * j + offset < m.nr 68 := by rw [inv.cursor]; omega
            rw [natural, writeMatchingCycleChild_lower _ _ _ _ below]
        have first := sameSlot 0 (by decide)
        simp only [Nat.add_zero] at first
        simpa only [matchingCycleChildAt, first, sameSlot 1 (by decide), sameSlot 2 (by decide), sameSlot 3 (by decide)]
          using inv.records j old safety
      · subst j
        rw [natural, ← inv.cursor, matchingCycleChildAt_write, inv.index]
        exact cycleSideRecord_unchanged right safety inside
          (fun r away => inv.bases r (by simp at away ⊢; omega)) inv.earlier
  obtain ⟨last, steps, final, budget, run⟩ := countedLoopFromZero_bounded 9 7 (cycleSideCount right)
    (s.nr (cycleSideCount right)) 23 (cycleSideCode right) (MatchingCycleSideScan s right) (s := s) entry running start
    (fun _ _ inv => ⟨inv.entry, inv.live, inv.index, inv.bases _ countSafe⟩) next
  exact ⟨_, steps, by omega, run, rfl, final.live, final.index, final.bases, final.cursor, final.earlier, final.real, final.records⟩



private theorem matchingCycleChildAt_congr {first second : ℕ → ℕ} (address : ℕ)
    (same : ∀ offset < 4, first (address + offset) = second (address + offset)) :
    matchingCycleChildAt first address = matchingCycleChildAt second address := by
  have atZero := same 0 (by decide)
  simp only [Nat.add_zero] at atZero
  simp only [matchingCycleChildAt, atZero, same 1 (by decide), same 2 (by decide), same 3 (by decide)]

/-- Writing a new cycle adds its header and exactly the oriented trace records.
The data needed by the trace and its parent witnesses are read below the append cursor. -/
theorem writeMatchingContractionCycle_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t steps, steps ≤ 26 * (s.nr 13 + s.nr 14) + 34 ∧ BlockRuns writeMatchingContractionCycle steps s t ∧
      t.halted = false ∧ t.nr 68 = s.nr 68 + 4 * matchingCycleChildCount s ∧
      (∀ a < s.nr 68, t.nm a = startMatchingCycleNat s a) ∧ t.rm = startMatchingCycleReal s ∧
      (∀ r, r ∉ [0, 6, 7, 10, 15, 16, 17, 18, 23, 68] → t.nr r = s.nr r) ∧
      (MatchingCycleReadSafety (matchingCycleRecordReference s) →
        (∀ j < s.nr 13, matchingCycleChildAt t.nm (s.nr 68 + 4 * j) = leftCycleRecordAt (matchingCycleRecordReference s) j) ∧
        matchingCycleChildAt t.nm (s.nr 68 + 4 * s.nr 13) = commonCycleRecord (matchingCycleRecordReference s) ∧
        ∀ j < s.nr 14, matchingCycleChildAt t.nm (s.nr 68 + 4 * (s.nr 13 + 1 + j)) = rightCycleRecordAt (matchingCycleRecordReference s) j) := by
  let zeroed := {s with pc := 1, nr := Function.update s.nr 23 0}
  have zero : BlockRuns [.natConst 23 0] 1 s zeroed := by
    apply BlockRuns.of_running_exit
    · simp [zeroed, entry, running, arithmeticStep]
    · exact running
    · rfl
  let a := {zeroed with pc := 0}
  have aOne : a.nr 9 = 1 := by simpa [a, zeroed] using one
  have aZero : a.nr 23 = 0 := by simp [a, zeroed]
  obtain ⟨header, wroteHeader, headerLive, headerNat, headerReal, headerKeeps⟩ := startMatchingCycleRecord_spec a rfl running aOne
  let b := {header with pc := 0}
  have bOne : b.nr 9 = 1 := (headerKeeps 9 (by decide)).trans aOne
  have bZero : b.nr 23 = 0 := (headerKeeps 23 (by decide)).trans aZero
  have bCursor : b.nr 68 = s.nr 68 := (headerKeeps 68 (by decide)).trans (by simp [a, zeroed])
  have bLeft : b.nr 13 = s.nr 13 := (headerKeeps 13 (by decide)).trans (by simp [a, zeroed])
  have bRight : b.nr 14 = s.nr 14 := (headerKeeps 14 (by decide)).trans (by simp [a, zeroed])
  have bNat : b.nm = startMatchingCycleNat s := by simpa [a, zeroed, startMatchingCycleNat, matchingCycleChildCount] using headerNat
  have bReal : b.rm = startMatchingCycleReal s := by simpa [a, zeroed, startMatchingCycleReal] using headerReal
  obtain ⟨left, leftTicks, leftBudget, wroteLeft, leftDone⟩ := writeMatchingCycleSide_bound false b rfl headerLive bOne bZero
  let c := {left with pc := 0}
  have cOne : c.nr 9 = 1 := (leftDone.bases 9 (by decide)).trans bOne
  have cZero : c.nr 23 = 0 := (leftDone.bases 23 (by decide)).trans bZero
  have cCursor : c.nr 68 = s.nr 68 + 4 * s.nr 13 := by
    have atEnd : c.nr 68 = b.nr 68 + 4 * b.nr 13 := leftDone.cursor
    rw [atEnd, bCursor, bLeft]
  obtain ⟨center, centerTicks, centerBudget, wroteCenter, centerLive, advanced, centerNat, centerReal⟩ :=
    commonMatchingCycleChild_spec c rfl leftDone.live cOne cZero
  let d := {center with pc := 0}
  have centerKeeps (r : ℕ) (safe : r ∉ [0, 6, 10, 15, 16, 17, 18, 68]) : center.nr r = c.nr r := by
    rw [← wroteCenter.run]
    exact arithmeticRun_keeps_from_destination_list [0, 6, 10, 15, 16, 17, 18, 68] (by decide) safe c centerTicks
  have dOne : d.nr 9 = 1 := (centerKeeps 9 (by decide)).trans cOne
  have dZero : d.nr 23 = 0 := (centerKeeps 23 (by decide)).trans cZero
  have dRight : d.nr 14 = s.nr 14 := (centerKeeps 14 (by decide)).trans ((leftDone.bases 14 (by decide)).trans bRight)
  obtain ⟨out, rightTicks, rightBudget, wroteRight, rightDone⟩ := writeMatchingCycleSide_bound true d rfl centerLive dOne dZero
  have combined : BlockRuns writeMatchingContractionCycle (1 + (9 + (leftTicks + (centerTicks + rightTicks)))) s _ :=
    zero.append (wroteHeader.append (wroteLeft.append (wroteCenter.append wroteRight)))
  refine ⟨_, _, ?_, combined, rightDone.live, ?_, ?_, rightDone.real.trans (centerReal.trans (leftDone.real.trans bReal)), ?_, ?_⟩
  · change leftTicks ≤ 26 * b.nr 13 + 2 at leftBudget
    change rightTicks ≤ 26 * d.nr 14 + 2 at rightBudget
    rw [bLeft] at leftBudget
    rw [dRight] at rightBudget
    omega
  · have cursor : out.nr 68 = d.nr 68 + 4 * d.nr 14 := rightDone.cursor
    change out.nr 68 = _
    rw [cursor, show d.nr 68 = c.nr 68 + 4 from advanced, cCursor, dRight]
    unfold matchingCycleChildCount
    omega
  · intro addr below
    have bBefore : addr < b.nr 68 := bCursor.symm ▸ below
    have cBefore : addr < c.nr 68 := by rw [cCursor]; omega
    have dBefore : addr < d.nr 68 := by change addr < center.nr 68; rw [advanced]; omega
    exact (rightDone.earlier addr dBefore).trans ((congrFun centerNat addr).trans
      ((writeMatchingCycleChild_lower _ _ _ _ cBefore).trans ((leftDone.earlier addr bBefore).trans (congrFun bNat addr))))
  · intro r safe
    rw [← combined.run]
    exact arithmeticRun_keeps_from_destination_list [0, 6, 7, 10, 15, 16, 17, 18, 23, 68]
      (by decide) safe s (1 + (9 + (leftTicks + (centerTicks + rightTicks))))
  · intro safety
    let reference := matchingCycleRecordReference s
    have bFrame (r : ℕ) (safe : r ∉ [0, 6, 10, 23]) : b.nr r = reference.nr r := by
      have away23 : r ≠ 23 := by simp at safe; omega
      exact (headerKeeps r (by simp at safe ⊢; omega)).trans
        (by simp [a, zeroed, reference, matchingCycleRecordReference, Function.update_of_ne away23])
    have cFrame (r : ℕ) (safe : r ∉ [0, 6, 7, 10, 15, 16, 17, 18, 23, 68]) : c.nr r = reference.nr r :=
      (leftDone.bases r (by simp at safe ⊢; omega)).trans (bFrame r (by simp at safe ⊢; omega))
    have dFrame (r : ℕ) (safe : r ∉ [0, 6, 7, 10, 15, 16, 17, 18, 23, 68]) : d.nr r = reference.nr r :=
      (centerKeeps r (by simp at safe ⊢; omega)).trans (cFrame r safe)
    have bMemory (addr : ℕ) (_ : addr < reference.nr 68) : b.nm addr = reference.nm addr := congrFun bNat addr
    have bSafe : MatchingCycleReadSafety b := safety.appended (by exact bCursor.ge)
      (fun r inside => bFrame r (by simp at inside ⊢; omega)) bMemory
    have cMemory (addr : ℕ) (lower : addr < reference.nr 68) : c.nm addr = reference.nm addr :=
      (leftDone.earlier addr (by rwa [bCursor])).trans (bMemory addr lower)
    have dCursor : d.nr 68 = s.nr 68 + 4 * (s.nr 13 + 1) := by
      change center.nr 68 = _
      rw [advanced, cCursor]
      omega
    have beforeCenter (addr : ℕ) (lower : addr < c.nr 68) : d.nm addr = c.nm addr := by
      change center.nm addr = c.nm addr
      rw [centerNat, writeMatchingCycleChild_lower _ _ _ _ lower]
    have dMemory (addr : ℕ) (lower : addr < reference.nr 68) : d.nm addr = reference.nm addr := by
      have below : addr < s.nr 68 := lower
      exact (beforeCenter addr (by rw [cCursor]; omega)).trans (cMemory addr lower)
    have enough : reference.nr 68 ≤ d.nr 68 := by change s.nr 68 ≤ d.nr 68; rw [dCursor]; omega
    have dSafe : MatchingCycleReadSafety d := safety.appended enough
      (fun r inside => dFrame r (by simp at inside ⊢; omega)) dMemory
    refine ⟨?_, ?_, ?_⟩
    · intro j inside
      change matchingCycleChildAt out.nm _ = _
      have atLeft : j < b.nr 13 := by rwa [bLeft]
      have encoded := leftDone.records j atLeft bSafe
      have read : matchingCycleChildAt out.nm (s.nr 68 + 4*j) = matchingCycleChildAt c.nm (s.nr 68 + 4*j) := by
        apply matchingCycleChildAt_congr
        intro p hp
        have lower : s.nr 68 + 4*j + p < c.nr 68 := by rw [cCursor]; omega
        exact (rightDone.earlier _ (by rw [dCursor]; rw [cCursor] at lower; omega)).trans (beforeCenter _ lower)
      rw [read, ← bCursor]
      change matchingCycleChildAt c.nm (b.nr 68 + 4*j) = _
      refine encoded.trans ?_
      exact cycleSideRecord_unchanged false safety inside (fun r safe => bFrame r (by simp at safe ⊢; omega)) bMemory
    · change matchingCycleChildAt out.nm _ = _
      rw [← cCursor]
      have read : matchingCycleChildAt out.nm (c.nr 68) = matchingCycleChildAt d.nm (c.nr 68) := by
        apply matchingCycleChildAt_congr
        intro p hp
        exact rightDone.earlier _ (by rw [cCursor, dCursor]; omega)
      rw [read]
      change matchingCycleChildAt center.nm _ = _
      rw [centerNat, matchingCycleChildAt_write]
      exact commonCycleRecord_unchanged safety (fun r inside => cFrame r (by simp at inside ⊢; omega)) cMemory
    · intro j inside
      change matchingCycleChildAt out.nm _ = _
      have physical : s.nr 68 + 4 * (s.nr 13 + 1 + j) = d.nr 68 + 4*j := by rw [dCursor]; omega
      rw [physical]
      have atRight : j < d.nr 14 := by rwa [dRight]
      exact (rightDone.records j atRight dSafe).trans
        (cycleSideRecord_unchanged true safety inside dFrame dMemory)



end VehicleRoutingSurvey.Routing
end RppSource_MatchingCycleSequence

open VehicleRoutingSurvey.Routing SupplyChainTheory in
theorem solution : (fun {P : Prop} (_ : P) => P) (@VehicleRoutingSurvey.Routing.writeMatchingContractionCycle_spec) :=
  @VehicleRoutingSurvey.Routing.writeMatchingContractionCycle_spec
