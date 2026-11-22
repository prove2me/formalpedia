-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.matchingContractionHandlerBlock_runs
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T16:02:57.277412+00:00
-- url     : https://prove2.me/submissions/a25272c7-0ce6-4312-a8bb-8b8cc1b9afcd

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces
import Theorems.Thm_VehicleRoutingSurvey_Routing_matchingContractionStructure_spec

/-! matching/WeightedCacheRAM.lean -/
section RppSource_WeightedCacheRAM
namespace VehicleRoutingSurvey.Routing



def mergeSlackEntryTakesCandidate (s : ArithmeticState) : Prop :=
  s.nr 0 ≠ 0 ∧ (s.nr 1 = 0 ∨ s.rr 0 < s.rr 1)

private theorem mergeSlackEntryBlock_absent (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (absent : s.nr 0 = 0) :
    (arithmeticStep mergeSlackEntryBlock)^[2] s = {s with pc := 7, nr := Function.update s.nr 2 0} := by
  simp [mergeSlackEntryBlock, arithmeticStep, Function.iterate_succ_apply', entry, running, absent]

private theorem mergeSlackEntryBlock_empty (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (available : s.nr 0 ≠ 0) (empty : s.nr 1 = 0) :
    (arithmeticStep mergeSlackEntryBlock)^[6] s =
      {s with
        pc := 7
        nr := Function.update (Function.update s.nr 2 0) 1 (s.nr 0)
        rr := Function.update (Function.update s.rr 2 0) 1 (s.rr 0)} := by
  simp [mergeSlackEntryBlock, arithmeticStep, Function.iterate_succ_apply', entry, running, available, empty]

private theorem mergeSlackEntryBlock_keep (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (available : s.nr 0 ≠ 0) (occupied : s.nr 1 ≠ 0)
    (noBetter : s.rr 1 ≤ s.rr 0) :
    (arithmeticStep mergeSlackEntryBlock)^[4] s = {s with pc := 7, nr := Function.update s.nr 2 0} := by
  simp [mergeSlackEntryBlock, arithmeticStep, Function.iterate_succ_apply', entry, running, available, occupied,
    noBetter]

private theorem mergeSlackEntryBlock_replace (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (available : s.nr 0 ≠ 0) (occupied : s.nr 1 ≠ 0)
    (better : s.rr 0 < s.rr 1) :
    (arithmeticStep mergeSlackEntryBlock)^[7] s =
      {s with
        pc := 7
        nr := Function.update (Function.update s.nr 2 0) 1 (s.nr 0)
        rr := Function.update (Function.update s.rr 2 0) 1 (s.rr 0)} := by
  simp [mergeSlackEntryBlock, arithmeticStep, Function.iterate_succ_apply', entry, running, available, occupied,
    not_le.mpr better]

/-- One cache comparison uses at most seven instructions, with the remaining memory intact. -/
theorem mergeSlackEntryBlock_spec (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ steps ≤ 7, let result := (arithmeticStep mergeSlackEntryBlock)^[steps] s
      BlockRuns mergeSlackEntryBlock steps s result ∧
      (mergeSlackEntryTakesCandidate s → result.nr 1 = s.nr 0 ∧ result.rr 1 = s.rr 0) ∧
      (¬ mergeSlackEntryTakesCandidate s → result.nr 1 = s.nr 1 ∧ result.rr 1 = s.rr 1) ∧
      result.nm = s.nm ∧ result.rm = s.rm := by
  classical
  by_cases absent : s.nr 0 = 0
  · refine ⟨2, by decide, ?_⟩
    rw [mergeSlackEntryBlock_absent s entry running absent]
    exact ⟨BlockRuns.of_running_exit (mergeSlackEntryBlock_absent s entry running absent) running rfl,
      by simp [mergeSlackEntryTakesCandidate, absent]⟩
  by_cases empty : s.nr 1 = 0
  · refine ⟨6, by decide, ?_⟩
    rw [mergeSlackEntryBlock_empty s entry running absent empty]
    exact ⟨BlockRuns.of_running_exit (mergeSlackEntryBlock_empty s entry running absent empty) running rfl,
      by simp [mergeSlackEntryTakesCandidate, absent, empty]⟩
  by_cases better : s.rr 0 < s.rr 1
  · refine ⟨7, by decide, ?_⟩
    rw [mergeSlackEntryBlock_replace s entry running absent empty better]
    exact ⟨BlockRuns.of_running_exit (mergeSlackEntryBlock_replace s entry running absent empty better) running rfl,
      by simp [mergeSlackEntryTakesCandidate, absent, empty, better]⟩
  · refine ⟨4, by decide, ?_⟩
    rw [mergeSlackEntryBlock_keep s entry running absent empty (le_of_not_gt better)]
    exact ⟨BlockRuns.of_running_exit (mergeSlackEntryBlock_keep s entry running absent empty (le_of_not_gt better)) running rfl,
      by simp [mergeSlackEntryTakesCandidate, absent, empty, better]⟩

end VehicleRoutingSurvey.Routing
end RppSource_WeightedCacheRAM

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

theorem arithmeticRun_keeps_high_register {p : List ArithmeticInstruction}
    {r : ℕ} (lowWrites : ∀ ins ∈ p, naturalDestination ins < r) (s : ArithmeticState) (steps : ℕ) :
    ((arithmeticStep p)^[steps] s).nr r = s.nr r := by
  exact arithmeticRun_keeps_register (fun ins h => (lowWrites ins h).ne) s steps

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

def realDestination : ArithmeticInstruction → ℕ
  | .realConst dst _ | .realAdd dst _ _ | .realSub dst _ _ | .realMul dst _ _
  | .realDiv dst _ _ | .realLoad dst _ => dst
  | _ => 0

private theorem arithmeticStep_keeps_real_register {p : List ArithmeticInstruction}
    {s : ArithmeticState} {r : ℕ} (otherWrites : ∀ ins ∈ p, realDestination ins ≠ r) :
    (arithmeticStep p s).rr r = s.rr r := by
  by_cases halted : s.halted = true
  · simp [arithmeticStep, halted]
  cases fetch : p[s.pc]? with
  | none => simp [arithmeticStep, halted, fetch]
  | some ins =>
    have writes := otherWrites ins (List.mem_of_getElem? fetch)
    cases ins <;> simp (disch := omega) [arithmeticStep, halted, fetch, realDestination] at writes ⊢

theorem arithmeticRun_keeps_real_from_destination_list {p : List ArithmeticInstruction} {r : ℕ}
    (written : List ℕ) (checked : p.all (fun ins => decide (realDestination ins ∈ written)) = true)
    (away : r ∉ written) (s : ArithmeticState) (steps : ℕ) :
    ((arithmeticStep p)^[steps] s).rr r = s.rr r := by
  have avoids : ∀ ins ∈ p, realDestination ins ≠ r := by
    intro ins present same
    apply away
    exact same ▸ of_decide_eq_true (List.all_eq_true.mp checked ins present)
  induction steps with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', arithmeticStep_keeps_real_register avoids, ih]











theorem no_halt_from_running {p : List ArithmeticInstruction} {s : ArithmeticState} {steps : ℕ}
    (running : s.halted = false) (safe : ∀ k < steps, ((arithmeticStep p)^[k] s).pc < p.length)
    (notHalt : ArithmeticInstruction.halt ∉ p) : ((arithmeticStep p)^[steps] s).halted = false := by
  induction steps with
  | zero => exact running
  | succ k ih =>
    let before := (arithmeticStep p)^[k] s
    have entry : before.pc < p.length := safe k (Nat.lt_succ_self k)
    have live : before.halted = false := ih (fun j earlier => safe j (earlier.trans (Nat.lt_succ_self k)))
    have fetch : p[before.pc]? = some p[before.pc] := List.getElem?_eq_getElem entry
    have selected : p[before.pc] ∈ p := List.getElem_mem entry
    rw [Function.iterate_succ_apply']
    change (arithmeticStep p before).halted = false
    generalize eq : p[before.pc] = instr at fetch selected
    cases instr <;> simp [arithmeticStep, live, fetch, notHalt] at selected ⊢

















end VehicleRoutingSurvey.Routing
end RppSource_WeightedReadDeltaRAM

/-! matching/MatchingCacheWriteRAM.lean -/
section RppSource_MatchingCacheWriteRAM
namespace VehicleRoutingSurvey.Routing



def installedMatchingCandidateNat (s : ArithmeticState) : ℕ → ℕ :=
  let slot := s.nr 18
  let position := s.nr 54 + (slot + slot)
  let identifier := Function.update s.nm (s.nr 58 + slot) (slot + 1)
  Function.update (Function.update identifier position (s.nr 15)) (position + 1) (s.nr 16)

def installedMatchingCandidateReal (s : ArithmeticState) : ℕ → ℝ :=
  let slot := s.nr 18
  Function.update (Function.update s.rm (s.nr 59 + slot) (s.rr 0)) (s.nr 60 + slot) (s.rr 4)

theorem storeMatchingCandidateCell_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    let t := (arithmeticStep storeMatchingCandidateCell)^[12] s
    BlockRuns storeMatchingCandidateCell 12 s t ∧ t.halted = false ∧
      t.nm = installedMatchingCandidateNat s ∧ t.rm = installedMatchingCandidateReal s := by
  let t := (arithmeticStep storeMatchingCandidateCell)^[12] s
  have effect : t.pc = storeMatchingCandidateCell.length ∧ t.halted = false ∧
      t.nm = installedMatchingCandidateNat s ∧ t.rm = installedMatchingCandidateReal s := by
    simp [t, arithmeticStep, storeMatchingCandidateCell, Function.iterate_succ_apply', entry, running, one,
      installedMatchingCandidateNat, installedMatchingCandidateReal]
  exact ⟨BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2⟩







def matchingCandidateImproves (s : ArithmeticState) : Prop :=
  s.nm (s.nr 58 + s.nr 18) = 0 ∨ s.rr 0 < s.rm (s.nr 59 + s.nr 18)

private theorem improveMatchingCandidate_write {s ready : ArithmeticState} {steps : ℕ}
    (prefixRun : (arithmeticStep improveMatchingCandidateBlock)^[steps] s = relocateState 7 ready)
    (entry : ready.pc = 0) (running : ready.halted = false) (one : ready.nr 9 = 1) :
    ∃ t, BlockRuns improveMatchingCandidateBlock (steps + 12) s t ∧ t.halted = false ∧
      t.nm = installedMatchingCandidateNat ready ∧ t.rm = installedMatchingCandidateReal ready := by
  let last := (arithmeticStep storeMatchingCandidateCell)^[12] ready
  obtain ⟨run, live, natEffect, realEffect⟩ := storeMatchingCandidateCell_spec ready entry running one
  have wrote : (arithmeticStep improveMatchingCandidateBlock)^[12] (relocateState 7 ready) = relocateState 7 last := by
    have shifted := arithmeticIterate_relocate compareMatchingCacheCandidate storeMatchingCandidateCell [] ready 12 run.inside
    rw [List.append_nil] at shifted
    exact shifted
  have complete : (arithmeticStep improveMatchingCandidateBlock)^[steps + 12] s = relocateState 7 last := by
    rw [Nat.add_comm steps 12, Function.iterate_add_apply, prefixRun, wrote]
  have exitLast : last.pc = storeMatchingCandidateCell.length := run.exit
  have exits : (relocateState 7 last).pc = improveMatchingCandidateBlock.length := by
    simp [relocateState, exitLast, improveMatchingCandidateBlock, compareMatchingCacheCandidate]
  exact ⟨_, BlockRuns.of_running_exit complete live exits, live, natEffect, realEffect⟩

/-- Replace an empty cache entry or one with larger slack, preserving the earlier entry on
ties. The comparison and all necessary stores take at most nineteen instructions. -/
theorem improveMatchingCandidateBlock_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ result steps, steps ≤ 19 ∧ BlockRuns improveMatchingCandidateBlock steps s result ∧ result.halted = false ∧
      (matchingCandidateImproves s → result.nm = installedMatchingCandidateNat s ∧ result.rm = installedMatchingCandidateReal s) ∧
      (¬matchingCandidateImproves s → result.nm = s.nm ∧ result.rm = s.rm) ∧
      ∀ r ≥ 15, result.nr r = s.nr r := by
  let read := {s with
    pc := 0
    nr := Function.update (Function.update (Function.update s.nr 6 (s.nr 58 + s.nr 18))
      10 (s.nm (s.nr 58 + s.nr 18))) 11 0}
  let compared := {read with
    nr := Function.update read.nr 6 (s.nr 59 + s.nr 18)
    rr := Function.update read.rr 2 (s.rm (s.nr 59 + s.nr 18))}
  have fixed {t : ArithmeticState} {steps : ℕ} (ran : BlockRuns improveMatchingCandidateBlock steps s t) :
      ∀ r ≥ 15, t.nr r = s.nr r := by
    intro r high
    have writes : ∀ ins ∈ improveMatchingCandidateBlock, naturalDestination ins < r := by
      simp [improveMatchingCandidateBlock, appendBlock, compareMatchingCacheCandidate,
        storeMatchingCandidateCell, relocateInstruction, naturalDestination] <;> omega
    exact ran.run ▸ arithmeticRun_keeps_high_register writes s steps
  classical
  by_cases absent : s.nm (s.nr 58 + s.nr 18) = 0
  · have first : (arithmeticStep improveMatchingCandidateBlock)^[4] s = relocateState 7 read := by
      simp [improveMatchingCandidateBlock, appendBlock, compareMatchingCacheCandidate, arithmeticStep,
        Function.iterate_succ_apply', read, relocateState, entry, running, absent]
    obtain ⟨out, ran, live, natEffect, realEffect⟩ := improveMatchingCandidate_write first rfl running (by simpa [read] using one)
    refine ⟨out, 16, by decide, ran, live, ?_, ?_, fixed ran⟩
    · intro _
      exact ⟨by simpa [installedMatchingCandidateNat, read] using natEffect,
        by simpa [installedMatchingCandidateReal, read] using realEffect⟩
    · intro refused
      exact (refused (Or.inl absent)).elim
  by_cases better : s.rr 0 < s.rm (s.nr 59 + s.nr 18)
  · have first : (arithmeticStep improveMatchingCandidateBlock)^[7] s = relocateState 7 compared := by
      simp [improveMatchingCandidateBlock, appendBlock, compareMatchingCacheCandidate, arithmeticStep,
        Function.iterate_succ_apply', read, compared, relocateState, entry, running, absent, not_le.mpr better]
    obtain ⟨out, ran, live, natEffect, realEffect⟩ := improveMatchingCandidate_write first rfl running
      (by simpa [read, compared] using one)
    refine ⟨out, 19, le_rfl, ran, live, ?_, ?_, fixed ran⟩
    · intro _
      exact ⟨by simpa [installedMatchingCandidateNat, read, compared] using natEffect,
        by simpa [installedMatchingCandidateReal, read, compared] using realEffect⟩
    · intro refused
      exact (refused (Or.inr better)).elim
  · let out := {compared with pc := 19}
    have trace : (arithmeticStep improveMatchingCandidateBlock)^[7] s = out := by
      simp [improveMatchingCandidateBlock, appendBlock, compareMatchingCacheCandidate, arithmeticStep,
        Function.iterate_succ_apply', out, read, compared, entry, running, absent, le_of_not_gt better]
    have ran : BlockRuns improveMatchingCandidateBlock 7 s out :=
      BlockRuns.of_running_exit trace running (by simp [out, improveMatchingCandidateBlock,
        compareMatchingCacheCandidate, storeMatchingCandidateCell])
    exact ⟨out, 7, by decide, ran, running, fun choose => (choose.elim absent better).elim,
      fun _ => ⟨rfl, rfl⟩, fixed ran⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingCacheWriteRAM

/-! matching/MatchingEdgeSlackRAM.lean -/
section RppSource_MatchingEdgeSlackRAM
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



theorem readExternalSlackBlock_spec (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) :
    let t := (arithmeticStep readExternalSlackBlock)^[11] s
    BlockRuns readExternalSlackBlock 11 s t ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      t.rr 1 = s.rr 1 ∧
      t.rr 0 = s.rm (s.nr 20 + s.nm (s.nr 21 + s.nr 15) + s.nr 16) -
        s.rm (s.nr 62 + s.nr 15) - s.rm (s.nr 62 + s.nr 16) ∧
      ∀ r, r ≠ 6 → r ≠ 10 → t.nr r = s.nr r := by
  let t := (arithmeticStep readExternalSlackBlock)^[11] s
  have live : t.halted = false := by
    simp [t, arithmeticStep, readExternalSlackBlock, Function.iterate_succ_apply', entry, running]
  have exit : t.pc = readExternalSlackBlock.length := by
    simp [t, arithmeticStep, readExternalSlackBlock, Function.iterate_succ_apply', entry, running]
  refine ⟨BlockRuns.of_running_exit rfl live exit, live, ?_, ?_, ?_, ?_, ?_⟩
  · simp [t, arithmeticStep, readExternalSlackBlock, Function.iterate_succ_apply', entry, running]
  · simp [t, arithmeticStep, readExternalSlackBlock, Function.iterate_succ_apply', entry, running]
  · simp [t, arithmeticStep, readExternalSlackBlock, Function.iterate_succ_apply', entry, running]
  · simp [t, arithmeticStep, readExternalSlackBlock, Function.iterate_succ_apply', entry, running]
  · intro r not6 not10
    simp [t, arithmeticStep, readExternalSlackBlock, Function.iterate_succ_apply', entry, running, not6, not10]



end VehicleRoutingSurvey.Routing
end RppSource_MatchingEdgeSlackRAM

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

/-! matching/MatchingPairBucketRAM.lean -/
section RppSource_MatchingPairBucketRAM
namespace VehicleRoutingSurvey.Routing



def matchingPairBucketAddress (s : ArithmeticState) : ℕ := s.nr 65 + (s.nr 18 + s.nr 18)

def matchingPairBucketImproves (s : ArithmeticState) : Prop :=
  s.nr 55 ≤ s.nm (matchingPairBucketAddress s) ∨ s.rr 5 < s.rm (s.nr 66 + s.nr 18)

def installedMatchingPairBucketNat (s : ArithmeticState) : ℕ → ℕ :=
  Function.update (Function.update s.nm (matchingPairBucketAddress s) (s.nr 15))
    (matchingPairBucketAddress s + 1) (s.nr 16)

def installedMatchingPairBucketReal (s : ArithmeticState) : ℕ → ℝ :=
  Function.update s.rm (s.nr 66 + s.nr 18) (s.rr 5)

/-- Keep the least normalized slack in the selected outer-block pair bucket. The first
endpoint equal to the compact vertex count is the empty sentinel. -/
theorem improveMatchingPairBucketCell_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ result steps, steps ≤ 12 ∧ BlockRuns improveMatchingPairBucketCell steps s result ∧
      result.halted = false ∧
      (matchingPairBucketImproves s → result.nm = installedMatchingPairBucketNat s ∧ result.rm = installedMatchingPairBucketReal s) ∧
      (¬matchingPairBucketImproves s → result.nm = s.nm ∧ result.rm = s.rm) ∧
      ∀ r ≥ 15, result.nr r = s.nr r := by
  have fixed {steps : ℕ} (r : ℕ) (high : 15 ≤ r) :
      ((arithmeticStep improveMatchingPairBucketCell)^[steps] s).nr r = s.nr r :=
    arithmeticRun_keeps_high_register (by
      simp [improveMatchingPairBucketCell, naturalDestination] <;> omega) s steps
  classical
  by_cases absent : s.nr 55 ≤ s.nm (s.nr 65 + (s.nr 18 + s.nr 18))
  · let t := (arithmeticStep improveMatchingPairBucketCell)^[9] s
    have effect : t.pc = improveMatchingPairBucketCell.length ∧ t.halted = false ∧
        t.nm = installedMatchingPairBucketNat s ∧ t.rm = installedMatchingPairBucketReal s := by
      simp [t, arithmeticStep, improveMatchingPairBucketCell, Function.iterate_succ_apply', entry, running,
        one, absent, installedMatchingPairBucketNat, installedMatchingPairBucketReal, matchingPairBucketAddress]
    refine ⟨t, 9, by decide, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1, fun _ => effect.2.2,
      ?_, fixed⟩
    intro refuses
    exact (refuses (Or.inl absent)).elim
  by_cases better : s.rr 5 < s.rm (s.nr 66 + s.nr 18)
  · let t := (arithmeticStep improveMatchingPairBucketCell)^[12] s
    have effect : t.pc = improveMatchingPairBucketCell.length ∧ t.halted = false ∧
        t.nm = installedMatchingPairBucketNat s ∧ t.rm = installedMatchingPairBucketReal s := by
      simp [t, arithmeticStep, improveMatchingPairBucketCell, Function.iterate_succ_apply', entry, running,
        one, absent, not_le.mpr better, installedMatchingPairBucketNat, installedMatchingPairBucketReal,
        matchingPairBucketAddress]
    refine ⟨t, 12, le_rfl, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1, fun _ => effect.2.2,
      ?_, fixed⟩
    intro refuses
    exact (refuses (Or.inr better)).elim
  · let t := (arithmeticStep improveMatchingPairBucketCell)^[7] s
    have effect : t.pc = improveMatchingPairBucketCell.length ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm := by
      simp [t, arithmeticStep, improveMatchingPairBucketCell, Function.iterate_succ_apply', entry, running,
        absent, le_of_not_gt better]
    refine ⟨t, 7, by decide, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1, ?_,
      fun _ => effect.2.2, fixed⟩
    intro chooses
    exact (chooses.elim absent better).elim

end VehicleRoutingSurvey.Routing
end RppSource_MatchingPairBucketRAM

/-! matching/MatchingGrowCacheRAM.lean -/
section RppSource_MatchingGrowCacheRAM
namespace VehicleRoutingSurvey.Routing

attribute [local simp] List.forall_mem_append List.forall_mem_map
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000





















structure CacheMemoryFrame (s t : ArithmeticState) : Prop where
  natural : ∀ a < s.nr 58, t.nm a = s.nm a
  real : ∀ a < s.nr 59, s.nr 59 ≤ s.nr 60 → s.nr 59 ≤ s.nr 66 → t.rm a = s.rm a

private def CacheBlockBounded (code : List ArithmeticInstruction) (cap : ℕ) : Prop :=
  ∀ s : ArithmeticState, s.pc = 0 → s.halted = false → s.nr 9 = 1 →
    s.nr 58 ≤ s.nr 54 → s.nr 58 ≤ s.nr 65 →
    ∃ t steps, steps ≤ cap ∧ BlockRuns code steps s t ∧ t.halted = false ∧ CacheMemoryFrame s t

private theorem CacheBlockBounded.append {a b : List ArithmeticInstruction} {m n : ℕ}
    (left : CacheBlockBounded a m) (right : CacheBlockBounded b n)
    (fixed : a.all (fun i => decide (naturalDestination i ∉ [9, 54, 58, 59, 60, 65, 66])) = true) :
    CacheBlockBounded (appendBlock a b) (m + n) := by
  intro s entry running one dict bucket
  obtain ⟨u, steps, small, first, live, prior⟩ := left s entry running one dict bucket
  have kept (r : ℕ) (base : r ∈ [9, 54, 58, 59, 60, 65, 66]) : u.nr r = s.nr r := by
    rw [← first.run]
    apply arithmeticRun_keeps_register _ s steps
    intro i hi same
    have cannot : naturalDestination i ∉ [9, 54, 58, 59, 60, 65, 66] :=
      of_decide_eq_true (List.all_eq_true.mp fixed i hi)
    exact cannot (same.symm ▸ base)
  have oneAgain : u.nr 9 = 1 := (kept 9 (by decide)).trans one
  have floor : u.nr 58 = s.nr 58 := kept 58 (by decide)
  have dictAgain : u.nr 58 ≤ u.nr 54 := by simpa [floor, kept 54 (by decide)] using dict
  have bucketAgain : u.nr 58 ≤ u.nr 65 := by simpa [floor, kept 65 (by decide)] using bucket
  obtain ⟨t, ticks, bounded, second, stillLive, following⟩ :=
    right {u with pc := 0} rfl live oneAgain dictAgain bucketAgain
  refine ⟨_, steps + ticks, Nat.add_le_add small bounded, first.append second, stillLive, ?_, ?_⟩
  · intro i before
    exact (following.natural i (floor.symm ▸ before)).trans (prior.natural i before)
  · intro i before rate pairScore
    have scoreFloor : u.nr 59 = s.nr 59 := kept 59 (by decide)
    have rateAgain : u.nr 59 ≤ u.nr 60 := by simpa [scoreFloor, kept 60 (by decide)] using rate
    have pairAgain : u.nr 59 ≤ u.nr 66 := by simpa [scoreFloor, kept 66 (by decide)] using pairScore
    exact (following.real i (scoreFloor.symm ▸ before) rateAgain pairAgain).trans (prior.real i before rate pairScore)

private theorem CacheBlockBounded.branch {left right : List ArithmeticInstruction} {l r : ℕ}
    (x y : ℕ) (leftBound : CacheBlockBounded left l) (rightBound : CacheBlockBounded right r) :
    CacheBlockBounded (branchOnAtMost x y left right) (max l r + 2) := by
  intro s entry running one dict bucket
  by_cases pickLeft : s.nr x ≤ s.nr y
  · obtain ⟨t, steps, short, run, live, prior⟩ := leftBound s entry running one dict bucket
    have bound := le_max_left l r
    exact ⟨_, 1 + steps + 1, by omega, branchOnAtMost_left x y left right entry running pickLeft run live,
      live, prior.natural, prior.real⟩
  · obtain ⟨t, steps, short, run, live, prior⟩ := rightBound s entry running one dict bucket
    have bound := le_max_right l r
    exact ⟨_, 1 + steps, by omega, branchOnAtMost_right x y left right entry running
      (Nat.lt_of_not_ge pickLeft) run live, live, prior.natural, prior.real⟩

private theorem CacheBlockBounded.unlessEqual {body : List ArithmeticInstruction} {n : ℕ}
    (x y : ℕ) (bound : CacheBlockBounded body n) :
    CacheBlockBounded (branchOnUnequal x y body) (2 + n) := by
  intro s entry running one dict bucket
  by_cases same : s.nr x = s.nr y
  · exact ⟨_, 2, by omega, branchOnUnequal_skip x y body s entry running same, running,
      fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  · obtain ⟨t, steps, short, run, live, prior⟩ := bound s entry running one dict bucket
    exact ⟨_, 2 + steps, by omega, branchOnUnequal_take x y body entry running same run,
      live, prior.natural, prior.real⟩

private theorem readGrowthCacheNeighbor_bound : CacheBlockBounded readGrowthCacheNeighbor 5 := by
  intro s entry running _ _ _
  let t := (arithmeticStep readGrowthCacheNeighbor)^[5] s
  have exit : t.pc = readGrowthCacheNeighbor.length ∧ t.halted = false := by
    simp [t, arithmeticStep, Function.iterate_succ_apply', readGrowthCacheNeighbor, entry, running]
  refine ⟨t, 5, le_rfl, BlockRuns.of_running_exit rfl exit.2 exit.1, exit.2, ?_, ?_⟩ <;>
    (intros; simp [t, arithmeticStep, Function.iterate_succ_apply', readGrowthCacheNeighbor, entry, running])

private theorem growIncomingArgs_bound (rate : ℚ) : CacheBlockBounded (growIncomingArgs rate) 2 := by
  intro s entry running _ _ _
  let t := (arithmeticStep (growIncomingArgs rate))^[2] s
  have exit : t.pc = (growIncomingArgs rate).length ∧ t.halted = false := by
    simp [t, arithmeticStep, Function.iterate_succ_apply', growIncomingArgs, entry, running]
  refine ⟨t, 2, le_rfl, BlockRuns.of_running_exit rfl exit.2 exit.1, exit.2, ?_, ?_⟩ <;>
    (intros; simp [t, arithmeticStep, Function.iterate_succ_apply', growIncomingArgs, entry, running])

private theorem improveMatchingCandidate_bound : CacheBlockBounded improveMatchingCandidateBlock 19 := by
  intro s entry running one dict _
  obtain ⟨t, steps, bound, run, live, write, ignore, _⟩ := improveMatchingCandidateBlock_spec s entry running one
  refine ⟨t, steps, bound, run, live, ?_, ?_⟩
  · intro a before
    by_cases better : matchingCandidateImproves s
    · rw [(write better).1]
      simp (disch := omega) [installedMatchingCandidateNat, Function.update_of_ne]
    · rw [(ignore better).1]
  · intro a before rates _
    by_cases better : matchingCandidateImproves s
    · rw [(write better).2]
      simp (disch := omega) [installedMatchingCandidateReal, Function.update_of_ne]
    · rw [(ignore better).2]

private theorem improveMatchingPairBucket_bound : CacheBlockBounded improveMatchingPairBucketCell 12 := by
  intro s entry running one _ bucket
  obtain ⟨t, steps, bound, run, live, write, ignore, _⟩ := improveMatchingPairBucketCell_spec s entry running one
  refine ⟨t, steps, bound, run, live, ?_, ?_⟩
  · intro a before
    by_cases better : matchingPairBucketImproves s
    · rw [(write better).1]
      simp (disch := omega) [installedMatchingPairBucketNat, matchingPairBucketAddress, Function.update_of_ne]
    · rw [(ignore better).1]
  · intro a before _ pairScore
    by_cases better : matchingPairBucketImproves s
    · rw [(write better).2]
      simp (disch := omega) [installedMatchingPairBucketReal, Function.update_of_ne]
    · rw [(ignore better).2]

private theorem growIncomingCache_bound (rate : ℚ) : CacheBlockBounded (growIncomingCache rate) 21 :=
  CacheBlockBounded.append (growIncomingArgs_bound rate) improveMatchingCandidate_bound rfl

private theorem normalizeGrowthSlack_bound : CacheBlockBounded normalizeGrowthSlack 3 := by
  intro s entry running _ _ _
  let t := (arithmeticStep normalizeGrowthSlack)^[3] s
  have exit : t.pc = normalizeGrowthSlack.length ∧ t.halted = false := by
    simp [t, arithmeticStep, Function.iterate_succ_apply', normalizeGrowthSlack, entry, running]
  refine ⟨t, 3, le_rfl, BlockRuns.of_running_exit rfl exit.2 exit.1, exit.2, ?_, ?_⟩ <;>
    (intros; simp [t, arithmeticStep, Function.iterate_succ_apply', normalizeGrowthSlack, entry, running])

private theorem growBucketArgs_bound (source target : ℕ) : CacheBlockBounded (growBucketArgs source target) 3 := by
  intro s entry running _ _ _
  let t := (arithmeticStep (growBucketArgs source target))^[3] s
  have exit : t.pc = (growBucketArgs source target).length ∧ t.halted = false := by
    simp [t, arithmeticStep, Function.iterate_succ_apply', growBucketArgs, entry, running]
  refine ⟨t, 3, le_rfl, BlockRuns.of_running_exit rfl exit.2 exit.1, exit.2, ?_, ?_⟩ <;>
    (intros; simp [t, arithmeticStep, Function.iterate_succ_apply', growBucketArgs, entry, running])

private theorem growOuterRowArgs_bound (source : ℕ) : CacheBlockBounded (growOuterRowArgs source) 1 := by
  intro s entry running _ _ _
  let t := arithmeticStep (growOuterRowArgs source) s
  have exit : t.pc = (growOuterRowArgs source).length ∧ t.halted = false := by
    simp [t, arithmeticStep, growOuterRowArgs, entry, running]
  refine ⟨t, 1, le_rfl, BlockRuns.of_running_exit rfl exit.2 exit.1, exit.2, ?_, ?_⟩ <;>
    (intros; simp [t, arithmeticStep, growOuterRowArgs, entry, running])

private theorem growOuterCacheSide_bound (source target : ℕ) :
    CacheBlockBounded (growOuterCacheSide source target) 35 :=
  CacheBlockBounded.append
    (CacheBlockBounded.append (growBucketArgs_bound source target) improveMatchingPairBucket_bound rfl)
    (CacheBlockBounded.append (growOuterRowArgs_bound source) improveMatchingCandidate_bound rfl)
    rfl



private theorem growOuterCache_bound : CacheBlockBounded insertMatchingOuterEdgeBlock 73 := by
  exact CacheBlockBounded.append (m := 3) (n := 70) normalizeGrowthSlack_bound
    (CacheBlockBounded.append (growOuterCacheSide_bound 26 17) (growOuterCacheSide_bound 17 26) rfl) rfl



theorem insertMatchingOuterEdgeBlock_frames (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ t steps, steps ≤ 73 ∧ BlockRuns insertMatchingOuterEdgeBlock steps s t ∧ t.halted = false ∧
      (∀ a < s.nr 58, t.nm a = s.nm a) ∧
      ∀ a < s.nr 59, s.nr 59 ≤ s.nr 60 → s.nr 59 ≤ s.nr 66 → t.rm a = s.rm a := by
  obtain ⟨t, steps, cost, run, live, frames⟩ := growOuterCache_bound s entry running one dict bucket
  exact ⟨t, steps, cost, run, live, frames.natural, frames.real⟩

private theorem readExternalSlack_bound : CacheBlockBounded readExternalSlackBlock 11 := by
  intro s entry running _ _ _
  obtain ⟨run, live, natural, real, _⟩ := readExternalSlackBlock_spec s entry running
  exact ⟨_, 11, le_rfl, run, live, fun a _ => congrFun natural a, fun a _ _ _ => congrFun real a⟩

private theorem refreshGrowthNeighborBlock_frames : CacheBlockBounded refreshGrowthNeighborBlock 95 := by
  have chosen : CacheBlockBounded chooseGrowthCache 77 :=
    CacheBlockBounded.branch 19 14 (growIncomingCache_bound 1)
      (CacheBlockBounded.branch 19 9 growOuterCache_bound (growIncomingCache_bound 0))
  have external : CacheBlockBounded (appendBlock readExternalSlackBlock chooseGrowthCache) 88 :=
    CacheBlockBounded.append readExternalSlack_bound chosen rfl
  exact CacheBlockBounded.append readGrowthCacheNeighbor_bound (external.unlessEqual 26 17) rfl





private theorem refreshGrowthNeighbor_no_write {r : ℕ}
    (away : r ∉ [0, 6, 10, 11, 16, 17, 18, 19]) :
    ∀ i ∈ refreshGrowthNeighborBlock, naturalDestination i ≠ r :=
  naturalDestination_ne_of_list [0, 6, 10, 11, 16, 17, 18, 19] (by decide) away



/-- Scan one selected outer original while preserving the earlier natural and real tables. -/
theorem refreshSelectedOuterVertex_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ t steps, steps ≤ s.nr 55 * 98 + 2 ∧ BlockRuns refreshSelectedOuterVertex steps s t ∧
      t.halted = false ∧ (∀ a < s.nr 58, t.nm a = s.nm a) ∧
      ∀ a < s.nr 59, s.nr 59 ≤ s.nr 60 → s.nr 59 ≤ s.nr 66 → t.rm a = s.rm a := by
  let inv (i : ℕ) (m : ArithmeticState) : Prop :=
    m.pc = 0 ∧ m.halted = false ∧ m.nr 25 = i ∧ m.nr 55 = s.nr 55 ∧ m.nr 9 = 1 ∧
    (∀ r ∈ [54, 58, 59, 60, 65, 66], m.nr r = s.nr r) ∧
    (∀ a < s.nr 58, m.nm a = s.nm a) ∧
    ∀ a < s.nr 59, s.nr 59 ≤ s.nr 60 → s.nr 59 ≤ s.nr 66 → m.rm a = s.rm a
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 25 0} := by
    refine ⟨rfl, running, by simp, by simp, by simpa using one, ?_, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    intro r hi
    have other : r ≠ 25 := by simp at hi; omega
    exact Function.update_of_ne other 0 s.nr
  have control (i : ℕ) (m : ArithmeticState) (h : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 25 = i ∧ m.nr 55 = s.nr 55 :=
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  have iteration (i : ℕ) (_ : i < s.nr 55) (m : ArithmeticState) (h : inv i m) :
      ∃ t steps, steps ≤ 95 ∧ BlockRuns refreshGrowthNeighborBlock steps m t ∧ t.halted = false ∧
        inv (i+1) {t with pc := 0, nr := Function.update t.nr 25 (t.nr 25 + t.nr 9)} := by
    obtain ⟨atStart, ready, index, size, unit, keptBases, prior, priorReal⟩ := h
    have mFloor : m.nr 58 = s.nr 58 := keptBases 58 (by decide)
    have mDict : m.nr 58 ≤ m.nr 54 := by simpa [mFloor, keptBases 54 (by decide)] using dict
    have mBucket : m.nr 58 ≤ m.nr 65 := by simpa [mFloor, keptBases 65 (by decide)] using bucket
    obtain ⟨t, steps, short, ran, live, frames⟩ := refreshGrowthNeighborBlock_frames m atStart ready unit mDict mBucket
    have fixed {r : ℕ} (away : r ∉ [0, 6, 10, 11, 16, 17, 18, 19]) :
        t.nr r = m.nr r := by
      rw [← ran.run, arithmeticRun_keeps_register (refreshGrowthNeighbor_no_write away)]
    refine ⟨t, steps, short, ran, live, rfl, live, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [fixed (r := 25) (by decide), fixed (r := 9) (by decide), index, unit]
    · simpa using (fixed (r := 55) (by decide)).trans size
    · simpa using (fixed (r := 9) (by decide)).trans unit
    · intro r base
      have no : r ≠ 25 := by simp at base; omega
      have away : r ∉ [0, 6, 10, 11, 16, 17, 18, 19] := by simp at base ⊢; omega
      exact (Function.update_of_ne no _ _).trans ((fixed away).trans (keptBases r base))
    · intro a before
      exact (frames.natural a (mFloor.symm ▸ before)).trans (prior a before)
    · intro a before rate score
      have mReal : m.nr 59 = s.nr 59 := keptBases 59 (by decide)
      have mRate : m.nr 59 ≤ m.nr 60 := by simpa [mReal, keptBases 60 (by decide)] using rate
      have mScore : m.nr 59 ≤ m.nr 66 := by simpa [mReal, keptBases 66 (by decide)] using score
      exact (frames.real a (mReal.symm ▸ before) mRate mScore).trans (priorReal a before rate score)
  obtain ⟨t, steps, valid, short, ran⟩ := countedLoopFromZero_bounded 9 25 55 (s.nr 55)
    95 refreshGrowthNeighborBlock inv entry running initial control iteration
  obtain ⟨_, ready, _, _, _, _, natural, real⟩ := valid
  exact ⟨_, steps, by omega, ran, ready, natural, real⟩





































end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowCacheRAM

/-! matching/MatchingGrowHandler.lean -/
section RppSource_MatchingGrowHandler
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096











theorem resetMatchingSelector_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 14 = 0) :
    ∃ t, BlockRuns resetMatchingSelector 5 s t ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      t.nr 1 = 0 ∧ t.nr 3 = s.nr 58 ∧ t.nr 4 = s.nr 59 ∧ t.nr 5 = s.nr 60 ∧ t.nr 8 = s.nr 61 := by
  let t := (arithmeticStep resetMatchingSelector)^[5] s
  have live : t.halted = false := by
    simp [t, resetMatchingSelector, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = resetMatchingSelector.length := by
    simp [t, resetMatchingSelector, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl live exit, live, ?_⟩
  simp [t, resetMatchingSelector, arithmeticStep, entry, running, zero, Function.iterate_succ_apply']









end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowHandler

/-! matching/MatchingContractCacheRAM.lean -/
section RppSource_MatchingContractCacheRAM
namespace VehicleRoutingSurvey.Routing

def contractedBucketIndex (s : ArithmeticState) (i : ℕ) : ℕ :=
  s.nm (s.nr 21 + s.nm (s.nr 86 + i)) + s.nr 17

def contractedBucketCode (s : ArithmeticState) (i : ℕ) : ℕ :=
  let slot := contractedBucketIndex s i
  if s.nr 55 ≤ s.nm (s.nr 65 + (slot + slot)) then 0 else slot + 1

def contractedBucketSlack (s : ArithmeticState) (i : ℕ) : ℝ :=
  s.rm (s.nr 66 + contractedBucketIndex s i)



private structure ContractedBucketRead (s t : ArithmeticState) (steps : ℕ) : Prop where
  run : BlockRuns readContractedBucket steps s t
  running : t.halted = false
  candidate : t.nr 0 = contractedBucketCode s (s.nr 7)
  best : t.nr 1 = s.nr 1
  score : t.rr 1 = s.rr 1
  candidateScore : t.nr 0 ≠ 0 → t.rr 0 = contractedBucketSlack s (s.nr 7)
  natural : t.nm = s.nm
  real : t.rm = s.rm

set_option maxRecDepth 4096 in
set_option maxHeartbeats 700000 in
private theorem readContractedBucket_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t steps, steps ≤ 12 ∧ ContractedBucketRead s t steps := by
  let slot := contractedBucketIndex s (s.nr 7)
  by_cases empty : s.nr 55 ≤ s.nm (s.nr 65 + (slot + slot))
  · dsimp [slot, contractedBucketIndex] at empty
    let t := (arithmeticStep readContractedBucket)^[11] s
    have effect : t.pc = readContractedBucket.length ∧ t.halted = false ∧
        t.nr 0 = contractedBucketCode s (s.nr 7) ∧ t.nr 1 = s.nr 1 ∧ t.rr 1 = s.rr 1 ∧
        t.nm = s.nm ∧ t.rm = s.rm := by
      simp [t, arithmeticStep, readContractedBucket, Function.iterate_succ_apply', entry, running,
        contractedBucketCode, contractedBucketIndex, empty]
    refine ⟨t, 11, by decide, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1,
      effect.2.2.1, effect.2.2.2.1, effect.2.2.2.2.1, ?_, effect.2.2.2.2.2.1, effect.2.2.2.2.2.2⟩
    intro available
    exfalso
    apply available
    exact effect.2.2.1.trans (by simp [contractedBucketCode, contractedBucketIndex, empty])
  · dsimp [slot, contractedBucketIndex] at empty
    let t := (arithmeticStep readContractedBucket)^[12] s
    have effect : t.pc = readContractedBucket.length ∧ t.halted = false ∧
        t.nr 0 = contractedBucketCode s (s.nr 7) ∧ t.nr 1 = s.nr 1 ∧ t.rr 1 = s.rr 1 ∧
        t.rr 0 = contractedBucketSlack s (s.nr 7) ∧ t.nm = s.nm ∧ t.rm = s.rm := by
      simp [t, arithmeticStep, readContractedBucket, Function.iterate_succ_apply', entry, running,
        contractedBucketCode, contractedBucketSlack, contractedBucketIndex, empty, one]
    exact ⟨t, 12, le_rfl, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1,
      effect.2.2.1, effect.2.2.2.1, effect.2.2.2.2.1, fun _ => effect.2.2.2.2.2.1,
      effect.2.2.2.2.2.2.1, effect.2.2.2.2.2.2.2⟩



def contractedBucketWins (s : ArithmeticState) : Prop :=
  contractedBucketCode s (s.nr 7) ≠ 0 ∧
    (s.nr 1 = 0 ∨ contractedBucketSlack s (s.nr 7) < s.rr 1)

/-- Compare a single absorbed row with the best normalized key so far, without
copying any endpoints or writing memory. -/
theorem considerContractedBucket_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t steps, steps ≤ 19 ∧ BlockRuns considerContractedBucket steps s t ∧ t.halted = false ∧
      (contractedBucketWins s → t.nr 1 = contractedBucketCode s (s.nr 7) ∧ t.rr 1 = contractedBucketSlack s (s.nr 7)) ∧
      (¬contractedBucketWins s → t.nr 1 = s.nr 1 ∧ t.rr 1 = s.rr 1) ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  obtain ⟨fetched, readTicks, readBound, read⟩ := readContractedBucket_spec s entry running one
  let lookup := {fetched with pc := 0}
  obtain ⟨steps, bound, compared, use, keep, natural, real⟩ := mergeSlackEntryBlock_spec lookup rfl read.running
  have stillRunning := no_halt_from_running (s := lookup) read.running compared.inside (by simp [mergeSlackEntryBlock])
  have chosen : mergeSlackEntryTakesCandidate lookup ↔ contractedBucketWins s := by
    change fetched.nr 0 ≠ 0 ∧ (fetched.nr 1 = 0 ∨ fetched.rr 0 < fetched.rr 1) ↔ _
    by_cases available : fetched.nr 0 = 0
    · simp [available, contractedBucketWins, ← read.candidate]
    · simp [available, contractedBucketWins, ← read.candidate, read.best, read.score, read.candidateScore available]
  refine ⟨_, readTicks + steps, by omega, read.run.append compared, stillRunning, ?_, ?_,
    natural.trans read.natural, real.trans read.real⟩
  · intro accepted
    have pick := chosen.mpr accepted
    have available : fetched.nr 0 ≠ 0 := pick.1
    obtain ⟨selected, value⟩ := use pick
    exact ⟨selected.trans read.candidate, value.trans (read.candidateScore available)⟩
  · intro skipped
    obtain ⟨selected, value⟩ := keep (fun bought => skipped (chosen.mp bought))
    exact ⟨selected.trans read.best, value.trans read.score⟩

def ContractedBucketMinimum (s : ArithmeticState) (seen code : ℕ) (score : ℝ) : Prop :=
  (code = 0 ∧ ∀ i < seen, contractedBucketCode s i = 0) ∨
    ∃ i < seen, contractedBucketCode s i ≠ 0 ∧ code = contractedBucketCode s i ∧
      score = contractedBucketSlack s i ∧
      ∀ j < seen, contractedBucketCode s j ≠ 0 → score ≤ contractedBucketSlack s j

private theorem ContractedBucketMinimum.extend {s : ArithmeticState}
    {i oldCode newCode : ℕ} {oldScore newScore : ℝ}
    (before : ContractedBucketMinimum s i oldCode oldScore)
    (take : contractedBucketCode s i ≠ 0 ∧ (oldCode = 0 ∨ contractedBucketSlack s i < oldScore) →
      newCode = contractedBucketCode s i ∧ newScore = contractedBucketSlack s i)
    (keep : ¬ (contractedBucketCode s i ≠ 0 ∧ (oldCode = 0 ∨ contractedBucketSlack s i < oldScore)) →
      newCode = oldCode ∧ newScore = oldScore) :
    ContractedBucketMinimum s (i + 1) newCode newScore := by
  by_cases replace : contractedBucketCode s i ≠ 0 ∧ (oldCode = 0 ∨ contractedBucketSlack s i < oldScore)
  · obtain ⟨code, score⟩ := take replace
    refine Or.inr ⟨i, by omega, replace.1, code, score, ?_⟩
    intro j hj available
    obtain earlier | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)
    · rcases before with ⟨_, missing⟩ | ⟨p, _, present, sameCode, _, least⟩
      · exact (available (missing j earlier)).elim
      · have better := replace.2.resolve_left (by rwa [sameCode])
        rw [score]
        exact better.le.trans (least j earlier available)
    · exact score.le
  · obtain ⟨rfl, rfl⟩ := keep replace
    rcases before with ⟨empty, missing⟩ | ⟨p, hp, present, code, score, least⟩
    · refine Or.inl ⟨empty, ?_⟩
      intro j hj
      obtain earlier | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)
      · exact missing j earlier
      · exact not_not.mp (fun available => replace ⟨available, Or.inl empty⟩)
    · refine Or.inr ⟨p, by omega, present, code, score, ?_⟩
      intro j hj available
      obtain earlier | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)
      · exact least j earlier available
      · exact le_of_not_gt (fun better => replace ⟨available, Or.inr better⟩)



private structure ContractedColumnScan (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  live : s.halted = false
  index : s.nr 7 = i
  geometry : ∀ r ∈ [9, 17, 21, 55, 65, 66, 86, 87], s.nr r = initial.nr r
  natural : s.nm = initial.nm
  real : s.rm = initial.rm
  minimum : ContractedBucketMinimum initial i (s.nr 1) (s.rr 1)

/-- Inspect one column of the absorbed rows. The cost depends on the absorbed-row
count, and the result names the exact old bucket furnishing the minimum. -/
theorem minimumContractedBucket_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t steps, steps ≤ s.nr 87 * 22 + 3 ∧ BlockRuns minimumContractedBucket steps s t ∧ t.halted = false ∧
      ContractedBucketMinimum s (s.nr 87) (t.nr 1) (t.rr 1) ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  let seeded := {s with pc := 1, nr := Function.update s.nr 1 0}
  have seed : BlockRuns [.natConst 1 0] 1 s seeded := by
    apply BlockRuns.of_running_exit
    · simp [seeded, arithmeticStep, entry, running]
    · exact running
    · rfl
  let start := {seeded with pc := 0}
  have init : ContractedColumnScan s 0 {start with pc := 0, nr := Function.update start.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, rfl, rfl, Or.inl ⟨by simp [start, seeded], fun i less => (Nat.not_lt_zero i less).elim⟩⟩
    intro r hr
    have a : r ≠ 1 := by simp at hr; omega
    have b : r ≠ 7 := by simp at hr; omega
    simp [start, seeded, Function.update_of_ne a, Function.update_of_ne b]
  have iterate (i : ℕ) (_ : i < s.nr 87) (m : ArithmeticState) (inv : ContractedColumnScan s i m) :
      ∃ t steps, steps ≤ 19 ∧ BlockRuns considerContractedBucket steps m t ∧ t.halted = false ∧
        ContractedColumnScan s (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    have mOne : m.nr 9 = 1 := (inv.geometry 9 (by decide)).trans one
    obtain ⟨t, ticks, short, run, live, choose, keep, natural, real⟩ :=
      considerContractedBucket_spec m inv.entry inv.live mOne
    have oldCode : contractedBucketCode m (m.nr 7) = contractedBucketCode s i := by
      have sameSlot : contractedBucketIndex m (m.nr 7) = contractedBucketIndex s i := by
        simp [contractedBucketIndex, inv.natural, inv.index, inv.geometry 17 (by decide),
          inv.geometry 21 (by decide), inv.geometry 86 (by decide)]
      let slot := contractedBucketIndex s i
      by_cases empty : s.nr 55 ≤ s.nm (s.nr 65 + (slot + slot)) <;>
        simp [contractedBucketCode, sameSlot, inv.natural, inv.geometry 55 (by decide),
          inv.geometry 65 (by decide), show contractedBucketIndex s i = slot from rfl, empty]
    have oldScore : contractedBucketSlack m (m.nr 7) = contractedBucketSlack s i := by
      simp [contractedBucketSlack, contractedBucketIndex, inv.natural, inv.real, inv.index,
        inv.geometry 17 (by decide), inv.geometry 21 (by decide), inv.geometry 66 (by decide), inv.geometry 86 (by decide)]
    have stable (r : ℕ) (away : r ∉ [0, 1, 2, 6, 10, 11]) : t.nr r = m.nr r := by
      rw [← run.run]
      apply arithmeticRun_keeps_register _ m ticks
      intro ins belongs same
      have destinations : considerContractedBucket.map naturalDestination =
          [6, 10, 6, 10, 10, 6, 6, 11, 0, 0, 0, 0, 6, 0, 2, 0, 0, 0, 1, 0, 0] := rfl
      have member := List.mem_map_of_mem (f := naturalDestination) belongs
      rw [destinations, same] at member
      simp at member away
      omega
    refine ⟨t, ticks, short, run, live, rfl, live, ?_, ?_, natural.trans inv.natural, real.trans inv.real, ?_⟩
    · simp [stable 7 (by decide), stable 9 (by decide), inv.index, mOne]
    · intro r hr
      have a : r ≠ 7 := by simp at hr; omega
      have b : r ∉ [0, 1, 2, 6, 10, 11] := by simp at hr ⊢; omega
      exact (Function.update_of_ne a _ _).trans ((stable r b).trans (inv.geometry r hr))
    · change ContractedBucketMinimum s (i + 1) (t.nr 1) (t.rr 1)
      exact inv.minimum.extend
        (by simpa only [contractedBucketWins, oldCode, oldScore] using choose)
        (by simpa only [contractedBucketWins, oldCode, oldScore] using keep)
  obtain ⟨last, ticks, done, short, run⟩ := countedLoopFromZero_bounded 9 7 87 (s.nr 87) 19
    considerContractedBucket (ContractedColumnScan s) (s := start) rfl running init
    (fun _ _ h => ⟨h.entry, h.live, h.index, h.geometry 87 (by decide)⟩) iterate
  exact ⟨_, 1 + ticks, by omega, seed.append run, done.live, done.minimum, done.natural, done.real⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractCacheRAM

/-! matching/MatchingContractPublish.lean -/
section RppSource_MatchingContractPublish
namespace VehicleRoutingSurvey.Routing





theorem readMinimumContractedBucket_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns readMinimumContractedBucket 8 s t ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      t.nr 15 = s.nm (s.nr 65 + ((s.nr 1 - 1) + (s.nr 1 - 1))) ∧
      t.nr 16 = s.nm (s.nr 65 + ((s.nr 1 - 1) + (s.nr 1 - 1)) + 1) ∧
      t.rr 0 = s.rr 1 - (s.rr 15 + s.rr 15) ∧ t.rr 15 = s.rr 15 ∧
      ∀ r, r ∉ [0, 6, 15, 16, 18] → t.nr r = s.nr r := by
  let t := (arithmeticStep readMinimumContractedBucket)^[8] s
  have effect : t.pc = readMinimumContractedBucket.length ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      t.nr 15 = s.nm (s.nr 65 + ((s.nr 1 - 1) + (s.nr 1 - 1))) ∧
      t.nr 16 = s.nm (s.nr 65 + ((s.nr 1 - 1) + (s.nr 1 - 1)) + 1) ∧
      t.rr 0 = s.rr 1 - (s.rr 15 + s.rr 15) ∧ t.rr 15 = s.rr 15 := by
    simp [t, readMinimumContractedBucket, arithmeticStep, entry, running, one, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1,
    effect.2.2.1, effect.2.2.2.1, effect.2.2.2.2.1, effect.2.2.2.2.2.1,
    effect.2.2.2.2.2.2.1, effect.2.2.2.2.2.2.2, ?_⟩
  intro r away
  apply arithmeticRun_keeps_register
  simp [readMinimumContractedBucket, naturalDestination] at away ⊢ <;> omega

theorem publishMinimumContractedBucket_bound (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ t steps, steps ≤ 85 ∧ BlockRuns publishMinimumContractedBucket steps s t ∧ t.halted = false ∧
      (∀ a < s.nr 58, t.nm a = s.nm a) ∧
      ∀ a < s.nr 59, s.nr 59 ≤ s.nr 60 → s.nr 59 ≤ s.nr 66 → t.rm a = s.rm a := by
  let seeded := {s with pc := 2, nr := Function.update (Function.update s.nr 23 0) 14 0}
  have seed : BlockRuns [.natConst 23 0, .natConst 14 0] 2 s seeded := by
    apply BlockRuns.of_running_exit
    · simp [seeded, arithmeticStep, entry, running, Function.iterate_succ_apply']
    · exact running
    · rfl
  let a := {seeded with pc := 0}
  have aOne : a.nr 9 = 1 := by simpa [a, seeded] using one
  have aId : a.nr 1 = s.nr 1 := by simp [a, seeded]
  have zero : a.nr 23 = 0 := by simp [a, seeded]
  let body := appendBlock readMinimumContractedBucket insertMatchingOuterEdgeBlock
  by_cases absent : s.nr 1 = 0
  · have skip := branchOnUnequal_skip 1 23 body a rfl running (aId.trans (absent.trans zero.symm))
    exact ⟨_, 4, by decide, seed.append skip, running, (fun _ _ => rfl), fun _ _ _ _ => rfl⟩
  obtain ⟨middle, fetched, live, natural, real, _, _, _, _, frame⟩ := readMinimumContractedBucket_spec a rfl running aOne
  let b := {middle with pc := 0}
  have bFloor : b.nr 58 = s.nr 58 := by simpa [a, seeded] using frame 58 (by decide)
  have b54 : b.nr 54 = s.nr 54 := (frame 54 (by decide)).trans (by simp [a, seeded])
  have b65 : b.nr 65 = s.nr 65 := (frame 65 (by decide)).trans (by simp [a, seeded])
  have bDict : b.nr 58 ≤ b.nr 54 := by rwa [bFloor, b54]
  have bBucket : b.nr 58 ≤ b.nr 65 := by rwa [bFloor, b65]
  have bOne : b.nr 9 = 1 := (frame 9 (by decide)).trans aOne
  obtain ⟨out, steps, short, wrote, ready, keepsMemory, keepsReal⟩ :=
    insertMatchingOuterEdgeBlock_frames b rfl live bOne bDict bBucket
  have different : a.nr 1 ≠ a.nr 23 := by simpa only [aId, zero] using absent
  have took := branchOnUnequal_take 1 23 body (s := a) rfl running different (fetched.append wrote)
  refine ⟨_, 2 + (2 + (8 + steps)), by omega, seed.append took, ready, ?_, ?_⟩
  · intro i before
    exact (keepsMemory i (bFloor.symm ▸ before)).trans (congrFun natural i)
  · intro i before rate score
    have b59 : b.nr 59 = s.nr 59 := (frame 59 (by decide)).trans (by simp [a, seeded])
    have b60 : b.nr 60 = s.nr 60 := (frame 60 (by decide)).trans (by simp [a, seeded])
    have b66 : b.nr 66 = s.nr 66 := (frame 66 (by decide)).trans (by simp [a, seeded])
    exact (keepsReal i (by rwa [b59]) (by rwa [b59, b60]) (by rwa [b59, b66])).trans (congrFun real i)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractPublish

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

/-! matching/MatchingContractHandler.lean -/
section RppSource_MatchingContractHandler
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000









private theorem clearContractedCandidateRows_bound (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) : ∃ t ticks, ticks ≤ 9 ∧ BlockRuns clearContractedCandidateRows ticks s t ∧
      t.halted = false ∧ CacheMemoryFrame s t := by
  by_cases absent : s.nm (s.nr 89 + s.nr 7) ≤ s.nr 23
  · let t := (arithmeticStep clearContractedCandidateRows)^[3] s
    have final : t.pc = clearContractedCandidateRows.length ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm := by
      simp [t, clearContractedCandidateRows, arithmeticStep, entry, running, absent, Function.iterate_succ_apply']
    exact ⟨t, 3, by decide, BlockRuns.of_running_exit rfl final.2.1 final.1, final.2.1,
      fun _ _ => congrFun final.2.2.1 _, fun _ _ _ _ => congrFun final.2.2.2 _⟩
  · let t := (arithmeticStep clearContractedCandidateRows)^[9] s
    have final : t.pc = clearContractedCandidateRows.length ∧ t.halted = false ∧
        t.nm = Function.update (Function.update s.nm (s.nr 58 + s.nr 7) (s.nr 23))
          (s.nr 58 + (s.nr 55 + s.nr 55 + s.nr 7)) (s.nr 23) ∧ t.rm = s.rm := by
      simp [t, clearContractedCandidateRows, arithmeticStep, entry, running, absent, Function.iterate_succ_apply']
    refine ⟨t, 9, le_rfl, BlockRuns.of_running_exit rfl final.2.1 final.1, final.2.1, ?_,
      fun _ _ _ _ => congrFun final.2.2.2 _⟩
    intro addr below
    simp (disch := omega) [final.2.2.1, Function.update_of_ne]

private theorem clearPromotedIncomingCandidate_bound (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) : ∃ t ticks, ticks ≤ 5 ∧ BlockRuns clearPromotedIncomingCandidate ticks s t ∧
      t.halted = false ∧ CacheMemoryFrame s t := by
  let t := (arithmeticStep clearPromotedIncomingCandidate)^[5] s
  have final : t.pc = clearPromotedIncomingCandidate.length ∧ t.halted = false ∧
      t.nm = Function.update s.nm (s.nr 58 + (s.nr 55 + s.nm (s.nr 88 + s.nr 7))) (s.nr 23) ∧ t.rm = s.rm := by
    simp [t, clearPromotedIncomingCandidate, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, 5, le_rfl, BlockRuns.of_running_exit rfl final.2.1 final.1, final.2.1, ?_,
    fun _ _ _ _ => congrFun final.2.2.2 _⟩
  intro addr below
  simp (disch := omega) [final.2.2.1, Function.update_of_ne]

private theorem writeMergedBucketForOuter_bound (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ t ticks, ticks ≤ 22 * s.nr 87 + 89 ∧ BlockRuns writeMergedBucketForOuter ticks s t ∧
      t.halted = false ∧ CacheMemoryFrame s t := by
  let a := {s with pc := 1, nr := Function.update s.nr 17 (s.nr 24 + s.nr 23)}
  have load : BlockRuns [.natAdd 17 24 23] 1 s a := by
    apply BlockRuns.of_running_exit
    · simp [a, arithmeticStep, entry, running]
    · exact running
    · rfl
  let b := {a with pc := 0}
  have bOne : b.nr 9 = 1 := by simpa [b, a] using one
  obtain ⟨min, searchTicks, searchCost, search, searchLive, _, minNat, minReal⟩ :=
    minimumContractedBucket_spec b rfl running bOne
  let c := {min with pc := 0}
  have kept (r : ℕ) (safe : r ∉ [0, 1, 2, 6, 7, 10, 11, 17]) : c.nr r = s.nr r := by
    change min.nr r = s.nr r
    rw [← search.run]
    have same := arithmeticRun_keeps_from_destination_list (p := minimumContractedBucket) [0, 1, 2, 6, 7, 10, 11] (by decide)
      (show r ∉ [0, 1, 2, 6, 7, 10, 11] by simp at safe ⊢; omega) b searchTicks
    have other : r ≠ 17 := by simp at safe; omega
    exact same.trans (by simp [b, a, Function.update_of_ne other])
  have cOne : c.nr 9 = 1 := (kept 9 (by decide)).trans one
  have cDict : c.nr 58 ≤ c.nr 54 := by rwa [kept 58 (by decide), kept 54 (by decide)]
  have cBucket : c.nr 58 ≤ c.nr 65 := by rwa [kept 58 (by decide), kept 65 (by decide)]
  obtain ⟨t, writeTicks, writeCost, publish, live, natural, real⟩ :=
    publishMinimumContractedBucket_bound c rfl searchLive cOne cDict cBucket
  refine ⟨_, 1 + (searchTicks + writeTicks), ?_, load.append (search.append publish), live, ?_, ?_⟩
  · have count : b.nr 87 = s.nr 87 := by simp [b, a]
    rw [count] at searchCost
    omega
  · intro addr below
    exact (natural addr (by rwa [kept 58 (by decide)])).trans (congrFun minNat addr)
  · intro addr below rate score
    exact (real addr (by rwa [kept 59 (by decide)]) (by rwa [kept 59 (by decide), kept 60 (by decide)])
      (by rwa [kept 59 (by decide), kept 66 (by decide)])).trans (congrFun minReal addr)

private theorem repairMergedBucketForColumn_bound (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ t ticks, ticks ≤ 22 * s.nr 87 + 97 ∧ BlockRuns repairMergedBucketForColumn ticks s t ∧
      t.halted = false ∧ CacheMemoryFrame s t := by
  let addr := s.nr 51 + s.nr 24
  let loaded := {s with pc := 2, nr := Function.update (Function.update s.nr 6 addr) 10 (s.nm addr)}
  have first : BlockRuns readSurvivingForestRole 2 s loaded := by
    apply BlockRuns.of_running_exit
    · simp [readSurvivingForestRole, arithmeticStep, loaded, addr, entry, running, Function.iterate_succ_apply']
    · exact running
    · rfl
  let a := {loaded with pc := 0}
  let repair := branchOnUnequal 24 26 writeMergedBucketForOuter
  let test := branchOnAtMost 9 10 repair []
  have empty : BlockRuns [] 0 a a := BlockRuns.of_running_exit rfl running rfl
  by_cases roleAtMost : a.nr 10 ≤ a.nr 9
  · by_cases roleAtLeast : a.nr 9 ≤ a.nr 10
    · by_cases same : a.nr 24 = a.nr 26
      · have skip := branchOnUnequal_skip 24 26 writeMergedBucketForOuter a rfl running same
        have selected := branchOnAtMost_left 9 10 repair [] (s := a) rfl running roleAtLeast skip running
        have step := branchOnAtMost_left 10 9 test [] (s := a) rfl running roleAtMost selected running
        exact ⟨_, _, by omega, first.append step, running, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
      · have aOne : a.nr 9 = 1 := by simpa [a, loaded] using one
        have aDict : a.nr 58 ≤ a.nr 54 := by simpa [a, loaded] using dict
        have aBucket : a.nr 58 ≤ a.nr 65 := by simpa [a, loaded] using bucket
        obtain ⟨t, ticks, cost, updated, ready, frame⟩ := writeMergedBucketForOuter_bound a rfl running aOne aDict aBucket
        have charged := branchOnUnequal_take 24 26 writeMergedBucketForOuter (s := a) rfl running same updated
        have selected := branchOnAtMost_left 9 10 repair [] (s := a) rfl running roleAtLeast charged ready
        have step := branchOnAtMost_left 10 9 test [] (s := a) rfl running roleAtMost selected ready
        have bound : a.nr 87 = s.nr 87 := by simp [a, loaded]
        rw [bound] at cost
        exact ⟨_, _, by omega, first.append step, ready, frame.natural, frame.real⟩
    · have selected := branchOnAtMost_right 9 10 repair [] (s := a) rfl running (Nat.lt_of_not_ge roleAtLeast) empty running
      have step := branchOnAtMost_left 10 9 test [] (s := a) rfl running roleAtMost selected running
      exact ⟨_, _, by omega, first.append step, running, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  · have step := branchOnAtMost_right 10 9 test [] (s := a) rfl running (Nat.lt_of_not_ge roleAtMost) empty running
    exact ⟨_, _, by omega, first.append step, running, fun _ _ => rfl, fun _ _ _ _ => rfl⟩

private theorem scanFreshContractedOriginal_bound (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ t ticks, ticks ≤ 98 * s.nr 55 + 4 ∧ BlockRuns scanFreshContractedOriginal ticks s t ∧
      t.halted = false ∧ CacheMemoryFrame s t := by
  let addr := s.nr 88 + s.nr 24
  let a := {s with pc := 2, nr := Function.update (Function.update s.nr 6 addr) 15 (s.nm addr)}
  have load : BlockRuns [.natAdd 6 88 24, .natLoad 15 6] 2 s a := by
    apply BlockRuns.of_running_exit
    · simp [a, addr, arithmeticStep, entry, running, Function.iterate_succ_apply']
    · exact running
    · rfl
  let b := {a with pc := 0}
  have bOne : b.nr 9 = 1 := by simpa [b, a] using one
  have bDict : b.nr 58 ≤ b.nr 54 := by simpa [b, a] using dict
  have bBucket : b.nr 58 ≤ b.nr 65 := by simpa [b, a] using bucket
  obtain ⟨t, ticks, cost, scan, ready, natural, real⟩ := refreshSelectedOuterVertex_spec b rfl running bOne bDict bBucket
  have size : b.nr 55 = s.nr 55 := by simp [b, a]
  rw [size, Nat.mul_comm] at cost
  exact ⟨_, 2 + ticks, by omega, load.append scan, ready, natural, real⟩

private def contractionCacheBases : List ℕ := [9, 54, 55, 58, 59, 60, 65, 66, 87, 99]

private theorem CacheMemoryFrame.chain {s m t : ArithmeticState} (earlier : CacheMemoryFrame s m)
    (same : ∀ r ∈ contractionCacheBases, m.nr r = s.nr r) (later : CacheMemoryFrame m t) : CacheMemoryFrame s t := by
  constructor
  · intro a lower
    exact (later.natural a (by rwa [same 58 (by decide)])).trans (earlier.natural a lower)
  · intro a before rate pair
    exact (later.real a (by rwa [same 59 (by decide)]) (by rwa [same 59 (by decide), same 60 (by decide)])
      (by rwa [same 59 (by decide), same 66 (by decide)])).trans (earlier.real a before rate pair)

private structure ContractionCachePass (s : ArithmeticState) (index : ℕ) (i : ℕ) (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  running : m.halted = false
  cursor : m.nr index = i
  stable : ∀ r ∈ contractionCacheBases, m.nr r = s.nr r
  memory : CacheMemoryFrame s m

/-- Check the common loop controls of all four repair passes. Each pass preserves
the routing region and the address and count registers used by the following pass. -/
private theorem contractionCachePass_runs (s : ArithmeticState) (index limit cap : ℕ)
    (body : List ArithmeticInstruction) (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (indexOut : index ∉ contractionCacheBases) (limitIn : limit ∈ contractionCacheBases)
    (writes : body.all (fun ins => decide (naturalDestination ins ∉ index :: contractionCacheBases)) = true)
    (iterate : ∀ m : ArithmeticState, m.pc = 0 → m.halted = false →
      (∀ r ∈ contractionCacheBases, m.nr r = s.nr r) →
      ∃ t steps, steps ≤ cap ∧ BlockRuns body steps m t ∧ t.halted = false ∧ CacheMemoryFrame m t) :
    ∃ t steps, steps ≤ s.nr limit * (cap + 3) + 2 ∧
      BlockRuns (countedLoopFromZero 9 index limit body) steps s t ∧ t.halted = false ∧
      CacheMemoryFrame s t ∧ ∀ r ∈ contractionCacheBases, t.nr r = s.nr r := by
  have init : ContractionCachePass s index 0 {s with pc := 0, nr := Function.update s.nr index 0} := by
    refine ⟨rfl, running, by simp, ?_, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    intro r listed
    have no : r ≠ index := fun same => indexOut (by rwa [← same])
    exact Function.update_of_ne no _ _
  have step (i : ℕ) (_ : i < s.nr limit) (m : ArithmeticState) (inv : ContractionCachePass s index i m) :
      ∃ t ticks, ticks ≤ cap ∧ BlockRuns body ticks m t ∧ t.halted = false ∧
        ContractionCachePass s index (i + 1) {t with pc := 0, nr := Function.update t.nr index (t.nr index + t.nr 9)} := by
    obtain ⟨t, steps, cost, run, live, frame⟩ := iterate m inv.entry inv.running inv.stable
    have kept (r : ℕ) (listed : r ∈ index :: contractionCacheBases) : t.nr r = m.nr r := by
      rw [← run.run]
      apply arithmeticRun_keeps_register _ m steps
      intro ins inside same
      have safe : naturalDestination ins ∉ index :: contractionCacheBases :=
        of_decide_eq_true (List.all_eq_true.mp writes ins inside)
      exact safe (same.symm ▸ listed)
    have carried (r : ℕ) (listed : r ∈ contractionCacheBases) : t.nr r = s.nr r :=
      (kept r (List.mem_cons_of_mem _ listed)).trans (inv.stable r listed)
    have composed := inv.memory.chain inv.stable frame
    refine ⟨t, steps, cost, run, live, rfl, live, ?_, ?_, composed.natural, composed.real⟩
    · simp [kept index (by simp), inv.cursor, (carried 9 (by decide)).trans one]
    · intro r listed
      have no : r ≠ index := fun same => indexOut (by rwa [← same])
      exact (Function.update_of_ne no _ _).trans (carried r listed)
  obtain ⟨last, steps, complete, cost, run⟩ := countedLoopFromZero_bounded 9 index limit (s.nr limit) cap body
    (ContractionCachePass s index) (s := s) entry running init
    (fun _ _ inv => ⟨inv.entry, inv.running, inv.cursor, inv.stable limit limitIn⟩) step
  exact ⟨_, steps, by omega, run, complete.running, ⟨complete.memory.natural, complete.memory.real⟩, complete.stable⟩

theorem repairMatchingContractionCache_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ t ticks, ticks ≤ (112 + 22 * s.nr 87) * s.nr 55 + (15 + 98 * s.nr 55) * s.nr 99 + 11 ∧
      BlockRuns repairMatchingContractionCache ticks s t ∧ t.halted = false ∧ CacheMemoryFrame s t ∧
      (∀ r, r ∉ [0, 1, 2, 6, 7, 10, 11, 14, 15, 16, 17, 18, 19, 23, 24, 25, 26] → t.nr r = s.nr r) ∧
      t.rr 15 = s.rr 15 ∧ t.nr 14 = 0 := by
  let seedCode : List ArithmeticInstruction := [.natConst 23 0, .natConst 14 0, .natAdd 26 12 23]
  let seeded := { s with
    pc := 3
    nr := Function.update (Function.update (Function.update s.nr 23 0) 14 0) 26 (s.nr 12) }
  have seed : BlockRuns seedCode 3 s seeded := by
    apply BlockRuns.of_running_exit
    · simp [seedCode, seeded, entry, running, arithmeticStep, Function.iterate_succ_apply']
    · exact running
    · rfl
  let a := {seeded with pc := 0}
  have initialBases (r : ℕ) (listed : r ∈ contractionCacheBases) : a.nr r = s.nr r := by
    have away23 : r ≠ 23 := by simp [contractionCacheBases] at listed; omega
    have away14 : r ≠ 14 := by simp [contractionCacheBases] at listed; omega
    have away26 : r ≠ 26 := by simp [contractionCacheBases] at listed; omega
    simp [a, seeded, Function.update_of_ne away23, Function.update_of_ne away14, Function.update_of_ne away26]
  have initialFrame : CacheMemoryFrame s a := ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  obtain ⟨cleared, clearTicks, clearCost, clear, clearLive, clearFrame, clearBases⟩ :=
    contractionCachePass_runs a 7 55 9 clearContractedCandidateRows rfl running
      ((initialBases 9 (by decide)).trans one) (by decide) (by decide) (by decide)
      (fun m start ready _ => clearContractedCandidateRows_bound m start ready)
  let b := {cleared with pc := 0}
  have bBases (r : ℕ) (listed : r ∈ contractionCacheBases) : b.nr r = s.nr r :=
    (clearBases r listed).trans (initialBases r listed)
  obtain ⟨clearedIncoming, incomingTicks, incomingCost, incoming, incomingLive, incomingFrame, incomingBases⟩ :=
    contractionCachePass_runs b 7 99 5 clearPromotedIncomingCandidate rfl clearLive
      ((bBases 9 (by decide)).trans one) (by decide) (by decide) (by decide)
      (fun m start ready _ => clearPromotedIncomingCandidate_bound m start ready)
  let c := {clearedIncoming with pc := 0}
  have cBases (r : ℕ) (listed : r ∈ contractionCacheBases) : c.nr r = s.nr r :=
    (incomingBases r listed).trans (bBases r listed)
  have geometry (m : ArithmeticState) (kept : ∀ r ∈ contractionCacheBases, m.nr r = s.nr r) :
      m.nr 9 = 1 ∧ m.nr 58 ≤ m.nr 54 ∧ m.nr 58 ≤ m.nr 65 := by
    refine ⟨(kept 9 (by decide)).trans one, ?_, ?_⟩
    · rwa [kept 58 (by decide), kept 54 (by decide)]
    · rwa [kept 58 (by decide), kept 65 (by decide)]
  obtain ⟨published, columnTicks, columnCost, columns, columnLive, columnFrame, columnBases⟩ :=
    contractionCachePass_runs c 24 55 (22 * s.nr 87 + 97) repairMergedBucketForColumn
      rfl incomingLive ((cBases 9 (by decide)).trans one) (by decide) (by decide) (by decide) (by
        intro m atStart live keeps
        have same (r : ℕ) (hr : r ∈ contractionCacheBases) : m.nr r = s.nr r := (keeps r hr).trans (cBases r hr)
        obtain ⟨mOne, mDict, mBucket⟩ := geometry m same
        simpa only [same 87 (by decide)] using repairMergedBucketForColumn_bound m atStart live mOne mDict mBucket)
  let d := {published with pc := 0}
  have dBases (r : ℕ) (listed : r ∈ contractionCacheBases) : d.nr r = s.nr r :=
    (columnBases r listed).trans (cBases r listed)
  obtain ⟨t, scanTicks, scanCost, scan, scanLive, scanFrame, _⟩ :=
    contractionCachePass_runs d 24 99 (98 * s.nr 55 + 4) scanFreshContractedOriginal
      rfl columnLive ((dBases 9 (by decide)).trans one) (by decide) (by decide) (by decide) (by
        intro m atStart live keeps
        have same (r : ℕ) (hr : r ∈ contractionCacheBases) : m.nr r = s.nr r := (keeps r hr).trans (dBases r hr)
        obtain ⟨mOne, mDict, mBucket⟩ := geometry m same
        simpa only [same 55 (by decide)] using scanFreshContractedOriginal_bound m atStart live mOne mDict mBucket)
  have run : BlockRuns repairMatchingContractionCache (3 + (clearTicks + (incomingTicks + (columnTicks + scanTicks)))) s _ :=
    seed.append (clear.append (incoming.append (columns.append scan)))
  have clearPrior := initialFrame.chain initialBases clearFrame
  have bPrior : CacheMemoryFrame s b := ⟨clearPrior.natural, clearPrior.real⟩
  have incomingPrior := bPrior.chain bBases incomingFrame
  have cPrior : CacheMemoryFrame s c := ⟨incomingPrior.natural, incomingPrior.real⟩
  have columnPrior := cPrior.chain cBases columnFrame
  have dPrior : CacheMemoryFrame s d := ⟨columnPrior.natural, columnPrior.real⟩
  have frame := dPrior.chain dBases scanFrame
  refine ⟨_, _, ?_, run, scanLive, ⟨frame.natural, frame.real⟩, ?_, ?_, ?_⟩
  · rw [initialBases 55 (by decide)] at clearCost
    rw [bBases 99 (by decide)] at incomingCost
    rw [cBases 55 (by decide)] at columnCost
    rw [dBases 99 (by decide)] at scanCost
    simp only [show 9 + 3 = 12 by decide, show 5 + 3 = 8 by decide] at clearCost incomingCost
    have columnsFactor : s.nr 55 * (22*s.nr 87 + 97 + 3) = (22*s.nr 87 + 100) * s.nr 55 := by ring
    have scansFactor : s.nr 99 * (98 * s.nr 55 + 4 + 3) = (98 * s.nr 55 + 7) * s.nr 99 := by ring
    rw [columnsFactor] at columnCost
    rw [scansFactor] at scanCost
    have a : (112 + 22 * s.nr 87) * s.nr 55 = 12 * s.nr 55 + (22 * s.nr 87 + 100) * s.nr 55 := by ring
    have b : (15 + 98 * s.nr 55) * s.nr 99 = 8 * s.nr 99 + (98 * s.nr 55 + 7) * s.nr 99 := by ring
    rw [a, b]
    omega
  · intro r safe
    rw [← run.run]
    exact arithmeticRun_keeps_from_destination_list [0, 1, 2, 6, 7, 10, 11, 14, 15, 16, 17, 18, 19, 23, 24, 25, 26]
      (by decide) safe s _
  · rw [← run.run]
    exact arithmeticRun_keeps_real_from_destination_list [0, 1, 2, 3, 4, 5, 6] (by decide) (by decide) s _
  · have tail := clear.append (incoming.append (columns.append scan))
    have zero : a.nr 14 = 0 := by simp [a, seeded]
    have stayed := blockRuns_preservesNaturalZero (r := 14) (by decide) tail zero
    exact stayed

theorem matchingContractionCost_le_charge (k rows fresh : ℕ) :
    120 * k + 78 + ((112 + 22 * rows) * k + (15 + 98 * k) * fresh + 11) + 5 ≤
      (300 * k + 110) * (1 + rows + fresh) := by
  have absorbed : 22 * k ≤ 300 * k + 110 := by omega
  have exposed : 15 + 98 * k ≤ 300 * k + 110 := by omega
  have rowsCost := Nat.mul_le_mul_right rows absorbed
  have freshCost := Nat.mul_le_mul_right fresh exposed
  have combined : (112 + 22 * rows) * k = 112 * k + (22 * k) * rows := by ring
  rw [combined, Nat.mul_add, Nat.mul_add, Nat.mul_one]
  omega











/-- Complete contraction timing and routing frame. The extra work is charged to
the absorbed outer rows and the newly outer originals counted by the actual scans. -/
theorem matchingContractionHandlerBlock_runs (s : ArithmeticState) (layout : MatchingContractionLayout s)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t ticks, ticks ≤ (300 * s.nr 55 + 110) * (1 + t.nr 87 + t.nr 99) ∧
      BlockRuns matchingContractionHandlerBlock ticks s t ∧ t.halted = false ∧ t.nr 87 ≤ s.nr 55 ∧
      t.nr 1 = 0 ∧ t.nr 3 = s.nr 58 ∧ t.nr 4 = s.nr 59 ∧ t.nr 5 = s.nr 60 ∧ t.nr 8 = s.nr 61 ∧
      t.rr 15 = s.rr 15 + s.rr 1 ∧ (∀ a < s.nr 51, t.nm a = s.nm a) ∧
      (∀ a < s.nr 62, t.rm a = s.rm a) ∧
      ∀ r ≥ 30, r ∉ [68, 76, 81, 82, 87, 99] → t.nr r = s.nr r := by
  obtain ⟨contracted, contractTicks, contractCost, contract, contractLive, active, time, natural, real, contractKeeps, _, _⟩ :=
    matchingContractionStructure_spec s layout entry running one
  let a := {contracted with pc := 0}
  have aOne : a.nr 9 = 1 := (contractKeeps 9 (by decide)).trans one
  have aDict : a.nr 58 ≤ a.nr 54 := by
    rw [contractKeeps 58 (by decide), contractKeeps 54 (by decide)]
    exact layout.dictionaryAfter
  have aBucket : a.nr 58 ≤ a.nr 65 := by
    rw [contractKeeps 58 (by decide), contractKeeps 65 (by decide)]
    exact layout.bucketsAfter
  obtain ⟨repaired, cacheTicks, cacheCost, cache, cacheLive, cacheFrame, keeps, cacheTime, zero⟩ :=
    repairMatchingContractionCache_spec a rfl contractLive aOne aDict aBucket
  let b := {repaired with pc := 0}
  have bKeeps (r : ℕ) (high : 30 ≤ r) (safe : r ∉ [68, 76, 81, 82, 87, 99]) : b.nr r = s.nr r :=
    (keeps r (by simp; omega)).trans (contractKeeps r (by simp at safe ⊢; omega))
  obtain ⟨t, reset, live, resetNat, resetReal, id, selectorIds, selectorSlack, selectorRates, selectorLength⟩ :=
    resetMatchingSelector_spec b rfl cacheLive zero
  have run : BlockRuns matchingContractionHandlerBlock (contractTicks + (cacheTicks + 5)) s _ := contract.append (cache.append reset)
  have resetKeeps (r : ℕ) (high : 30 ≤ r) : t.nr r = b.nr r := by
    rw [← reset.run]
    exact arithmeticRun_keeps_from_destination_list [0, 1, 3, 4, 5, 8] (by decide) (by simp; omega) b 5
  have rows : t.nr 87 = a.nr 87 := (resetKeeps 87 (by decide)).trans (keeps 87 (by decide))
  have fresh : t.nr 99 = a.nr 99 := (resetKeeps 99 (by decide)).trans (keeps 99 (by decide))
  have cumulative : t.rr 15 = s.rr 15 + s.rr 1 := by
    have resetTime : t.rr 15 = b.rr 15 := by
      rw [← reset.run]
      exact arithmeticRun_keeps_real_from_destination_list [0] (by decide) (by decide) b 5
    exact resetTime.trans (cacheTime.trans time)
  refine ⟨_, _, ?_, run, live, rows.trans_le active, id,
    selectorIds.trans (bKeeps 58 (by decide) (by decide)), selectorSlack.trans (bKeeps 59 (by decide) (by decide)),
    selectorRates.trans (bKeeps 60 (by decide) (by decide)), selectorLength.trans (bKeeps 61 (by decide) (by decide)),
    cumulative, ?_, ?_, ?_⟩
  · have bound : a.nr 55 = s.nr 55 := contractKeeps 55 (by decide)
    rw [bound, ← rows, ← fresh] at cacheCost
    have whole := matchingContractionCost_le_charge (s.nr 55) (t.nr 87) (t.nr 99)
    change contractTicks + (cacheTicks + 5) ≤ (300 * s.nr 55 + 110) * (1 + t.nr 87 + t.nr 99)
    omega
  · intro addr lower
    have cap : addr < a.nr 58 := by
      rw [contractKeeps 58 (by decide)]
      have h₁ := layout.roleEnd
      have h₂ := layout.representativeEnd
      omega
    exact (congrFun resetNat addr).trans ((cacheFrame.natural addr cap).trans (natural addr lower))
  · intro addr lower
    have aFloor : a.nr 59 = s.nr 59 := contractKeeps 59 (by decide)
    have rate : a.nr 59 ≤ a.nr 60 := by
      rw [aFloor, contractKeeps 60 (by decide)]
      exact layout.realRatesAfter
    have score : a.nr 59 ≤ a.nr 66 := by
      rw [aFloor, contractKeeps 66 (by decide)]
      exact layout.realBucketsAfter
    have belowCache : addr < a.nr 59 := aFloor.symm ▸ lower.trans_le layout.slacksAfter
    exact (congrFun resetReal addr).trans ((cacheFrame.real addr belowCache rate score).trans (real addr lower))
  · intro r high safe
    exact (resetKeeps r high).trans (bKeeps r high safe)



end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractHandler

open VehicleRoutingSurvey.Routing SupplyChainTheory in
theorem solution : (fun {P : Prop} (_ : P) => P) (@VehicleRoutingSurvey.Routing.matchingContractionHandlerBlock_runs) :=
  @VehicleRoutingSurvey.Routing.matchingContractionHandlerBlock_runs
