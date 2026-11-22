-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.matchingContractionStructure_spec
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T16:12:19.488843+00:00
-- url     : https://prove2.me/submissions/c7d645b6-1fab-4f84-a704-a7eb89681640

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_ContractionStructure
import Theorems.Thm_VehicleRoutingSurvey_Routing_finishMatchingContractionStructure_spec

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





























end VehicleRoutingSurvey.Routing
end RppSource_WeightedReadDeltaRAM

/-! matching/MatchingBlossomDualRAM.lean -/
section RppSource_MatchingBlossomDualRAM
namespace VehicleRoutingSurvey.Routing











structure BlossomDualCellResult (s t : ArithmeticState) (steps : ℕ) : Prop where
  run : BlockRuns advanceMatchingBlossomDualCell steps s t
  live : t.halted = false
  natural : t.nm = s.nm
  real : t.rm = modifyBlossomDualAt s (s.nr 7)
  delta : t.rr 1 = s.rr 1
  cumulative : t.rr 15 = s.rr 15

set_option maxRecDepth 4096 in
theorem advanceMatchingBlossomDualCell_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 14 = 0) (one : s.nr 9 = 1) :
    ∃ t steps, steps ≤ 12 ∧ BlossomDualCellResult s t steps := by
  by_cases singleton : s.nm (s.nr 74 + s.nr 7) = 0
  · let t := (arithmeticStep advanceMatchingBlossomDualCell)^[3] s
    have effect : t.pc = advanceMatchingBlossomDualCell.length ∧ t.halted = false ∧
        t.nm = s.nm ∧ t.rm = modifyBlossomDualAt s (s.nr 7) ∧ t.rr 1 = s.rr 1 ∧ t.rr 15 = s.rr 15 := by
      simp [t, arithmeticStep, advanceMatchingBlossomDualCell, Function.iterate_succ_apply', entry, running,
        zero, singleton, modifyBlossomDualAt, blossomNodeAt]
    exact ⟨t, 3, by decide, BlockRuns.of_running_exit rfl effect.2.1 effect.1,
      effect.2.1, effect.2.2.1, effect.2.2.2.1, effect.2.2.2.2.1, effect.2.2.2.2.2⟩
  by_cases dormant : s.nm (s.nr 51 + s.nr 7) = 0
  · let t := (arithmeticStep advanceMatchingBlossomDualCell)^[6] s
    have effect : t.pc = advanceMatchingBlossomDualCell.length ∧ t.halted = false ∧
        t.nm = s.nm ∧ t.rm = modifyBlossomDualAt s (s.nr 7) ∧ t.rr 1 = s.rr 1 ∧ t.rr 15 = s.rr 15 := by
      simp [t, arithmeticStep, advanceMatchingBlossomDualCell, Function.iterate_succ_apply', entry, running,
        zero, singleton, dormant, modifyBlossomDualAt, blossomNodeAt, blossomRoleAt]
    exact ⟨t, 6, by decide, BlockRuns.of_running_exit rfl effect.2.1 effect.1,
      effect.2.1, effect.2.2.1, effect.2.2.2.1, effect.2.2.2.2.1, effect.2.2.2.2.2⟩
  by_cases outer : s.nm (s.nr 51 + s.nr 7) ≤ 1
  · let t := (arithmeticStep advanceMatchingBlossomDualCell)^[12] s
    have effect : t.pc = advanceMatchingBlossomDualCell.length ∧ t.halted = false ∧
        t.nm = s.nm ∧ t.rm = modifyBlossomDualAt s (s.nr 7) ∧ t.rr 1 = s.rr 1 ∧ t.rr 15 = s.rr 15 := by
      simp [t, arithmeticStep, advanceMatchingBlossomDualCell, Function.iterate_succ_apply', entry, running,
        zero, singleton, dormant, one, outer, modifyBlossomDualAt, blossomDualAfterDelta, blossomNodeAt, blossomRoleAt]
    exact ⟨t, 12, le_rfl, BlockRuns.of_running_exit rfl effect.2.1 effect.1,
      effect.2.1, effect.2.2.1, effect.2.2.2.1, effect.2.2.2.2.1, effect.2.2.2.2.2⟩
  · let t := (arithmeticStep advanceMatchingBlossomDualCell)^[11] s
    have effect : t.pc = advanceMatchingBlossomDualCell.length ∧ t.halted = false ∧
        t.nm = s.nm ∧ t.rm = modifyBlossomDualAt s (s.nr 7) ∧ t.rr 1 = s.rr 1 ∧ t.rr 15 = s.rr 15 := by
      simp [t, arithmeticStep, advanceMatchingBlossomDualCell, Function.iterate_succ_apply', entry, running,
        zero, singleton, dormant, one, outer, modifyBlossomDualAt, blossomDualAfterDelta, blossomNodeAt, blossomRoleAt]
    exact ⟨t, 11, by decide, BlockRuns.of_running_exit rfl effect.2.1 effect.1,
      effect.2.1, effect.2.2.1, effect.2.2.2.1, effect.2.2.2.2.1, effect.2.2.2.2.2⟩





private structure BlossomDualScan (initial : ArithmeticState) (index : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  indexAt : s.nr 7 = index
  kept : ∀ r, r ∉ [0, 6, 7, 10, 11] → s.nr r = initial.nr r
  natural : s.nm = initial.nm
  effect : s.rm = iterateBlossomDuals initial index
  delta : s.rr 1 = initial.rr 1
  cumulative : s.rr 15 = initial.rr 15

/-- Execute one pass of registry updates in at most fifteen instructions per vertex. -/
theorem advanceMatchingBlossomDualBlock_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 14 = 0) (one : s.nr 9 = 1) :
    ∃ t steps, steps ≤ s.nr 55 * 15 + 2 ∧ BlockRuns advanceMatchingBlossomDualBlock steps s t ∧
      t.halted = false ∧ t.nm = s.nm ∧ t.rm = iterateBlossomDuals s (s.nr 55) ∧
      t.rr 1 = s.rr 1 ∧ t.rr 15 = s.rr 15 ∧
      ∀ r, r ∉ [0, 6, 7, 10, 11] → t.nr r = s.nr r := by
  have init : BlossomDualScan s 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, rfl, rfl, rfl, rfl⟩
    intro r away
    have other : r ≠ 7 := by simp at away; omega
    exact Function.update_of_ne other 0 s.nr
  have iterate (i : ℕ) (_ : i < s.nr 55) (m : ArithmeticState) (ready : BlossomDualScan s i m) :
      ∃ t steps, steps ≤ 12 ∧ BlockRuns advanceMatchingBlossomDualCell steps m t ∧ t.halted = false ∧
        BlossomDualScan s (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    have mZero := (ready.kept 14 (by decide)).trans zero
    have mOne := (ready.kept 9 (by decide)).trans one
    obtain ⟨t, ticks, short, computed⟩ := advanceMatchingBlossomDualCell_spec m ready.entry ready.running mZero mOne
    have fixed (r : ℕ) (other : r ∉ [0, 6, 10, 11]) : t.nr r = m.nr r := by
      rw [← computed.run.run]
      apply arithmeticRun_keeps_register _ m ticks
      simp [advanceMatchingBlossomDualCell, naturalDestination] at other ⊢ <;> omega
    have updateSame : modifyBlossomDualAt m i = modifyBlossomDualAt {s with rm := iterateBlossomDuals s i} i := by
      have nodeAddr := ready.kept 74 (by decide)
      have roleAddr := ready.kept 51 (by decide)
      have dualAddr := ready.kept 75 (by decide)
      by_cases absent : s.nm (s.nr 74 + i) = 0 <;> by_cases dormant : s.nm (s.nr 51 + i) = 0 <;>
        by_cases outer : s.nm (s.nr 51 + i) ≤ 1 <;>
        simp [modifyBlossomDualAt, blossomDualAfterDelta, blossomNodeAt, blossomRoleAt, ready.natural, ready.effect,
          ready.delta, nodeAddr, roleAddr, dualAddr, absent, dormant, outer]
    refine ⟨t, ticks, short, computed.run, computed.live, rfl, computed.live, ?_, ?_,
      computed.natural.trans ready.natural, ?_, computed.delta.trans ready.delta,
      computed.cumulative.trans ready.cumulative⟩
    · simp [fixed 7 (by decide), fixed 9 (by decide), ready.indexAt, mOne]
    · intro r away
      have neq : r ≠ 7 := by simp at away; omega
      have outside : r ∉ [0, 6, 10, 11] := by simp at away ⊢; omega
      exact (Function.update_of_ne neq _ _).trans ((fixed r outside).trans (ready.kept r away))
    · change t.rm = _
      rw [computed.real, ready.indexAt, updateSame] <;> rfl
  obtain ⟨last, steps, done, cost, run⟩ := countedLoopFromZero_bounded 9 7 55 (s.nr 55) 12
    advanceMatchingBlossomDualCell (BlossomDualScan s) entry running init
    (fun _ _ h => ⟨h.entry, h.running, h.indexAt, h.kept 55 (by decide)⟩) iterate
  exact ⟨_, steps, by omega, run, done.running, done.natural, done.effect, done.delta, done.cumulative, done.kept⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingBlossomDualRAM

/-! matching/MatchingEffectiveUpdateRAM.lean -/
section RppSource_MatchingEffectiveUpdateRAM
namespace VehicleRoutingSurvey.Routing







private structure EffectiveCellResult (s t : ArithmeticState) (steps : ℕ) : Prop where
  run : BlockRuns advanceEffectivePotentialCell steps s t
  live : t.halted = false
  fixed : ∀ r, r ≠ 6 → r ≠ 10 → r ≠ 11 → r ≠ 12 → t.nr r = s.nr r
  delta : t.rr 1 = s.rr 1
  cumulative : t.rr 15 = s.rr 15
  natMemory : t.nm = s.nm
  effect : t.rm = Function.update s.rm (s.nr 62 + s.nr 7) (effectivePotentialAfterDelta s (s.nr 7))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
private theorem advanceEffectivePotentialCell_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) : ∃ t steps, steps ≤ 13 ∧ EffectiveCellResult s t steps := by
  by_cases idle : s.nm (s.nr 51 + s.nm (s.nr 57 + s.nr 7)) = 0
  · let t := (arithmeticStep advanceEffectivePotentialCell)^[8] s
    have live : t.halted = false := by
      simp [t, arithmeticStep, advanceEffectivePotentialCell, Function.iterate_succ_apply', entry, running,
        idle]
    have exits : t.pc = advanceEffectivePotentialCell.length := by
      simp [t, arithmeticStep, advanceEffectivePotentialCell, Function.iterate_succ_apply', entry, running,
        idle]
    refine ⟨t, 8, by decide, BlockRuns.of_running_exit rfl live exits, live, ?_, ?_, ?_, ?_, ?_⟩
    · intro r not6 not10 not11 not12
      simp [t, arithmeticStep, advanceEffectivePotentialCell, Function.iterate_succ_apply', entry, running,
        idle, not6, not10, not11, not12]
    all_goals simp [t, arithmeticStep, advanceEffectivePotentialCell, Function.iterate_succ_apply', entry, running,
      idle, effectivePotentialAfterDelta, effectiveRoleAt, Function.update_eq_self]
  by_cases outer : s.nm (s.nr 51 + s.nm (s.nr 57 + s.nr 7)) ≤ 1
  · let t := (arithmeticStep advanceEffectivePotentialCell)^[13] s
    have live : t.halted = false := by
      simp [t, arithmeticStep, advanceEffectivePotentialCell, Function.iterate_succ_apply', entry, running,
        idle, outer]
    have exits : t.pc = advanceEffectivePotentialCell.length := by
      simp [t, arithmeticStep, advanceEffectivePotentialCell, Function.iterate_succ_apply', entry, running,
        idle, outer]
    refine ⟨t, 13, le_rfl, BlockRuns.of_running_exit rfl live exits, live, ?_, ?_, ?_, ?_, ?_⟩
    · intro r not6 not10 not11 not12
      simp [t, arithmeticStep, advanceEffectivePotentialCell, Function.iterate_succ_apply', entry, running,
        idle, outer, not6, not10, not11, not12]
    all_goals simp [t, arithmeticStep, advanceEffectivePotentialCell, Function.iterate_succ_apply', entry, running,
      idle, outer, effectivePotentialAfterDelta, effectiveRoleAt]
  · let t := (arithmeticStep advanceEffectivePotentialCell)^[12] s
    have live : t.halted = false := by
      simp [t, arithmeticStep, advanceEffectivePotentialCell, Function.iterate_succ_apply', entry, running,
        idle, outer]
    have exits : t.pc = advanceEffectivePotentialCell.length := by
      simp [t, arithmeticStep, advanceEffectivePotentialCell, Function.iterate_succ_apply', entry, running,
        idle, outer]
    refine ⟨t, 12, by decide, BlockRuns.of_running_exit rfl live exits, live, ?_, ?_, ?_, ?_, ?_⟩
    · intro r not6 not10 not11 not12
      simp [t, arithmeticStep, advanceEffectivePotentialCell, Function.iterate_succ_apply', entry, running,
        idle, outer, not6, not10, not11, not12]
    all_goals simp [t, arithmeticStep, advanceEffectivePotentialCell, Function.iterate_succ_apply', entry, running,
      idle, outer, effectivePotentialAfterDelta, effectiveRoleAt]



private structure EffectivePotentialScan (initial : ArithmeticState) (index : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  live : s.halted = false
  indexAt : s.nr 7 = index
  fixed : ∀ r, r ≠ 6 → r ≠ 7 → r ≠ 10 → r ≠ 11 → r ≠ 12 → s.nr r = initial.nr r
  delta : s.rr 1 = initial.rr 1
  cumulative : s.rr 15 = initial.rr 15
  natMemory : s.nm = initial.nm
  table : ∀ a, s.rm a = if initial.nr 62 ≤ a ∧ a < initial.nr 62 + index then
    effectivePotentialAfterDelta initial (a - initial.nr 62) else initial.rm a

/-- Apply the dual step to the effective-potential table in at most sixteen instructions
per compact vertex plus two boundary instructions. The labelled forest is read-only. -/
theorem advanceEffectivePotentialBlock_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ result steps, steps ≤ 16 * s.nr 55 + 2 ∧ BlockRuns advanceEffectivePotentialBlock steps s result ∧
      result.halted = false ∧ result.nm = s.nm ∧ result.rr 1 = s.rr 1 ∧
      result.rr 15 = s.rr 15 ∧
      (∀ r, r ≠ 6 → r ≠ 7 → r ≠ 10 → r ≠ 11 → r ≠ 12 → result.nr r = s.nr r) ∧
      ∀ a, result.rm a = if s.nr 62 ≤ a ∧ a < s.nr 62 + s.nr 55 then
        effectivePotentialAfterDelta s (a - s.nr 62) else s.rm a := by
  let inv := EffectivePotentialScan s
  have starts : inv 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, rfl, rfl, rfl, ?_⟩
    · intro r _ not7 _ _ _
      simp [Function.update_of_ne not7]
    · intro a
      have outside : ¬(s.nr 62 ≤ a ∧ a < s.nr 62 + 0) := by omega
      rw [if_neg outside]
  have control (i : ℕ) (m : ArithmeticState) (ready : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 55 = s.nr 55 :=
    ⟨ready.entry, ready.live, ready.indexAt, ready.fixed 55 (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  have iterate (i : ℕ) (_ : i < s.nr 55) (m : ArithmeticState) (before : inv i m) :
      ∃ t steps, steps ≤ 13 ∧ BlockRuns advanceEffectivePotentialCell steps m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    obtain ⟨t, ticks, short, cell⟩ := advanceEffectivePotentialCell_spec m before.entry before.live
    have base := before.fixed 62 (by decide) (by decide) (by decide) (by decide) (by decide)
    have repBase := before.fixed 57 (by decide) (by decide) (by decide) (by decide) (by decide)
    have roleBase := before.fixed 51 (by decide) (by decide) (by decide) (by decide) (by decide)
    have rateOne := (before.fixed 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans one
    let address := s.nr 62 + i
    have old : m.rm address = s.rm address := by
      have outside : ¬(s.nr 62 ≤ address ∧ address < s.nr 62 + i) := by simp [address]
      rw [before.table, if_neg outside]
    have sameUpdate : effectivePotentialAfterDelta m i = effectivePotentialAfterDelta s i := by
      by_cases idle : s.nm (s.nr 51 + s.nm (s.nr 57 + i)) = 0 <;>
        by_cases outer : s.nm (s.nr 51 + s.nm (s.nr 57 + i)) ≤ 1 <;>
        simp [effectivePotentialAfterDelta, effectiveRoleAt, base, repBase, roleBase,
          before.natMemory, before.delta, idle, outer, show m.rm (s.nr 62 + i) = s.rm (s.nr 62 + i) from old]
    refine ⟨t, ticks, short, cell.run, cell.live, rfl, cell.live, ?_, ?_, cell.delta.trans before.delta,
      cell.cumulative.trans before.cumulative, cell.natMemory.trans before.natMemory, ?_⟩
    · simp [cell.fixed 7 (by decide) (by decide) (by decide) (by decide),
        cell.fixed 9 (by decide) (by decide) (by decide) (by decide), before.indexAt, rateOne]
    · intro r not6 not7 not10 not11 not12
      simp only [Function.update_of_ne not7]
      exact (cell.fixed r not6 not10 not11 not12).trans (before.fixed r not6 not7 not10 not11 not12)
    · intro a
      change t.rm a = _
      rw [cell.effect, base, before.indexAt, sameUpdate]
      change Function.update m.rm address (effectivePotentialAfterDelta s i) a = _
      by_cases current : a = address
      · subst a
        have nowInside : s.nr 62 ≤ address ∧ address < s.nr 62 + (i + 1) := by
          dsimp [address]
          omega
        rw [Function.update_self, if_pos nowInside]
        simp [address]
      · rw [Function.update_of_ne current, before.table]
        have earlier : (s.nr 62 ≤ a ∧ a < s.nr 62 + i) ↔ (s.nr 62 ≤ a ∧ a < s.nr 62 + (i + 1)) := by
          dsimp [address] at current
          omega
        simp only [earlier]
  obtain ⟨last, steps, valid, cost, completed⟩ := countedLoopFromZero_bounded 9 7 55 (s.nr 55) 13
    advanceEffectivePotentialCell inv entry running starts control iterate
  exact ⟨_, steps, by omega, completed, valid.live, valid.natMemory, valid.delta, valid.cumulative,
    valid.fixed, valid.table⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingEffectiveUpdateRAM

/-! matching/MatchingGrowHandler.lean -/
section RppSource_MatchingGrowHandler
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096



private theorem advanceMatchingTime_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    let t := { s with
      pc := 2
      nr := Function.update s.nr 14 0
      rr := Function.update s.rr 15 (s.rr 15 + s.rr 1) }
    BlockRuns advanceMatchingTime 2 s t := by
  dsimp only
  apply BlockRuns.of_running_exit
  · simp [advanceMatchingTime, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · exact running
  · rfl

/-- Advance the cumulative step size and both stored dual views once. The topology and
chosen event ID stay unchanged, so the next block can decode the event. -/
theorem advanceMatchingEventDuals_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t ticks, ticks ≤ 31 * s.nr 55 + 6 ∧ BlockRuns advanceMatchingEventDuals ticks s t ∧
      t.halted = false ∧ t.nm = s.nm ∧ t.rr 1 = s.rr 1 ∧ t.rr 15 = s.rr 15 + s.rr 1 ∧ t.nr 14 = 0 ∧
      (∀ r, r ∉ [0, 6, 7, 10, 11, 12, 14] → t.nr r = s.nr r) ∧
      t.rm = iterateBlossomDuals {s with rm := advancedEffectiveMemory s} (s.nr 55) := by
  let seeded := { s with
    pc := 2
    nr := Function.update s.nr 14 0
    rr := Function.update s.rr 15 (s.rr 15 + s.rr 1) }
  have time : BlockRuns advanceMatchingTime 2 s seeded := advanceMatchingTime_spec s entry running
  let a := {seeded with pc := 0}
  have aOne : a.nr 9 = 1 := by simp [a, seeded, one]
  obtain ⟨middle, firstTicks, firstBound, first, live, natSame, deltaSame, timeSame, keeps, effective⟩ :=
    advanceEffectivePotentialBlock_spec a rfl running aOne
  let b := {middle with pc := 0}
  have bOne : b.nr 9 = 1 := (keeps 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans aOne
  have bZero : b.nr 14 = 0 := (keeps 14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [a, seeded])
  have bLimit : b.nr 55 = s.nr 55 := (keeps 55 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [a, seeded])
  obtain ⟨t, secondTicks, secondBound, second, stillLive, natAgain, registry, deltaAgain, timeAgain, preserved⟩ :=
    advanceMatchingBlossomDualBlock_spec b rfl live bZero bOne
  have aLimit : a.nr 55 = s.nr 55 := by simp [a, seeded]
  have aDelta : a.rr 1 = s.rr 1 := by simp [a, seeded]
  have bDelta : b.rr 1 = s.rr 1 := deltaSame.trans aDelta
  have bNat : b.nm = s.nm := natSame
  have timeValue : a.rr 15 = s.rr 15 + s.rr 1 := by simp [a, seeded]
  have memEff : b.rm = advancedEffectiveMemory s := by
    funext addr
    have pairBase : a.nr 62 = s.nr 62 := by simp [a, seeded]
    have repBase : a.nr 57 = s.nr 57 := by simp [a, seeded]
    have roleBase : a.nr 51 = s.nr 51 := by simp [a, seeded]
    change middle.rm addr = _
    rw [effective, advancedEffectiveMemory, pairBase, aLimit]
    simp [effectivePotentialAfterDelta, effectiveRoleAt, a, seeded] <;> rfl
  have bBase (r : ℕ) (outside : r ∉ [0, 6, 7, 10, 11, 12, 14]) : b.nr r = s.nr r := by
    simp at outside
    have aSame : a.nr r = s.nr r := by
      have different : r ≠ 14 := by omega
      simp [a, seeded, Function.update_of_ne different]
    exact (keeps r (by omega) (by omega) (by omega) (by omega) (by omega)).trans aSame
  have agree : ∀ n, iterateBlossomDuals b n =
      iterateBlossomDuals {s with rm := advancedEffectiveMemory s} n := by
    intro n
    induction n with
    | zero => exact memEff
    | succ n ih =>
      have nodeAt : b.nr 74 = s.nr 74 := bBase 74 (by decide)
      have roleAt : b.nr 51 = s.nr 51 := bBase 51 (by decide)
      have dualAt : b.nr 75 = s.nr 75 := bBase 75 (by decide)
      simp [iterateBlossomDuals, modifyBlossomDualAt, blossomDualAfterDelta, blossomRoleAt, blossomNodeAt,
        nodeAt, roleAt, dualAt, bNat, bDelta, ih] <;> rfl
  refine ⟨_, 2 + (firstTicks + secondTicks), ?_, time.append (first.append second), stillLive,
    natAgain.trans bNat, deltaAgain.trans bDelta, timeAgain.trans (timeSame.trans timeValue),
    (preserved 14 (by decide)).trans bZero, ?_, ?_⟩
  · rw [aLimit] at firstBound
    rw [bLimit] at secondBound
    omega
  · intro r outside
    have stable : r ∉ [0, 6, 7, 10, 11] := by simp at outside ⊢; omega
    exact (preserved r stable).trans (bBase r outside)
  · rw [bLimit] at registry
    exact registry.trans (agree _)

theorem matchingEventDualMemory_keeps_prefix (s : ArithmeticState) (floor address : ℕ)
    (before : address < floor) (effective : floor ≤ s.nr 62) (blossom : floor ≤ s.nr 75) :
    iterateBlossomDuals {s with rm := advancedEffectiveMemory s} (s.nr 55) address = s.rm address := by
  have lower : address < s.nr 62 := by omega
  have fixed (i : ℕ) : iterateBlossomDuals {s with rm := advancedEffectiveMemory s} i address = s.rm address := by
    induction i with
    | zero =>
      change advancedEffectiveMemory s address = _
      simp [advancedEffectiveMemory, Nat.not_le.mpr lower]
    | succ i ih =>
      have different : address ≠ s.nr 75 + blossomNodeAt s i := by omega
      rw [iterateBlossomDuals, modifyBlossomDualAt]
      split
      · exact ih
      · simpa [blossomNodeAt, Function.update_of_ne (by simpa [blossomNodeAt] using different)] using ih
  exact fixed _













end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowHandler

/-! matching/MatchingSearchDualRAM.lean -/
section RppSource_MatchingSearchDualRAM
namespace VehicleRoutingSurvey.Routing

private theorem modifyBlossomDualAt_with_real (s : ArithmeticState) (values : ℕ → ℝ) (i : ℕ) :
    modifyBlossomDualAt {s with rm := values} i =
      if blossomNodeAt s i = 0 ∨ blossomRoleAt s i = 0 then values else
        Function.update values (s.nr 75 + blossomNodeAt s i) (blossomDualAfterDelta {s with rm := values} i) := rfl

/-- The scan can only touch the nonzero node IDs in the top-level table. -/
theorem iterateBlossomDuals_keeps_address (s : ArithmeticState) (n address : ℕ)
    (untouched : ∀ i < n, blossomNodeAt s i ≠ 0 → blossomRoleAt s i ≠ 0 →
      address ≠ s.nr 75 + blossomNodeAt s i) : iterateBlossomDuals s n address = s.rm address := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have before := ih (fun i hi => untouched i (Nat.lt.step hi))
    by_cases skip : blossomNodeAt s n = 0 ∨ blossomRoleAt s n = 0
    · simpa only [iterateBlossomDuals, modifyBlossomDualAt_with_real, if_pos skip] using before
    · push_neg at skip
      have distinct := untouched n (Nat.lt_succ_self _) skip.1 skip.2
      simpa only [iterateBlossomDuals, modifyBlossomDualAt_with_real, skip.1, skip.2, false_or,
        if_false, Function.update_of_ne distinct] using before














end VehicleRoutingSurvey.Routing
end RppSource_MatchingSearchDualRAM

/-! matching/MatchingContractRowsRAM.lean -/
section RppSource_MatchingContractRowsRAM
namespace VehicleRoutingSurvey.Routing

































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





end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractRowsRAM

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

theorem contractionFreshOriginalsBefore_congr {s t : ArithmeticState}
    (fixed : ∀ r ∈ ([12, 13, 14, 51, 55, 57, 83, 84, 89] : List ℕ), t.nr r = s.nr r)
    (natural : t.nm = s.nm) : contractionFreshOriginalsBefore t = contractionFreshOriginalsBefore s := by
  have marks := matchingContractionMaskAddresses_congr (s := s) (t := t)
    (fun r listed => fixed r (by simp at listed ⊢; omega))
    (fun a _ => congrFun natural _) (fun a _ => congrFun natural _)
  unfold contractionFreshOriginalsBefore
  rw [fixed 55 (by decide)]
  apply List.filter_congr
  intro j _
  apply decide_eq_decide.mpr
  simp only [originalTopRepresentative, fixed 57 (by decide), fixed 89 (by decide), fixed 51 (by decide), natural, marks]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionPrefixView

/-! matching/MatchingContractHandler.lean -/
section RppSource_MatchingContractHandler
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private def savedMatchingContractionData (s : ArithmeticState) : ArithmeticState :=
  {s with
    pc := 3
    nr := Function.update (Function.update (Function.update s.nr 23 0) 81 (s.nr 12)) 82 (s.nr 14)}

private theorem stabilizeMatchingContractionData_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) : BlockRuns stabilizeMatchingContractionData 3 s (savedMatchingContractionData s) := by
  apply BlockRuns.of_running_exit
  · simp [stabilizeMatchingContractionData, savedMatchingContractionData, entry, running, arithmeticStep,
      Function.iterate_succ_apply']
  · exact running
  · rfl

private def restoredMatchingContractionData (s : ArithmeticState) : ArithmeticState :=
  {s with pc := 2, nr := Function.update (Function.update s.nr 12 (s.nr 81)) 14 (s.nr 82)}

private theorem restoreMatchingContractionData_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 14 = 0) :
    BlockRuns restoreMatchingContractionData 2 s (restoredMatchingContractionData s) := by
  apply BlockRuns.of_running_exit
  · simp [restoreMatchingContractionData, restoredMatchingContractionData, entry, running, zero, arithmeticStep,
      Function.iterate_succ_apply']
  · exact running
  · rfl





























private theorem matchingContractionLayout_congr {s t : ArithmeticState} (layout : MatchingContractionLayout s)
    (registers : ∀ r, r ∉ [0, 6, 7, 10, 11, 23, 81, 82] → t.nr r = s.nr r)
    (natural : t.nm = s.nm) : MatchingContractionLayout t := by
  rcases layout with ⟨⟩
  constructor <;> simp (disch := decide) only [registers, natural, originalTopRepresentative] at * <;> assumption

theorem matchingContractionStructure_spec (s : ArithmeticState) (layout : MatchingContractionLayout s)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t ticks, ticks ≤ 120 * s.nr 55 + 78 ∧ BlockRuns matchingContractionStructure ticks s t ∧
      t.halted = false ∧ t.nr 87 ≤ s.nr 55 ∧ t.rr 15 = s.rr 15 + s.rr 1 ∧
      (∀ a < s.nr 51, t.nm a = s.nm a) ∧ (∀ a < s.nr 62, t.rm a = s.rm a) ∧
      (∀ r, r ∉ [0, 6, 7, 10, 11, 15, 16, 17, 18, 19, 23, 68, 76, 81, 82, 87, 99] → t.nr r = s.nr r) ∧
      t.rm = Function.update (iterateBlossomDuals {s with rm := advancedEffectiveMemory s} (s.nr 55))
        (s.nr 75+s.nr 76) 0 ∧
      (s.nr 52+s.nr 55 ≤ s.nr 86 → s.nr 74+s.nr 55 ≤ s.nr 86 → MatchingContractionPrefixView s t) := by
  let seeded := savedMatchingContractionData s
  have save : BlockRuns stabilizeMatchingContractionData 3 s seeded := stabilizeMatchingContractionData_spec s entry running
  let a := {seeded with pc := 0}
  have aFrame (r : ℕ) (safe : r ∉ [23, 81, 82]) : a.nr r = s.nr r := by
    have away23 : r ≠ 23 := by simp at safe; omega
    have away81 : r ≠ 81 := by simp at safe; omega
    have away82 : r ≠ 82 := by simp at safe; omega
    simp [a, seeded, savedMatchingContractionData, Function.update_of_ne away23, Function.update_of_ne away81,
      Function.update_of_ne away82]
  have aOne : a.nr 9 = 1 := (aFrame 9 (by decide)).trans one
  obtain ⟨dual, dualTicks, dualCost, dualRun, dualLive, dualNat, _, dualTime, dualZero, dualKeeps, dualReal⟩ :=
    advanceMatchingEventDuals_spec a rfl running aOne
  let b := {dual with pc := 0}
  let restored := restoredMatchingContractionData b
  have restore : BlockRuns restoreMatchingContractionData 2 b restored := restoreMatchingContractionData_spec b rfl dualLive dualZero
  let c := {restored with pc := 0}
  have leftAt : b.nr 81 = s.nr 12 := (dualKeeps 81 (by decide)).trans (by simp [a, seeded, savedMatchingContractionData])
  have rightAt : b.nr 82 = s.nr 14 := (dualKeeps 82 (by decide)).trans (by simp [a, seeded, savedMatchingContractionData])
  have cFrame (r : ℕ) (safe : r ∉ [0, 6, 7, 10, 11, 23, 81, 82]) : c.nr r = s.nr r := by
    by_cases isBase : r = 12
    · subst r
      simpa [c, restored, restoredMatchingContractionData] using leftAt
    by_cases isLength : r = 14
    · subst r
      simpa [c, restored, restoredMatchingContractionData] using rightAt
    have bFrame : b.nr r = s.nr r := (dualKeeps r (by simp at safe ⊢; omega)).trans (aFrame r (by simp at safe ⊢; omega))
    simpa [c, restored, restoredMatchingContractionData, Function.update_of_ne isBase, Function.update_of_ne isLength] using bFrame
  have cNat : c.nm = s.nm := dualNat
  have cZero : c.nr 23 = 0 := by
    have atZero : b.nr 23 = 0 := (dualKeeps 23 (by decide)).trans (by simp [a, seeded, savedMatchingContractionData])
    simpa [c, restored, restoredMatchingContractionData] using atZero
  obtain ⟨t, tailTicks, tailCost, tail, tailLive, rowBound, natural, real, tailKeeps, tailReal, tailView⟩ :=
    finishMatchingContractionStructure_spec c (matchingContractionLayout_congr layout cFrame cNat) rfl dualLive
      ((cFrame 9 (by decide)).trans one) cZero
  have run : BlockRuns matchingContractionStructure (3 + (dualTicks + (2 + tailTicks))) s _ :=
    save.append (dualRun.append (restore.append tail))
  have lowerReal (addr : ℕ) (lower : addr < s.nr 62) : c.rm addr = s.rm addr := by
    change dual.rm addr = _
    rw [dualReal]
    exact matchingEventDualMemory_keeps_prefix a (s.nr 62) addr lower
      (by rw [aFrame 62 (by decide)]) (by rw [aFrame 75 (by decide)]; exact layout.nodeDualAfter)
  refine ⟨_, _, ?_, run, tailLive, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [aFrame 55 (by decide)] at dualCost
    rw [cFrame 55 (by decide)] at tailCost
    omega
  · change t.nr 87 ≤ s.nr 55
    simpa only [cFrame 55 (by decide)] using rowBound
  · have frame : t.rr 15 = c.rr 15 := by
      rw [← tail.run]
      exact arithmeticRun_keeps_real_from_destination_list [0] (by decide) (by decide) c tailTicks
    exact frame.trans dualTime
  · intro addr lower
    exact (natural addr (by rwa [cFrame 51 (by decide)])).trans (congrFun cNat addr)
  · intro addr lower
    exact (real addr (by rwa [cFrame 62 (by decide)])).trans (lowerReal addr lower)
  · intro r safe
    exact (tailKeeps r (by simp at safe ⊢; omega)).trans (cFrame r (by simp at safe ⊢; omega))
  · have sameEffective : advancedEffectiveMemory a = advancedEffectiveMemory s := by
      funext addr
      simp [a,seeded,savedMatchingContractionData,advancedEffectiveMemory,effectivePotentialAfterDelta,effectiveRoleAt] <;> rfl
    have sameCut (i : ℕ) : iterateBlossomDuals {a with rm := advancedEffectiveMemory a} i =
        iterateBlossomDuals {s with rm := advancedEffectiveMemory s} i := by
      induction i with
      | zero => exact sameEffective
      | succ i ih =>
        simp only [iterateBlossomDuals,modifyBlossomDualAt,blossomNodeAt,blossomRoleAt,blossomDualAfterDelta,
          aFrame 74 (by decide),aFrame 51 (by decide),aFrame 75 (by decide),ih]
        rfl
    change t.rm = _
    rw [tailReal]
    change Function.update dual.rm (c.nr 75+c.nr 76) 0 = _
    rw [dualReal,sameCut,cFrame 75 (by decide),cFrame 76 (by decide),aFrame 55 (by decide)]
  · intro parentBefore nodeBefore
    have ordinary := tailView
      (by rwa [cFrame 52 (by decide), cFrame 55 (by decide), cFrame 86 (by decide)])
      (by rwa [cFrame 74 (by decide), cFrame 55 (by decide), cFrame 86 (by decide)])
    have oldRows : absorbedMatchingOuterRows c = absorbedMatchingOuterRows s :=
      absorbedMatchingOuterRows_congr (fun r listed => cFrame r (by simp at listed ⊢; omega))
        (fun a _ => congrFun cNat _) (fun a _ => congrFun cNat _)
        (fun a _ => congrFun cNat _) (fun a _ => congrFun cNat _)
    have oldFresh : contractionFreshOriginalsBefore c = contractionFreshOriginalsBefore s :=
      contractionFreshOriginalsBefore_congr (fun r listed => cFrame r (by simp at listed ⊢; omega)) cNat
    refine ⟨?_,ordinary.absorbedCount.trans (congrArg List.length oldRows),
      ordinary.freshCount.trans (congrArg List.length oldFresh), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨w,z,n,pc,live,unit,nm,regs,write,cur,count,top,rm,keep⟩ := ordinary.writer.allocation
      exact ⟨w,z,n,pc,live,unit,nm.trans cNat,fun r safe => (regs r safe).trans (cFrame r safe),write,cur,count,top,rm,keep⟩
    · intro j hi
      change t.nm (t.nr 86+j) = _
      simpa only [oldRows] using ordinary.absorbed j hi
    · intro j hi
      change t.nm (t.nr 88+j) = _
      simpa only [oldFresh] using ordinary.fresh j hi

    · intro addr pastRep pastParent belowNode belowStart belowCount belowRows
      refine (ordinary.cacheNatural addr ?_ ?_ ?_ ?_ ?_ ?_).trans (congrFun cNat addr) <;>
        simp only [cFrame 57 (by decide),cFrame 55 (by decide),cFrame 52 (by decide),cFrame 74 (by decide),
          cFrame 77 (by decide),cFrame 78 (by decide),cFrame 76 (by decide),cFrame 86 (by decide)] <;> assumption
    · intro addr past below
      refine (ordinary.cacheReal addr (by rwa [cFrame 62 (by decide),cFrame 55 (by decide)])
        (by rwa [cFrame 75 (by decide)])).trans ?_
      change dual.rm addr = s.rm addr
      rw [dualReal, iterateBlossomDuals_keeps_address]
      · change advancedEffectiveMemory a addr = s.rm addr
        simp only [advancedEffectiveMemory, aFrame 62 (by decide), aFrame 55 (by decide),
          Nat.not_lt_of_ge past, and_false, if_false]
        <;> rfl
      · intro i _ _ _
        change addr ≠ a.nr 75 + _
        rw [aFrame 75 (by decide)]
        omega
    · intro pastParent belowNode j hj
      have before := ordinary.representative (by rwa [cFrame 52 (by decide),cFrame 55 (by decide),cFrame 57 (by decide)])
        (by rwa [cFrame 57 (by decide),cFrame 55 (by decide),cFrame 74 (by decide)]) j (by rwa [cFrame 55 (by decide)])
      have marks := matchingContractionMaskAddresses_congr (s := s) (t := c)
        (fun r listed => cFrame r (by simp at listed ⊢; omega)) (fun _ _ => congrFun cNat _) (fun _ _ => congrFun cNat _)
      change t.nm _ = _
      have atIndex := before
      simp only [cFrame 57 (by decide), cFrame 89 (by decide), cFrame 12 (by decide),
        originalTopRepresentative, cNat, marks] at atIndex ⊢
      exact atIndex

    · intro repEnd parentEnd pointers counts j hj
      have marks := matchingContractionMaskAddresses_congr (s := s) (t := c)
        (fun r listed => cFrame r (by simp at listed ⊢; omega)) (fun _ _ => congrFun cNat _) (fun _ _ => congrFun cNat _)
      have result := ordinary.topNodes (by rwa [cFrame 57 (by decide),cFrame 55 (by decide),cFrame 74 (by decide)])
        (by rwa [cFrame 52 (by decide),cFrame 55 (by decide),cFrame 74 (by decide)])
        (by rwa [cFrame 74 (by decide),cFrame 55 (by decide),cFrame 77 (by decide)])
        (by rwa [cFrame 74 (by decide),cFrame 55 (by decide),cFrame 78 (by decide)]) j (by rwa [cFrame 55 (by decide)])
      change t.nm _ = _
      by_cases atBase : j = s.nr 12 <;> by_cases on : s.nr 89+j ∈ matchingContractionMaskAddresses s <;>
        simpa only [cFrame 74 (by decide),cFrame 12 (by decide),cFrame 76 (by decide),cFrame 89 (by decide),cNat,marks,
          atBase,on,if_true,if_false] using result
    · intro j hj
      have marks := matchingContractionMaskAddresses_congr (s := s) (t := c)
        (fun r listed => cFrame r (by simp at listed ⊢; omega)) (fun _ _ => congrFun cNat _) (fun _ _ => congrFun cNat _)
      change t.nm _ = _
      simpa only [cFrame 89 (by decide), marks] using ordinary.cycleMask j ((cFrame 55 (by decide)).symm ▸ hj)
    · intro k size parent depth beforeRep beforeNode old base cycle baseAt encoded cycleMarks
      have marks := matchingContractionMaskAddresses_congr (s := s) (t := c)
        (fun r listed => cFrame r (by simp at listed ⊢; omega)) (fun _ _ => congrFun cNat _) (fun _ _ => congrFun cNat _)
      have model := ordinary.forest ((cFrame 55 (by decide)).trans size)
        (by rwa [cFrame 52 (by decide),cFrame 51 (by decide)]) (by rwa [cFrame 53 (by decide),cFrame 51 (by decide)])
        (by rwa [cFrame 53 (by decide),cFrame 57 (by decide)]) (by rwa [cFrame 57 (by decide),cFrame 74 (by decide)])
        old base cycle ((cFrame 12 (by decide)).trans baseAt)
        (by rwa [cFrame 51 (by decide),cNat]) (fun v => by rw [cFrame 89 (by decide),marks]; exact cycleMarks v)
      rw [cFrame 51 (by decide)] at model
      exact model





end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractHandler

open VehicleRoutingSurvey.Routing SupplyChainTheory in
theorem solution : (fun {P : Prop} (_ : P) => P) (@VehicleRoutingSurvey.Routing.matchingContractionStructure_spec) :=
  @VehicleRoutingSurvey.Routing.matchingContractionStructure_spec
