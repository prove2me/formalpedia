-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.MatchingSelectedExpansion.openedCore
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T16:03:50.10424+00:00
-- url     : https://prove2.me/submissions/529c2cae-80a4-4ea2-9428-6047f3bdfbf3

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces
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

/-! matching/AlternatingForestGrow.lean -/
section RppSource_AlternatingForestGrow
namespace VehicleRoutingSurvey.Routing









theorem AlternatingForestState.grow_valid {α : Type*} [DecidableEq α]
    {state : AlternatingForestState α} {mate : α → Option α} {tight : α → α → Prop}
    (valid : state.valid mate tight) {source inner outer : α} {parent : Option α}
    (fromRole : state.role source = .outer parent)
    (innerRole : state.role inner = .unlabelled) (outerRole : state.role outer = .unlabelled)
    (distinct : inner ≠ outer) (mateInner : mate inner = some outer) (mateOuter : mate outer = some inner)
    (tightIncoming : tight source inner) (tightMatched : tight inner outer) :
    (state.grow source inner outer).valid mate tight := by
  let after := state.grow source inner outer
  have unchanged {x} (marked : state.role x ≠ .unlabelled) :
      after.role x = state.role x ∧ after.depth x = state.depth x := by
    have notInner : x ≠ inner := fun h => marked (h.symm ▸ innerRole)
    have notOuter : x ≠ outer := fun h => marked (h.symm ▸ outerRole)
    simp [after, grow, notInner, notOuter]
  have fromMarked : state.role source ≠ .unlabelled := by simp [fromRole]
  have fromUnchanged := unchanged fromMarked
  have fromDifferent : outer ≠ source := by
    intro equal
    exact fromMarked (equal ▸ outerRole)
  have newInner : after.role inner = .inner source := by simp [after, grow]
  have newOuter : after.role outer = .outer (some inner) := by simp [after, grow, distinct.symm]
  have innerDepth : after.depth inner = state.depth source + 1 := by simp [after, grow]
  have outerDepth : after.depth outer = state.depth source + 2 := by simp [after, grow, distinct.symm]
  change after.valid mate tight
  intro x
  by_cases isInner : x = inner
  · subst x
    rw [newInner]
    refine ⟨⟨parent, fromUnchanged.1.trans fromRole⟩, ?_, ⟨outer, mateInner, newOuter⟩, tightIncoming, ?_⟩
    · exact fun h => fromDifferent (Option.some.inj (mateInner.symm.trans h))
    · rw [fromUnchanged.2, innerDepth]
      omega
  by_cases isOuter : x = outer
  · subst x
    rw [newOuter]
    refine ⟨⟨source, newInner⟩, mateOuter, mateInner, tightMatched, ?_⟩
    rw [innerDepth, outerDepth]
    omega
  have xRole : after.role x = state.role x := by simp [after, grow, isInner, isOuter]
  have xDepth : after.depth x = state.depth x := by simp [after, grow, isInner, isOuter]
  rw [xRole]
  have old := valid x
  cases kind : state.role x with
  | unlabelled => trivial
  | outer parent' =>
    try rw [kind] at old
    cases parent' with
    | none => exact old
    | some p =>
      obtain ⟨⟨q, pRole⟩, xMate, pMate, edge, earlier⟩ := old
      have pMarked : state.role p ≠ .unlabelled := by simp [pRole]
      obtain ⟨pSame, pDepth⟩ := unchanged pMarked
      exact ⟨⟨q, pSame.trans pRole⟩, xMate, pMate, edge, by simpa only [pDepth, xDepth] using earlier⟩
  | inner p =>
    try rw [kind] at old
    obtain ⟨⟨q, pRole⟩, notMate, ⟨child, childMate, childRole⟩, edge, earlier⟩ := old
    have pMarked : state.role p ≠ .unlabelled := by simp [pRole]
    have childMarked : state.role child ≠ .unlabelled := by simp [childRole]
    obtain ⟨pSame, pDepth⟩ := unchanged pMarked
    exact ⟨⟨q, pSame.trans pRole⟩, notMate, ⟨child, childMate, (unchanged childMarked).1.trans childRole⟩,
      edge, by simpa only [pDepth, xDepth] using earlier⟩

end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestGrow

/-! matching/MatchingSearchTopology.lean -/
section RppSource_MatchingSearchTopology
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



theorem effectiveVertexPotential_erase_zero {k : ℕ} (cuts : Finset (Finset (Fin k)))
    {B : Finset (Fin k)} (present : B ∈ cuts) (potential : Fin k → ℝ)
    (cutDual : Finset (Fin k) → ℝ) (zero : cutDual B = 0) (v : Fin k) :
    effectiveVertexPotential (cuts.erase B) potential cutDual v = effectiveVertexPotential cuts potential cutDual v := by
  simp only [effectiveVertexPotential, Finset.sum_filter]
  congr 1
  simpa [zero] using Finset.sum_erase_add cuts (fun S => if v ∈ S then cutDual S else 0) present










end VehicleRoutingSurvey.Routing
end RppSource_MatchingSearchTopology

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

/-! matching/AlternatingForestGrowRAM.lean -/
section RppSource_AlternatingForestGrowRAM
namespace VehicleRoutingSurvey.Routing



def alternatingForestGrownMemory (s : ArithmeticState) : ℕ → ℕ :=
  let withInnerRole := Function.update s.nm (s.nr 3 + s.nr 1) 2
  let withOuterRole := Function.update withInnerRole (s.nr 3 + s.nr 2) 1
  let withInnerParent := Function.update withOuterRole (s.nr 4 + s.nr 1) (s.nr 0)
  let withOuterParent := Function.update withInnerParent (s.nr 4 + s.nr 2) (s.nr 1)
  let predecessorDepth := s.nm (s.nr 5 + s.nr 0)
  let withInnerDepth := Function.update withOuterParent (s.nr 5 + s.nr 1) (predecessorDepth + 1)
  Function.update withInnerDepth (s.nr 5 + s.nr 2) (predecessorDepth + 2)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem alternatingForestGrowBlock_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    let result := (arithmeticStep alternatingForestGrowBlock)^[18] s
    BlockRuns alternatingForestGrowBlock 18 s result ∧
      result.nm = alternatingForestGrownMemory s ∧ result.rm = s.rm ∧ result.rr = s.rr ∧
      ∀ reg < 6, result.nr reg = s.nr reg := by
  let result := (arithmeticStep alternatingForestGrowBlock)^[18] s
  have computed : result.pc = alternatingForestGrowBlock.length ∧ result.halted = false ∧
      result.nm = alternatingForestGrownMemory s ∧ result.rm = s.rm ∧ result.rr = s.rr := by
    simp [result, alternatingForestGrowBlock, arithmeticStep, Function.iterate_succ_apply',
      alternatingForestGrownMemory, entry, running, Nat.add_assoc]
  refine ⟨BlockRuns.of_running_exit rfl computed.2.1 computed.1,
    computed.2.2.1, computed.2.2.2.1, computed.2.2.2.2, ?_⟩
  intro reg argument
  have notAddress : reg ≠ 6 := by omega
  have notValue : reg ≠ 7 := by omega
  have notDepth : reg ≠ 8 := by omega
  simp [result, alternatingForestGrowBlock, arithmeticStep, Function.iterate_succ_apply',
    entry, running, notAddress, notValue, notDepth]

end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestGrowRAM

/-! matching/AlternatingForestMemory.lean -/
section RppSource_AlternatingForestMemory
namespace VehicleRoutingSurvey.Routing







theorem alternatingForestGrownMemory_encodes {n : ℕ}
    {forest : AlternatingForestState (Fin n)} {base : ℕ} {s : ArithmeticState}
    (before : AlternatingForestMemory forest base s.nm) {source inner outer : Fin n}
    (sourceArg : s.nr 0 = source.val) (innerArg : s.nr 1 = inner.val) (outerArg : s.nr 2 = outer.val)
    (roleBase : s.nr 3 = base) (parentBase : s.nr 4 = base + n) (depthBase : s.nr 5 = base + n + n)
    (distinct : inner ≠ outer) :
    AlternatingForestMemory (forest.grow source inner outer) base (alternatingForestGrownMemory s) := by
  intro v
  have sourceDepth := (before source).2.2
  have oldRole := (before v).1
  have oldParent := (before v).2.1
  have oldDepth := (before v).2.2
  have innerLt := inner.isLt
  have outerLt := outer.isLt
  have vLt := v.isLt
  have different : inner.val ≠ outer.val := fun equal => distinct (Fin.ext equal)
  by_cases isInner : v = inner
  · subst v
    simp (disch := omega) [alternatingForestGrownMemory, sourceArg, innerArg, outerArg,
      roleBase, parentBase, depthBase, Function.update_apply, AlternatingForestState.grow,
      alternatingRoleCode, alternatingParentCode, sourceDepth]
  by_cases isOuter : v = outer
  · subst v
    simp (disch := omega) [alternatingForestGrownMemory, sourceArg, innerArg, outerArg,
      roleBase, parentBase, depthBase, Function.update_apply, AlternatingForestState.grow,
      alternatingRoleCode, alternatingParentCode, sourceDepth, distinct.symm]
  have notInner : v.val ≠ inner.val := fun equal => isInner (Fin.ext equal)
  have notOuter : v.val ≠ outer.val := fun equal => isOuter (Fin.ext equal)
  simp (disch := omega) [alternatingForestGrownMemory, sourceArg, innerArg, outerArg,
    roleBase, parentBase, depthBase, Function.update_apply, AlternatingForestState.grow,
    isInner, isOuter, oldRole, oldParent, oldDepth]



end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestMemory

/-! matching/MatchingWarmPrimal.lean -/
section RppSource_MatchingWarmPrimal
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory













theorem CompactTopMatching.crossing_endpoints {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    (top : CompactTopMatching part) {u v : Fin k} (edge : s(u, v) ∈ state.edges)
    (separate : part.blocks.block u ≠ part.blocks.block v) :
    part.representative u = u ∧ part.representative v = v := by
  have atBase {a b : Fin k} (present : s(a, b) ∈ state.edges)
      (separated : part.blocks.block a ≠ part.blocks.block b) : part.representative a = a := by
    by_contra notBase
    obtain ⟨inner, member, incident, allInside⟩ := top.interior a a
      (part.blocks.self_mem a (Finset.mem_univ a)) (Ne.symm notBase)
    have covered := (state.perfect.1 _ present).2 a (Sym2.mem_mk_left _ _)
    have equal := (state.perfect.2 a covered).unique ⟨present, Sym2.mem_mk_left _ _⟩ ⟨member, incident⟩
    have bIn := allInside b (equal ▸ Sym2.mem_mk_right a b)
    exact separated (part.blocks.same_of_mem (Finset.mem_univ a) bIn).symm
  exact ⟨atBase edge separate, atBase (Sym2.eq_swap ▸ edge) separate.symm⟩








end VehicleRoutingSurvey.Routing
end RppSource_MatchingWarmPrimal

/-! matching/MatchingExpansionPartition.lean -/
section RppSource_MatchingExpansionPartition
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory









theorem CompactMatchingPartition.openZeroCut_block {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    {B : Finset (Fin k)} (top : B ∈ Finset.univ.image part.blocks.block)
    (present : B ∈ state.cuts) (zero : state.cutDual B = 0)
    (children : MatchingExpansionChildren state B) (v : Fin k) :
    (part.openZeroCut top present zero children).blocks.block v =
      if v ∈ B then children.block v else part.blocks.block v := by
  change (if part.blocks.block v = B then children.block v else part.blocks.block v) = _
  rw [selectExpansionBlock part top v]

theorem CompactMatchingPrimalDual.partialMate_eraseZeroCut {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) {B : Finset (Fin k)}
    (present : B ∈ state.cuts) (zero : state.cutDual B = 0) :
    (state.eraseZeroCut present zero).partialMate = state.partialMate := by
  funext v
  rfl



end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionPartition

/-! matching/MatchingCycleRecordRAM.lean -/
section RppSource_MatchingCycleRecordRAM
namespace VehicleRoutingSurvey.Routing

































theorem readMatchingCycleHeader_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    ∃ t, BlockRuns readMatchingCycleHeader 4 s t ∧ t.halted = false ∧
      t.nr 18 = s.nm (s.nr 77 + s.nr 22) ∧ t.nr 19 = s.nm (s.nr 78 + s.nr 22) ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 18, 19] → t.nr r = s.nr r := by
  let t := (arithmeticStep readMatchingCycleHeader)^[4] s
  have effect : t.pc = readMatchingCycleHeader.length ∧ t.halted = false ∧
      t.nr 18 = s.nm (s.nr 77 + s.nr 22) ∧ t.nr 19 = s.nm (s.nr 78 + s.nr 22) ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, readMatchingCycleHeader, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1,
    effect.2.2.1, effect.2.2.2.1, effect.2.2.2.2.1, effect.2.2.2.2.2.1, effect.2.2.2.2.2.2, ?_⟩
  intro r away
  exact arithmeticRun_keeps_from_destination_list [0, 6, 18, 19] (by decide) away s 4



def readMatchingCycleChildValue (s : ArithmeticState) : MatchingCycleChild :=
  ⟨s.nr 15, s.nr 25, s.nr 16, s.nr 17⟩

theorem readMatchingCycleChild_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns readMatchingCycleChild 10 s t ∧ t.halted = false ∧
      readMatchingCycleChildValue t = matchingCycleChildAt s.nm (s.nr 18 + 4 * s.nr 7) ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 15, 16, 17, 25] → t.nr r = s.nr r := by
  let t := (arithmeticStep readMatchingCycleChild)^[10] s
  have effect : t.pc = readMatchingCycleChild.length ∧ t.halted = false ∧
      readMatchingCycleChildValue t = matchingCycleChildAt s.nm (s.nr 18 + 4 * s.nr 7) ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    have quad : s.nr 7 + s.nr 7 + (s.nr 7 + s.nr 7) = 4 * s.nr 7 := by omega
    have two : s.nr 18 + 4 * s.nr 7 + 1 + 1 = s.nr 18 + 4 * s.nr 7 + 2 := by omega
    have three : s.nr 18 + 4 * s.nr 7 + 1 + 1 + 1 = s.nr 18 + 4 * s.nr 7 + 3 := by omega
    simp [t, readMatchingCycleChild, arithmeticStep, entry, running, one, Function.iterate_succ_apply',
      readMatchingCycleChildValue, matchingCycleChildAt, quad, two, three]
  refine ⟨t, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1,
    effect.2.2.1, effect.2.2.2.1, effect.2.2.2.2.1, effect.2.2.2.2.2, ?_⟩
  intro r away
  exact arithmeticRun_keeps_from_destination_list [0, 6, 15, 16, 17, 25] (by decide) away s 10

end VehicleRoutingSurvey.Routing
end RppSource_MatchingCycleRecordRAM

/-! matching/MatchingCycleMembersRAM.lean -/
section RppSource_MatchingCycleMembersRAM
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

def matchingCycleStackAddress (s : ArithmeticState) (i : ℕ) : ℕ := s.nr 80 + 3 * i

def pushedMatchingCycleMember (s : ArithmeticState) : ℕ → ℕ :=
  let addr := matchingCycleStackAddress s (s.nr 87)
  Function.update (Function.update (Function.update s.nm addr (s.nr 15)) (addr + 1) (s.nr 25))
    (addr + 2) (s.nr 26)



theorem pushMatchingCycleMember_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns pushMatchingCycleMember 9 s t ∧ t.halted = false ∧
      t.nr 87 = s.nr 87 + 1 ∧ t.nm = pushedMatchingCycleMember s ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 87] → t.nr r = s.nr r := by
  let t := (arithmeticStep pushMatchingCycleMember)^[9] s
  have address : s.nr 87 + s.nr 87 + s.nr 87 = 3 * s.nr 87 := by omega
  have extra : s.nr 80 + 3 * s.nr 87 + 1 + 1 = s.nr 80 + 3 * s.nr 87 + 2 := by omega
  have effect : t.pc = pushMatchingCycleMember.length ∧ t.halted = false ∧
      t.nr 87 = s.nr 87 + 1 ∧ t.nm = pushedMatchingCycleMember s ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, pushMatchingCycleMember, arithmeticStep, entry, running, one, Function.iterate_succ_apply',
      pushedMatchingCycleMember, matchingCycleStackAddress, address, extra]
  refine ⟨t, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1, effect.2.2.1,
    effect.2.2.2.1, effect.2.2.2.2.1, effect.2.2.2.2.2, ?_⟩
  intro r away
  exact arithmeticRun_keeps_from_destination_list [0, 6, 87] (by decide) away s 9



theorem popMatchingCycleMember_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns popMatchingCycleMember 9 s t ∧ t.halted = false ∧ t.nr 87 = s.nr 87 - 1 ∧
      t.nr 15 = s.nm (matchingCycleStackAddress s (s.nr 87 - 1)) ∧
      t.nr 22 = s.nm (matchingCycleStackAddress s (s.nr 87 - 1) + 1) ∧
      t.nr 26 = s.nm (matchingCycleStackAddress s (s.nr 87 - 1) + 2) ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 15, 22, 26, 87] → t.nr r = s.nr r := by
  let t := (arithmeticStep popMatchingCycleMember)^[9] s
  let i := s.nr 87 - 1
  have address : i + i + i = 3 * i := by omega
  have extra : s.nr 80 + 3 * i + 1 + 1 = s.nr 80 + 3 * i + 2 := by omega
  have effect : t.pc = popMatchingCycleMember.length ∧ t.halted = false ∧ t.nr 87 = s.nr 87 - 1 ∧
      t.nr 15 = s.nm (matchingCycleStackAddress s (s.nr 87 - 1)) ∧
      t.nr 22 = s.nm (matchingCycleStackAddress s (s.nr 87 - 1) + 1) ∧
      t.nr 26 = s.nm (matchingCycleStackAddress s (s.nr 87 - 1) + 2) ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    have rewriteIndex : s.nr 87 - 1 = i := rfl
    simp [t, popMatchingCycleMember, arithmeticStep, entry, running, one, Function.iterate_succ_apply',
      matchingCycleStackAddress, rewriteIndex, address, extra]
  obtain ⟨exit, live, count, rep, node, root, natural, real, registers⟩ := effect
  refine ⟨t, BlockRuns.of_running_exit rfl live exit, live, count, rep, node, root, natural, real, registers, ?_⟩
  intro r away
  exact arithmeticRun_keeps_from_destination_list [0, 6, 15, 22, 26, 87] (by decide) away s 9

















theorem mapMatchingCycleNodeMembers_keeps_register {s t : ArithmeticState} {steps r : ℕ}
    (run : BlockRuns mapMatchingCycleNodeMembers steps s t)
    (away : r ∉ [0, 6, 7, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 28, 87]) : t.nr r = s.nr r := by
  rw [← run.run]
  exact arithmeticRun_keeps_from_destination_list [0, 6, 7, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 28, 87]
    (by decide) away s steps

private def onlyReadsReals : ArithmeticInstruction → Bool
  | .realConst _ _ | .realAdd _ _ _ | .realSub _ _ _ | .realMul _ _ _ | .realDiv _ _ _
  | .realLoad _ _ | .realStore _ _ => false
  | _ => true

private theorem arithmeticStep_keeps_reals {p : List ArithmeticInstruction} (readOnly : p.all onlyReadsReals = true)
    (s : ArithmeticState) : (arithmeticStep p s).rr = s.rr ∧ (arithmeticStep p s).rm = s.rm := by
  by_cases stopped : s.halted = true
  · simp [arithmeticStep, stopped]
  cases fetched : p[s.pc]? with
  | none => simp [arithmeticStep, stopped, fetched]
  | some ins =>
    have reads := List.all_eq_true.mp readOnly ins (List.mem_of_getElem? fetched)
    cases ins <;> simp [arithmeticStep, stopped, fetched, onlyReadsReals] at reads ⊢

private theorem arithmeticRun_keeps_reals {p : List ArithmeticInstruction} (readOnly : p.all onlyReadsReals = true)
    (s : ArithmeticState) (ticks : ℕ) :
    ((arithmeticStep p)^[ticks] s).rr = s.rr ∧ ((arithmeticStep p)^[ticks] s).rm = s.rm := by
  induction ticks with
  | zero => exact ⟨rfl, rfl⟩
  | succ ticks ih =>
    rw [Function.iterate_succ_apply']
    have step := arithmeticStep_keeps_reals readOnly ((arithmeticStep p)^[ticks] s)
    exact ⟨step.1.trans ih.1, step.2.trans ih.2⟩

theorem mapMatchingCycleNodeMembers_keeps_reals {s t : ArithmeticState} {steps : ℕ}
    (run : BlockRuns mapMatchingCycleNodeMembers steps s t) : t.rr = s.rr ∧ t.rm = s.rm := by
  rw [← run.run]
  exact arithmeticRun_keeps_reals (by decide) s steps

end VehicleRoutingSurvey.Routing
end RppSource_MatchingCycleMembersRAM

/-! matching/MatchingMemberTree.lean -/
section RppSource_MatchingMemberTree
namespace VehicleRoutingSurvey.Routing



namespace MatchingMemberTree



def nodes : MatchingMemberTree → ℕ
  | .nil => 0
  | .leaf _ siblings => 1 + siblings.nodes
  | .blossom _ _ children siblings => 1 + children.nodes + siblings.nodes





theorem nodes_add_arity_le (tree : MatchingMemberTree) (properTree : tree.proper) :
    tree.nodes + tree.arity ≤ 2 * tree.leaves.length := by
  induction tree with
  | nil => simp [nodes, arity, leaves]
  | leaf v siblings ih =>
    have bound := ih properTree
    simp only [nodes, arity, leaves, List.length_cons]
    omega
  | blossom representative node children siblings ihChildren ihSiblings =>
    obtain ⟨_, branching, childrenWellFormed, siblingsWellFormed⟩ := properTree
    have childrenBound := ihChildren childrenWellFormed
    have siblingsBound := ihSiblings siblingsWellFormed
    simp only [nodes, arity, leaves, List.length_append]
    omega







@[simp] theorem rootKeys_length (tree : MatchingMemberTree) : tree.rootKeys.length = tree.arity := by
  induction tree with
  | nil => rfl
  | leaf v siblings ih => simp [rootKeys, arity, ih, Nat.add_comm]
  | blossom r node children siblings _ ih => simp [rootKeys, arity, ih, Nat.add_comm]





theorem encoded_congr {tree : MatchingMemberTree} {before after : ℕ → ℕ} {startBase countBase : ℕ}
    {untouched : ℕ → Prop} (input : tree.encoded before startBase countBase)
    (frame : tree.readable before startBase countBase untouched)
    (keeps : ∀ a, untouched a → after a = before a) : tree.encoded after startBase countBase := by
  induction tree with
  | nil => trivial
  | leaf v siblings ih => exact ih input frame
  | blossom r node children siblings ihChildren ihSiblings =>
    obtain ⟨count, records, childInput, siblingInput⟩ := input
    obtain ⟨header, total, region, childFrame, siblingFrame⟩ := frame
    refine ⟨(keeps _ total).trans count, ?_, ihChildren childInput childFrame, ihSiblings siblingInput siblingFrame⟩
    intro i hi
    have index : i < children.arity := by simpa using hi
    have zero : untouched (before (startBase + node) + 4 * i) := by simpa using region i index 0 (by decide)
    have one := region i index 1 (by decide)
    have restored := records i hi
    simpa only [keeps _ header, rootKey, matchingCycleChildAt, keeps _ zero, keeps _ one] using restored



end MatchingMemberTree

end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberTree

/-! matching/MatchingMemberStack.lean -/
section RppSource_MatchingMemberStack
namespace VehicleRoutingSurvey.Routing



namespace MatchingMemberJob



def visits (job : MatchingMemberJob) : ℕ := 1 + (job.children.map MatchingMemberTree.nodes).getD 0

def proper (job : MatchingMemberJob) : Prop :=
  match job.children with
  | none => job.node = 0
  | some children => 0 < job.node ∧ 2 ≤ children.arity ∧ children.proper





def work (stack : List MatchingMemberJob) : ℕ := (stack.map visits).sum

theorem work_append (left right : List MatchingMemberJob) : work (left ++ right) = work left + work right := by
  simp [work, List.sum_append]





end MatchingMemberJob

namespace MatchingMemberTree



theorem jobs_length (tree : MatchingMemberTree) (owner : Option ℕ) : (tree.jobs owner).length = tree.arity := by
  induction tree with
  | nil => rfl
  | leaf v siblings ih => simp [jobs, arity, ih, Nat.add_comm]
  | blossom r node children siblings _ ih => simp [jobs, arity, ih, Nat.add_comm]

theorem jobs_rootKeys (tree : MatchingMemberTree) (owner : Option ℕ) :
    (tree.jobs owner).map (fun job => rootKey job.representative job.node) = tree.rootKeys := by
  induction tree with
  | nil => rfl
  | leaf v siblings ih => simp [jobs, rootKeys, ih]
  | blossom r node children siblings _ ih => simp [jobs, rootKeys, ih]

theorem jobs_owner (tree : MatchingMemberTree) (owner : Option ℕ) :
    ∀ job ∈ tree.jobs owner, job.owner = owner.getD job.representative := by
  induction tree with
  | nil => simp [jobs]
  | leaf v siblings ih =>
    intro job present
    simp only [jobs, List.mem_cons] at present
    rcases present with rfl | present
    · rfl
    · exact ih job present
  | blossom r node children siblings _ ih =>
    intro job present
    simp only [jobs, List.mem_cons] at present
    rcases present with rfl | present
    · rfl
    · exact ih job present

theorem jobs_proper (tree : MatchingMemberTree) (owner : Option ℕ) (properTree : tree.proper) :
    ∀ job ∈ tree.jobs owner, job.proper := by
  induction tree with
  | nil => simp [jobs]
  | leaf v siblings ih =>
    intro job found
    simp only [jobs, List.mem_cons] at found
    rcases found with rfl | found
    · rfl
    · exact ih properTree job found
  | blossom r node children siblings ihChildren ihSiblings =>
    obtain ⟨identifier, branching, validChildren, validSiblings⟩ := properTree
    intro job found
    simp only [jobs, List.mem_cons] at found
    rcases found with rfl | found
    · exact ⟨identifier, branching, validChildren⟩
    · exact ihSiblings validSiblings job found

theorem jobs_work (tree : MatchingMemberTree) (owner : Option ℕ) :
    MatchingMemberJob.work (tree.jobs owner) = tree.nodes := by
  induction tree with
  | nil => rfl
  | leaf v siblings ih =>
    change 1 + MatchingMemberJob.work (siblings.jobs owner) = 1 + siblings.nodes
    rw [ih]
  | blossom r node children siblings _ ih =>
    change 1 + children.nodes + MatchingMemberJob.work (siblings.jobs owner) = 1 + children.nodes + siblings.nodes
    rw [ih]

theorem jobs_inheritedFrontier (tree : MatchingMemberTree) (owner : ℕ) :
    MatchingMemberJob.frontier (tree.jobs (some owner)) = tree.leaves.map (fun v => (v, owner)) := by
  induction tree with
  | nil => rfl
  | leaf v siblings ih =>
    simpa [jobs, leaves, MatchingMemberJob.frontier, MatchingMemberJob.assignments] using congrArg ((v, owner) :: ·) ih
  | blossom r node children siblings _ ih =>
    simpa [jobs, leaves, MatchingMemberJob.frontier, MatchingMemberJob.assignments] using
      congrArg (children.leaves.map (fun v => (v, owner)) ++ ·) ih

theorem jobs_frontier_vertices (tree : MatchingMemberTree) (owner : Option ℕ) :
    (MatchingMemberJob.frontier (tree.jobs owner)).map Prod.fst = tree.leaves := by
  induction tree with
  | nil => rfl
  | leaf v siblings ih =>
    simpa [jobs, leaves, MatchingMemberJob.frontier, MatchingMemberJob.assignments] using congrArg (v :: ·) ih
  | blossom r node children siblings _ ih =>
    simpa [jobs, leaves, MatchingMemberJob.frontier, MatchingMemberJob.assignments, List.map_map, Function.comp_def] using
      congrArg (children.leaves ++ ·) ih

theorem jobs_encoded (tree : MatchingMemberTree) (owner : Option ℕ) (memory : ℕ → ℕ)
    (startBase countBase lower : ℕ) (untouched : ℕ → Prop)
    (encodedTree : tree.encoded memory startBase countBase)
    (readableTree : tree.readable memory startBase countBase untouched)
    (recordSpace : tree.recordsAbove memory startBase lower) :
    ∀ job ∈ tree.jobs owner, job.tree.encoded memory startBase countBase ∧
      job.tree.readable memory startBase countBase untouched ∧ job.tree.recordsAbove memory startBase lower := by
  induction tree with
  | nil => simp [jobs]
  | leaf v siblings ih =>
    intro job found
    simp only [jobs, List.mem_cons] at found
    rcases found with rfl | found
    · exact ⟨trivial, trivial, trivial⟩
    · exact ih encodedTree readableTree recordSpace job found
  | blossom r node children siblings _ ih =>
    obtain ⟨size, rows, childEncoding, siblingEncoding⟩ := encodedTree
    obtain ⟨header, total, cell, childReadable, siblingReadable⟩ := readableTree
    obtain ⟨space, childSpace, siblingSpace⟩ := recordSpace
    intro job found
    simp only [jobs, List.mem_cons] at found
    rcases found with rfl | found
    · exact ⟨⟨size, rows, childEncoding, trivial⟩, ⟨header, total, cell, childReadable, trivial⟩,
        ⟨space, childSpace, trivial⟩⟩
    · exact ih siblingEncoding siblingReadable siblingSpace job found

end MatchingMemberTree

namespace MatchingMemberJob





theorem visits_pos (job : MatchingMemberJob) : 0 < job.visits := by
  simp [visits]

theorem length_le_work (stack : List MatchingMemberJob) : stack.length ≤ work stack := by
  induction stack with
  | nil => rfl
  | cons head rest ih =>
    have pos := head.visits_pos
    simp only [List.length_cons, work, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem assignments_nonempty (job : MatchingMemberJob) (good : job.proper) : 0 < job.assignments.length := by
  cases owned : job.children with
  | none => simp [assignments, owned]
  | some children =>
    rw [proper, owned] at good
    obtain ⟨_, many, childrenGood⟩ := good
    have count := children.nodes_add_arity_le childrenGood
    simp only [assignments, owned, List.length_map]
    omega

theorem length_le_frontier (stack : List MatchingMemberJob) (good : ∀ job ∈ stack, job.proper) :
    stack.length ≤ (frontier stack).length := by
  induction stack with
  | nil => rfl
  | cons head rest ih =>
    have positive := head.assignments_nonempty (good head (by simp))
    have below := ih (fun job h => good job (List.mem_cons_of_mem _ h))
    simp only [frontier, List.flatMap_cons, List.length_append, List.length_cons] at below ⊢
    omega

theorem frontier_append (first second : List MatchingMemberJob) :
    frontier (first ++ second) = frontier first ++ frontier second := by simp [frontier]

theorem appendChildren_frontier (earlier : List MatchingMemberJob) (job : MatchingMemberJob)
    (children : MatchingMemberTree) (nested : job.children = some children) :
    frontier (earlier ++ children.jobs (some job.owner)) = frontier (earlier ++ [job]) := by
  rw [frontier_append, frontier_append, children.jobs_inheritedFrontier]
  simp [frontier, assignments, nested]

theorem appendChildren_work (earlier : List MatchingMemberJob) (job : MatchingMemberJob)
    (children : MatchingMemberTree) (nested : job.children = some children) :
    work (earlier ++ children.jobs (some job.owner)) + 1 = work (earlier ++ [job]) := by
  rw [work_append, work_append, children.jobs_work]
  simp [work, visits, nested] <;> omega

theorem frontier_length_le {stack : List MatchingMemberJob} {done all : List (ℕ × ℕ)}
    (same : (done ++ frontier stack).Perm all) : (frontier stack).length ≤ all.length := by
  have length := same.length_eq
  simp only [List.length_append] at length
  omega

theorem boundedAssignments_length (assignments : List (ℕ × ℕ)) (k : ℕ)
    (unique : (assignments.map Prod.fst).Nodup) (inside : ∀ p ∈ assignments, p.1 < k) :
    assignments.length ≤ k := by
  let vertices := assignments.map Prod.fst
  have values : vertices.toFinset ⊆ Finset.range k := by
    intro v found
    have inList := List.mem_toFinset.mp found
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp inList
    exact Finset.mem_range.mpr (inside p hp)
  simpa [List.toFinset_card_of_nodup unique, vertices] using Finset.card_le_card values

end MatchingMemberJob

end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberStack

/-! matching/MatchingMemberVisitRAM.lean -/
section RppSource_MatchingMemberVisitRAM
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

def matchingMemberJobWords (job : MatchingMemberJob) : ℕ × ℕ × ℕ :=
  (job.representative, job.node, job.owner)

def matchingMemberStackWords (memory : ℕ → ℕ) (address : ℕ) : ℕ × ℕ × ℕ :=
  (memory address, memory (address + 1), memory (address + 2))

def matchingMemberStackWrite (memory : ℕ → ℕ) (address : ℕ) (words : ℕ × ℕ × ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update memory address words.1) (address + 1) words.2.1)
    (address + 2) words.2.2

theorem matchingMemberStackWrite_words (memory : ℕ → ℕ) (address : ℕ) (words : ℕ × ℕ × ℕ) :
    matchingMemberStackWords (matchingMemberStackWrite memory address words) address = words := by
  rcases words with ⟨representative, node, owner⟩
  simp (disch := omega) [matchingMemberStackWrite, matchingMemberStackWords, Function.update_of_ne]

theorem matchingMemberStackWrite_unchanged (memory : ℕ → ℕ) (address : ℕ) (words : ℕ × ℕ × ℕ)
    (a : ℕ) (outside : a < address ∨ address + 3 ≤ a) : matchingMemberStackWrite memory address words a = memory a := by
  simp (disch := omega) [matchingMemberStackWrite, Function.update_of_ne]

theorem writeCycleMemberLeaf_spec (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns writeCycleMemberLeaf 2 s t ∧ t.halted = false ∧
      t.nm = Function.update s.nm (s.nr 79 + s.nr 15) (s.nr 26) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6] → t.nr r = s.nr r := by
  let t := (arithmeticStep writeCycleMemberLeaf)^[2] s
  have effect : t.pc = writeCycleMemberLeaf.length ∧ t.halted = false ∧
      t.nm = Function.update s.nm (s.nr 79 + s.nr 15) (s.nr 26) ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, writeCycleMemberLeaf, entry, running, arithmeticStep, Function.iterate_succ_apply']
  exact ⟨t, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1, effect.2.2.1,
    effect.2.2.2.1, effect.2.2.2.2, fun _ safe =>
      arithmeticRun_keeps_from_destination_list _ (by decide) safe s 2⟩

theorem clearCycleMemberMapCell_spec (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns clearCycleMemberMapCell 2 s t ∧ t.halted = false ∧
      t.nm = Function.update s.nm (s.nr 79 + s.nr 7) (s.nr 55) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6] → t.nr r = s.nr r := by
  let t := (arithmeticStep clearCycleMemberMapCell)^[2] s
  have effect : t.pc = clearCycleMemberMapCell.length ∧ t.halted = false ∧
      t.nm = Function.update s.nm (s.nr 79 + s.nr 7) (s.nr 55) ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, clearCycleMemberMapCell, entry, running, arithmeticStep, Function.iterate_succ_apply']
  exact ⟨t, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1, effect.2.2.1,
    effect.2.2.2.1, effect.2.2.2.2, fun _ safe =>
      arithmeticRun_keeps_from_destination_list _ (by decide) safe s 2⟩

private structure ClearedMatchingMemberMap (s : ArithmeticState) (i : ℕ) (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  running : m.halted = false
  index : m.nr 7 = i
  registers : ∀ r, r ∉ [0, 6, 7] → m.nr r = s.nr r
  natural : ∀ a, m.nm a = if s.nr 79 ≤ a ∧ a < s.nr 79 + i then s.nr 55 else s.nm a
  real : m.rm = s.rm
  realRegisters : m.rr = s.rr

theorem clearCycleMemberMap_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t steps, steps ≤ 5 * s.nr 55 + 2 ∧
      BlockRuns (countedLoopFromZero 9 7 55 clearCycleMemberMapCell) steps s t ∧ t.halted = false ∧
      (∀ a, t.nm a = if s.nr 79 ≤ a ∧ a < s.nr 79 + s.nr 55 then s.nr 55 else s.nm a) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 7] → t.nr r = s.nr r := by
  have initial : ClearedMatchingMemberMap s 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, ?_, rfl, rfl⟩
    · intro r safe
      exact Function.update_of_ne (by simp at safe; omega) _ _
    · intro a
      have no : ¬(s.nr 79 ≤ a ∧ a < s.nr 79 + 0) := by omega
      simp [no]
  have iteration (i : ℕ) (_ : i < s.nr 55) (m : ArithmeticState) (inv : ClearedMatchingMemberMap s i m) :
      ∃ t steps, steps ≤ 2 ∧ BlockRuns clearCycleMemberMapCell steps m t ∧ t.halted = false ∧
        ClearedMatchingMemberMap s (i+1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    obtain ⟨t, run, live, natural, real, rr, keeps⟩ := clearCycleMemberMapCell_spec m inv.entry inv.running
    have oneAt : m.nr 9 = 1 := (inv.registers 9 (by decide)).trans one
    refine ⟨t, 2, le_rfl, run, live, rfl, live, ?_, ?_, ?_, real.trans inv.real, rr.trans inv.realRegisters⟩
    · simp [keeps 7 (by decide), keeps 9 (by decide), inv.index, oneAt]
    · intro r away
      have safe : r ∉ [0, 6] := by simp at away ⊢; omega
      exact (Function.update_of_ne (by simp at away; omega) _ _).trans ((keeps r safe).trans (inv.registers r away))
    · intro a
      change t.nm a = _
      rw [natural, inv.registers 79 (by decide), inv.index, inv.registers 55 (by decide)]
      by_cases atEnd : a = s.nr 79 + i
      · have inside : s.nr 79 ≤ a ∧ a < s.nr 79 + (i+1) := by omega
        simp [atEnd, if_pos (by omega : s.nr 79 ≤ s.nr 79 + i ∧ s.nr 79 + i < s.nr 79 + (i+1))]
      · have same : (s.nr 79 ≤ a ∧ a < s.nr 79 + (i+1)) ↔ s.nr 79 ≤ a ∧ a < s.nr 79 + i := by omega
        simp [Function.update_of_ne atEnd, inv.natural, same]
  obtain ⟨t, ticks, done, budget, run⟩ := countedLoopFromZero_bounded 9 7 55 (s.nr 55) 2
    clearCycleMemberMapCell (ClearedMatchingMemberMap s) (s := s) entry running initial
    (fun _ _ inv => ⟨inv.entry, inv.running, inv.index, inv.registers 55 (by decide)⟩) iteration
  exact ⟨_, ticks, by omega, run, done.running, done.natural, done.real, done.realRegisters, done.registers⟩

def pushMatchingMemberFromCycle (newOwner : Bool) : List ArithmeticInstruction :=
  if newOwner then pushTopCycleChild else pushNestedCycleChild

theorem pushMatchingMemberFromCycle_spec (newOwner : Bool) (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0) :
    let record := matchingCycleChildAt s.nm (s.nr 18 + 4 * s.nr 7)
    let owner := if newOwner then record.representative else s.nr 26
    ∃ t steps, steps ≤ 20 ∧ BlockRuns (pushMatchingMemberFromCycle newOwner) steps s t ∧ t.halted = false ∧
      t.nr 87 = s.nr 87 + 1 ∧ t.nm = matchingMemberStackWrite s.nm (matchingCycleStackAddress s (s.nr 87))
        (record.representative, record.node, owner) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 15, 16, 17, 25, 26, 87] → t.nr r = s.nr r := by
  intro record owner
  obtain ⟨read, readRun, readLive, fields, sameNat, sameReal, sameRR, keeps⟩ :=
    readMatchingCycleChild_spec s entry running one
  let a := {read with pc := 0}
  have aOne : a.nr 9 = 1 := (keeps 9 (by decide)).trans one
  have aZero : a.nr 23 = 0 := (keeps 23 (by decide)).trans zero
  have rep : a.nr 15 = record.representative := congrArg MatchingCycleChild.representative fields
  have node : a.nr 25 = record.node := congrArg MatchingCycleChild.node fields
  have count : a.nr 87 = s.nr 87 := keeps 87 (by decide)
  have stackBase : a.nr 80 = s.nr 80 := keeps 80 (by decide)
  have previousOwner : a.nr 26 = s.nr 26 := keeps 26 (by decide)
  have aNat : a.nm = s.nm := sameNat
  cases newOwner
  · obtain ⟨t, write, ready, more, written, real, realRegs, _⟩ := pushMatchingCycleMember_spec a rfl readLive aOne
    have combined : BlockRuns (pushMatchingMemberFromCycle false) (10 + 9) s _ := readRun.append write
    refine ⟨_, 19, by decide, combined, ready, more.trans (congrArg (· + 1) count), ?_,
      real.trans sameReal, realRegs.trans sameRR, ?_⟩
    · change t.nm = _
      rw [written]
      simp [pushedMatchingCycleMember, matchingMemberStackWrite, matchingCycleStackAddress, aNat, count,
        stackBase, rep, node, previousOwner, owner]
    · intro r safe
      rw [← combined.run]
      exact arithmeticRun_keeps_from_destination_list [0, 6, 15, 16, 17, 25, 26, 87] (by decide) safe s 19
  · let b := {a with pc := 1, nr := Function.update a.nr 26 (a.nr 15)}
    have readZero : read.nr 23 = 0 := aZero
    have save : BlockRuns preserveTopCycleChild 1 a b := by
      apply BlockRuns.of_running_exit
      · simp [b, preserveTopCycleChild, arithmeticStep, a, readLive, readZero]
      · exact readLive
      · rfl
    let c := {b with pc := 0}
    have cOne : c.nr 9 = 1 := by simpa [c, b] using aOne
    obtain ⟨t, write, ready, more, written, real, realRegs, _⟩ := pushMatchingCycleMember_spec c rfl readLive cOne
    have combined : BlockRuns (pushMatchingMemberFromCycle true) (10 + (1 + 9)) s _ := readRun.append (save.append write)
    have cCount : c.nr 87 = s.nr 87 := by simpa [c, b] using count
    have cBase : c.nr 80 = s.nr 80 := by simpa [c, b] using stackBase
    have cRep : c.nr 15 = record.representative := by simpa [c, b] using rep
    have cNode : c.nr 25 = record.node := by simpa [c, b] using node
    have cOwner : c.nr 26 = record.representative := by simpa [c, b] using rep
    have cNat : c.nm = s.nm := sameNat
    refine ⟨_, 20, le_rfl, combined, ready, more.trans (congrArg (· + 1) cCount), ?_,
      real.trans sameReal, realRegs.trans sameRR, ?_⟩
    · change t.nm = _
      rw [written]
      simp [pushedMatchingCycleMember, matchingMemberStackWrite, matchingCycleStackAddress, cNat, cCount,
        cBase, cRep, cNode, cOwner, owner]
    · intro r safe
      rw [← combined.run]
      exact arithmeticRun_keeps_from_destination_list [0, 6, 15, 16, 17, 25, 26, 87] (by decide) safe s 20

theorem pushMatchingMemberFromCycle_keeps_inherited {s t : ArithmeticState} {steps : ℕ}
    (run : BlockRuns (pushMatchingMemberFromCycle false) steps s t) : t.nr 26 = s.nr 26 := by
  rw [← run.run]
  exact arithmeticRun_keeps_from_destination_list [0, 6, 15, 16, 17, 25, 87] (by decide) (by decide) s steps

def matchingMemberChildPushCount (s : ArithmeticState) (i : ℕ) : ℕ := s.nr 80 + 3 * (s.nr 87 + i)

/-- The stack initially contains an untouched prefix. The child scan appends the
cycle records in increasing physical order, leaving later pushes to use LIFO order. -/
structure MatchingMemberChildPush (s : ArithmeticState) (newOwner : Bool) (jobs : List MatchingMemberJob)
    (i : ℕ) (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  running : m.halted = false
  index : m.nr 7 = i
  count : m.nr 87 = s.nr 87 + i
  registers : ∀ r, r ∉ [0, 6, 7, 15, 16, 17, 25, 26, 87] → m.nr r = s.nr r
  inherited : newOwner = false → m.nr 26 = s.nr 26
  stack : ∀ j (hj : j < i) (inside : j < jobs.length),
    matchingMemberStackWords m.nm (matchingMemberChildPushCount s j) = matchingMemberJobWords jobs[j]
  natural : ∀ a, (a < matchingMemberChildPushCount s 0 ∨ matchingMemberChildPushCount s i ≤ a) → m.nm a = s.nm a
  real : m.rm = s.rm
  realRegisters : m.rr = s.rr

theorem pushMatchingMemberChildren_spec (newOwner : Bool) (s : ArithmeticState) (jobs : List MatchingMemberJob)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0)
    (count : s.nr 19 = jobs.length) (space : matchingMemberChildPushCount s jobs.length ≤ s.nr 18)
    (read : ∀ i (hi : i < jobs.length),
      let record := matchingCycleChildAt s.nm (s.nr 18 + 4 * i)
      let job := jobs[i]
      (record.representative, record.node) = (job.representative, job.node) ∧
      job.owner = (if newOwner then job.representative else s.nr 26)) :
    ∃ t steps, steps ≤ 23 * jobs.length + 2 ∧
      BlockRuns (countedLoopFromZero 9 7 19 (pushMatchingMemberFromCycle newOwner)) steps s t ∧
      MatchingMemberChildPush s newOwner jobs jobs.length {t with pc := 0} := by
  have initial : MatchingMemberChildPush s newOwner jobs 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, by simp, ?_, by simp, ?_, fun _ _ => rfl, rfl, rfl⟩
    · intro r safe
      have other : r ≠ 7 := by simp at safe; omega
      exact Function.update_of_ne other _ _
    · intro j hj
      omega
  have step (i : ℕ) (hi : i < jobs.length) (m : ArithmeticState)
      (inv : MatchingMemberChildPush s newOwner jobs i m) :
      ∃ t steps, steps ≤ 20 ∧ BlockRuns (pushMatchingMemberFromCycle newOwner) steps m t ∧ t.halted = false ∧
        MatchingMemberChildPush s newOwner jobs (i+1)
          {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    have oneAt : m.nr 9 = 1 := (inv.registers 9 (by decide)).trans one
    have zeroAt : m.nr 23 = 0 := (inv.registers 23 (by decide)).trans zero
    obtain ⟨t, steps, budget, run, live, more, memory, real, realRegisters, kept⟩ :=
      pushMatchingMemberFromCycle_spec newOwner m inv.entry inv.running oneAt zeroAt
    have atCycle : m.nr 18 = s.nr 18 := inv.registers 18 (by decide)
    have recordEq : matchingCycleChildAt m.nm (m.nr 18 + 4 * m.nr 7) =
        matchingCycleChildAt s.nm (s.nr 18 + 4 * i) := by
      rw [atCycle, inv.index]
      have addresses (w : ℕ) : m.nm (s.nr 18 + 4 * i + w) = s.nm (s.nr 18 + 4 * i + w) := by
        apply inv.natural
        right
        unfold matchingMemberChildPushCount at space ⊢
        omega
      have first := addresses 0
      simp only [Nat.add_zero] at first
      simp only [matchingCycleChildAt, first, addresses 1, addresses 2, addresses 3]
    have whereAt : matchingCycleStackAddress m (m.nr 87) = matchingMemberChildPushCount s i := by
      rw [matchingCycleStackAddress, matchingMemberChildPushCount, inv.registers 80 (by decide), inv.count]
    have ownerAt : (if newOwner then jobs[i].representative else m.nr 26) = jobs[i].owner := by
      cases h : newOwner
      · simpa [h, inv.inherited h] using (read i hi).2.symm
      · simpa [h] using (read i hi).2.symm
    have effect : t.nm = matchingMemberStackWrite m.nm (matchingMemberChildPushCount s i)
        (matchingMemberJobWords jobs[i]) := by
      rw [memory, recordEq, whereAt]
      have rp : (matchingCycleChildAt s.nm (s.nr 18 + 4 * i)).representative = jobs[i].representative :=
        congrArg Prod.fst (read i hi).1
      have nd : (matchingCycleChildAt s.nm (s.nr 18 + 4 * i)).node = jobs[i].node := congrArg Prod.snd (read i hi).1
      rw [rp, nd, ownerAt]
      rfl
    refine ⟨t, steps, budget, run, live, rfl, live, ?_, ?_, ?_, ?_, ?_, ?_,
      real.trans inv.real, realRegisters.trans inv.realRegisters⟩
    · simp [kept 7 (by decide), kept 9 (by decide), inv.index, oneAt]
    · change t.nr 87 = _
      rw [more, inv.count]
      omega
    · intro r safe
      have different : r ≠ 7 := by simp at safe; omega
      have outside : r ∉ [0, 6, 15, 16, 17, 25, 26, 87] := by simp at safe ⊢; omega
      exact (Function.update_of_ne different _ _).trans ((kept r outside).trans (inv.registers r safe))
    · intro inherited
      subst newOwner
      change t.nr 26 = s.nr 26
      exact (pushMatchingMemberFromCycle_keeps_inherited run).trans (inv.inherited rfl)
    · intro j hj inJobs
      change matchingMemberStackWords t.nm (matchingMemberChildPushCount s j) = _
      rw [effect]
      obtain before | equal := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)
      · have same (w : ℕ) (hw : w < 3) : matchingMemberStackWrite m.nm (matchingMemberChildPushCount s i)
            (matchingMemberJobWords jobs[i]) (matchingMemberChildPushCount s j + w) =
            m.nm (matchingMemberChildPushCount s j + w) := by
          apply matchingMemberStackWrite_unchanged
          left
          unfold matchingMemberChildPushCount
          omega
        have first := same 0 (by decide)
        simp only [Nat.add_zero] at first
        simpa only [matchingMemberStackWords, first, same 1 (by decide), same 2 (by decide)] using inv.stack j before inJobs
      · subst j
        exact matchingMemberStackWrite_words _ _ _
    · intro a far
      change t.nm a = s.nm a
      have previous : a < matchingMemberChildPushCount s 0 ∨ matchingMemberChildPushCount s i ≤ a := by
        unfold matchingMemberChildPushCount at far ⊢
        omega
      have skips : a < matchingMemberChildPushCount s i ∨ matchingMemberChildPushCount s i + 3 ≤ a := by
        unfold matchingMemberChildPushCount at far ⊢
        omega
      exact (congrFun effect a).trans ((matchingMemberStackWrite_unchanged _ _ _ a skips).trans (inv.natural a previous))
  obtain ⟨t, steps, completed, budget, run⟩ := countedLoopFromZero_bounded 9 7 19 jobs.length 20
    (pushMatchingMemberFromCycle newOwner) (MatchingMemberChildPush s newOwner jobs) (s := s)
    entry running initial (fun _ _ inv => ⟨inv.entry, inv.running, inv.index,
      (inv.registers 19 (by decide)).trans count⟩) step
  exact ⟨_, steps, by omega, run, rfl, completed.running, completed.index, completed.count,
    completed.registers, completed.inherited, completed.stack, completed.natural, completed.real, completed.realRegisters⟩

/-- The leaf branch pops one record, writes the recorded owner, and leaves the
remaining stack words unchanged. -/
theorem visitCycleMemberLeaf_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0) (v owner : ℕ)
    (top : matchingMemberStackWords s.nm (matchingCycleStackAddress s (s.nr 87 - 1)) = (v, 0, owner)) :
    ∃ t, BlockRuns visitCycleMemberNode 13 s t ∧ t.halted = false ∧ t.nr 87 = s.nr 87 - 1 ∧
      t.nm = Function.update s.nm (s.nr 79 + v) owner ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 15, 22, 26, 87] → t.nr r = s.nr r := by
  obtain ⟨p, pop, pLive, pCount, rep, node, tag, pNat, pReal, pRR, pKeeps⟩ :=
    popMatchingCycleMember_spec s entry running one
  let a := {p with pc := 0}
  have vertex : a.nr 15 = v := rep.trans (congrArg Prod.fst top)
  have identifier : a.nr 22 = 0 := node.trans (congrArg (fun w : ℕ × ℕ × ℕ => w.2.1) top)
  have ownerAt : a.nr 26 = owner := tag.trans (congrArg (fun w : ℕ × ℕ × ℕ => w.2.2) top)
  have zeroAt : a.nr 23 = 0 := (pKeeps 23 (by decide)).trans zero
  have mapAt : a.nr 79 = s.nr 79 := pKeeps 79 (by decide)
  obtain ⟨t, write, tLive, natural, real, rr, kept⟩ := writeCycleMemberLeaf_spec a rfl pLive
  have branch := branchOnAtMost_left 22 23 writeCycleMemberLeaf
    (appendBlock readMatchingCycleHeader (countedLoopFromZero 9 7 19 pushNestedCycleChild)) (s := a) rfl pLive
    (by simp [identifier, zeroAt]) write tLive
  have run : BlockRuns visitCycleMemberNode 13 s _ := pop.append branch
  refine ⟨_, run, tLive, (kept 87 (by decide)).trans pCount, ?_, real.trans pReal, rr.trans pRR, ?_⟩
  · change t.nm = _
    rw [natural, mapAt, vertex, ownerAt]
    change Function.update p.nm _ _ = _
    rw [pNat]
  · intro r safe
    exact (kept r (by simp at safe ⊢; omega)).trans (pKeeps r safe)

/-- The nontrivial branch pops one node and pushes exactly its ordered children.
Only the appended stack area is written. -/
theorem visitCycleMemberBlossom_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0)
    (representative node owner : ℕ) (positive : 0 < node) (jobs : List MatchingMemberJob)
    (top : matchingMemberStackWords s.nm (matchingCycleStackAddress s (s.nr 87 - 1)) = (representative, node, owner))
    (headerCount : s.nm (s.nr 78 + node) = jobs.length)
    (space : s.nr 80 + 3 * (s.nr 87 - 1 + jobs.length) ≤ s.nm (s.nr 77 + node))
    (read : ∀ i (hi : i < jobs.length),
      let cell := matchingCycleChildAt s.nm (s.nm (s.nr 77 + node) + 4 * i)
      (cell.representative, cell.node) = (jobs[i].representative, jobs[i].node) ∧ jobs[i].owner = owner) :
    ∃ t steps, steps ≤ 23 * jobs.length + 16 ∧ BlockRuns visitCycleMemberNode steps s t ∧ t.halted = false ∧
      t.nr 87 = s.nr 87 - 1 + jobs.length ∧
      (∀ i (hi : i < jobs.length), matchingMemberStackWords t.nm (s.nr 80 + 3 * (s.nr 87 - 1 + i)) =
        matchingMemberJobWords jobs[i]) ∧
      (∀ a, a < s.nr 80 + 3 * (s.nr 87 - 1) ∨ s.nr 80 + 3 * (s.nr 87 - 1 + jobs.length) ≤ a → t.nm a = s.nm a) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 7, 15, 16, 17, 18, 19, 22, 25, 26, 87] → t.nr r = s.nr r := by
  obtain ⟨p, pop, pLive, pCount, _, pNode, tag, pNat, pReal, pRR, pKeeps⟩ :=
    popMatchingCycleMember_spec s entry running one
  let a := {p with pc := 0}
  have nodeAt : a.nr 22 = node := pNode.trans (congrArg (fun w : ℕ × ℕ × ℕ => w.2.1) top)
  have ownerAt : a.nr 26 = owner := tag.trans (congrArg (fun w : ℕ × ℕ × ℕ => w.2.2) top)
  have zeroAt : a.nr 23 = 0 := (pKeeps 23 (by decide)).trans zero
  have countAt : a.nr 87 = s.nr 87 - 1 := pCount
  have natAt : a.nm = s.nm := pNat
  have ahead : a.nr 23 < a.nr 22 := by rwa [zeroAt, nodeAt]
  obtain ⟨h, header, hLive, oldStart, oldCount, hNat, hReal, hRR, hKeeps⟩ :=
    readMatchingCycleHeader_spec a rfl pLive
  let b := {h with pc := 0}
  have bNat : b.nm = s.nm := hNat.trans natAt
  have bOne : b.nr 9 = 1 := (hKeeps 9 (by decide)).trans ((pKeeps 9 (by decide)).trans one)
  have bZero : b.nr 23 = 0 := (hKeeps 23 (by decide)).trans zeroAt
  have bCount : b.nr 87 = s.nr 87 - 1 := (hKeeps 87 (by decide)).trans countAt
  have bStack : b.nr 80 = s.nr 80 := (hKeeps 80 (by decide)).trans (pKeeps 80 (by decide))
  have bOwner : b.nr 26 = owner := (hKeeps 26 (by decide)).trans ownerAt
  have bStart : b.nr 18 = s.nm (s.nr 77 + node) := by
    change h.nr 18 = _
    rw [oldStart, natAt, nodeAt, show a.nr 77 = s.nr 77 from pKeeps 77 (by decide)]
  have bLength : b.nr 19 = jobs.length := by
    change h.nr 19 = _
    rw [oldCount, natAt, nodeAt, show a.nr 78 = s.nr 78 from pKeeps 78 (by decide), headerCount]
  have room : matchingMemberChildPushCount b jobs.length ≤ b.nr 18 := by
    simpa [matchingMemberChildPushCount, bStack, bCount, bStart] using space
  have rows (i : ℕ) (hi : i < jobs.length) :
      let cell := matchingCycleChildAt b.nm (b.nr 18 + 4 * i)
      (cell.representative, cell.node) = (jobs[i].representative, jobs[i].node) ∧
        jobs[i].owner = (if false then jobs[i].representative else b.nr 26) := by
    simpa [bNat, bStart, bOwner] using read i hi
  obtain ⟨t, ticks, budget, push, result⟩ :=
    pushMatchingMemberChildren_spec false b jobs rfl hLive bOne bZero bLength room rows
  have branch := branchOnAtMost_right 22 23 writeCycleMemberLeaf _ (s := a) rfl pLive ahead (header.append push) result.running
  have run : BlockRuns visitCycleMemberNode (9 + (1 + (4 + ticks))) s _ := pop.append branch
  refine ⟨_, _, by omega, run, result.running, ?_, ?_, ?_, result.real.trans (hReal.trans pReal),
    result.realRegisters.trans (hRR.trans pRR), ?_⟩
  · have out : t.nr 87 = b.nr 87 + jobs.length := result.count
    change t.nr 87 = _
    exact out.trans (congrArg (· + jobs.length) bCount)
  · intro i hi
    change matchingMemberStackWords t.nm _ = _
    simpa [matchingMemberChildPushCount, bStack, bCount] using result.stack i hi hi
  · intro address untouched
    have safe : address < matchingMemberChildPushCount b 0 ∨ matchingMemberChildPushCount b jobs.length ≤ address := by
      simpa [matchingMemberChildPushCount, bStack, bCount] using untouched
    change t.nm address = _
    exact (result.natural address safe).trans (congrFun bNat address)
  · intro r safe
    exact (result.registers r (by simp at safe ⊢; omega)).trans
      ((hKeeps r (by simp at safe ⊢; omega)).trans (pKeeps r (by simp at safe ⊢; omega)))

end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberVisitRAM

/-! matching/MatchingMemberWalkRAM.lean -/
section RppSource_MatchingMemberWalkRAM
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096



def matchingMemberJobValid (s : ArithmeticState) (job : MatchingMemberJob) : Prop :=
  job.proper ∧ job.tree.encoded s.nm (s.nr 77) (s.nr 78) ∧
    job.tree.readable s.nm (s.nr 77) (s.nr 78) (outsideMatchingMemberScratch s) ∧
    job.tree.recordsAbove s.nm (s.nr 77) (s.nr 80 + 3 * s.nr 55)

/-- Logical and physical correspondence of a traversal prefix. The encoded stack
is in increasing address order, with the next task at its highest address. -/
structure MatchingMemberWalk (s : ArithmeticState) (assignments done : List (ℕ × ℕ))
    (jobs : List MatchingMemberJob) (i : ℕ) (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  running : m.halted = false
  registers : ∀ r ∈ [9, 55, 77, 78, 79, 80], m.nr r = s.nr r
  zero : m.nr 23 = 0
  index : m.nr 24 = i
  watch : m.nr 28 = 2 * s.nr 55
  count : m.nr 87 = jobs.length
  pending : jobs ≠ [] → i + MatchingMemberJob.work jobs ≤ 2 * s.nr 55
  tasks : ∀ job ∈ jobs, matchingMemberJobValid s job
  remaining : (done ++ MatchingMemberJob.frontier jobs).Perm assignments
  slots : ∀ j (inStack : j < jobs.length),
    matchingMemberStackWords m.nm (s.nr 80 + 3 * j) = matchingMemberJobWords jobs[j]
  placed : ∀ x ∈ done, m.nm (s.nr 79 + x.1) = x.2
  stillEmpty : ∀ v < s.nr 55, v ∉ done.map Prod.fst → m.nm (s.nr 79 + v) = s.nr 55
  natural : ∀ a, outsideMatchingMemberScratch s a → m.nm a = s.nm a



def matchingMemberWalkCredit (s : ArithmeticState) (m : ArithmeticState) : ℕ :=
  23 * (2 * s.nr 55 - m.nr 24 - m.nr 87)

private theorem visitMatchingMember_preservesLoopRegisters {s m t : ArithmeticState}
    (one : s.nr 9 = 1) {i : ℕ}
    (atIndex : m.nr 24 = i)
    (registers : ∀ r ∈ [9, 55, 77, 78, 79, 80], m.nr r = s.nr r)
    (keeps : ∀ r ∈ [9, 23, 24, 28, 55, 77, 78, 79, 80], t.nr r = m.nr r) :
    let next := {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)}
    next.nr 24 = i + 1 ∧
      (∀ r ∈ [9, 55, 77, 78, 79, 80], next.nr r = s.nr r) ∧
      next.nr 23 = m.nr 23 ∧ next.nr 28 = m.nr 28 := by
  intro next
  have atOne := (keeps 9 (by decide)).trans ((registers 9 (by decide)).trans one)
  refine ⟨by simp [next, atOne, keeps 24 (by decide), atIndex], ?_, ?_, ?_⟩
  · intro r known
    have safe : r ≠ 24 := by simp at known; omega
    have listed : r ∈ [9, 23, 24, 28, 55, 77, 78, 79, 80] := by simp at known ⊢; omega
    exact (Function.update_of_ne safe _ _).trans ((keeps r listed).trans (registers r known))
  · simpa [next] using keeps 23 (by decide)
  · simpa [next] using keeps 28 (by decide)

theorem matchingMemberJobRows {children : MatchingMemberTree} {owner : Option ℕ}
    {memory : ℕ → ℕ} {start : ℕ}
    (saved : ∀ i (hi : i < children.rootKeys.length),
      let cell := matchingCycleChildAt memory (start + 4 * i)
      MatchingMemberTree.rootKey cell.representative cell.node = children.rootKeys[i]) :
    ∀ i (hi : i < (children.jobs owner).length),
      let cell := matchingCycleChildAt memory (start + 4 * i)
      let job := (children.jobs owner)[i]
      (cell.representative, cell.node) = (job.representative, job.node) ∧
        job.owner = owner.getD job.representative := by
  intro i hi
  have hiKeys : i < children.rootKeys.length := by simpa [children.jobs_length owner] using hi
  have keys := congrArg (fun rows : List (ℕ × ℕ) => rows[i]?) (children.jobs_rootKeys owner)
  have typed : MatchingMemberTree.rootKey (children.jobs owner)[i].representative (children.jobs owner)[i].node =
      children.rootKeys[i] := by
    simpa only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hiKeys, Option.map_some,
      Option.some.injEq] using keys
  exact ⟨(saved i hiKeys).trans typed.symm, children.jobs_owner owner _ (List.getElem_mem hi)⟩

private theorem matchingMember_popLeaf {s m : ArithmeticState} {assignments done : List (ℕ × ℕ)}
    {jobs : List MatchingMemberJob} {i : ℕ} {job : MatchingMemberJob}
    (inv : MatchingMemberWalk s assignments done (jobs ++ [job]) i m)
    (one : s.nr 9 = 1) (unique : (assignments.map Prod.fst).Nodup)
    (validLeaves : ∀ p ∈ assignments, p.1 < s.nr 55)
    (separated : s.nr 79 + s.nr 55 ≤ s.nr 80) (singleton : job.children = none) :
    ∃ t, BlockRuns visitCycleMemberNode 13 m t ∧ t.halted = false ∧
      let next := {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)}
      MatchingMemberWalk s assignments ((job.representative, job.owner) :: done) jobs (i+1) next ∧
        matchingMemberWalkCredit s next = matchingMemberWalkCredit s m := by
  let pair := (job.representative, job.owner)
  have appears : job ∈ jobs ++ [job] := by simp
  have isLeaf : job.node = 0 := by simpa [MatchingMemberJob.proper, singleton] using (inv.tasks job appears).1
  have oneAt : m.nr 9 = 1 := (inv.registers 9 (by decide)).trans one
  have count : m.nr 87 = jobs.length + 1 := by simpa using inv.count
  have here : jobs.length < (jobs ++ [job]).length := by simp
  have atTop := inv.slots jobs.length here
  have lastJob : (jobs ++ [job])[jobs.length] = job := by simp
  rw [lastJob] at atTop
  have top : matchingMemberStackWords m.nm (matchingCycleStackAddress m (m.nr 87 - 1)) =
      (job.representative, 0, job.owner) := by
    simpa [matchingCycleStackAddress, inv.registers 80 (by decide), count, matchingMemberJobWords, isLeaf] using atTop
  obtain ⟨t, run, live, popCount, memory, _, _, kept⟩ :=
    visitCycleMemberLeaf_spec m inv.entry inv.running oneAt inv.zero job.representative job.owner top
  have same : ((pair :: done) ++ MatchingMemberJob.frontier jobs).Perm assignments := by
    have reorder : ([pair] ++ (done ++ MatchingMemberJob.frontier jobs)).Perm
        ((done ++ MatchingMemberJob.frontier jobs) ++ [pair]) := List.perm_append_comm
    have oldOrder : (done ++ (MatchingMemberJob.frontier jobs ++ [pair])).Perm assignments := by
      simpa [MatchingMemberJob.frontier_append, MatchingMemberJob.frontier, MatchingMemberJob.assignments,
        singleton, pair, List.append_assoc] using inv.remaining
    exact reorder.trans (by simpa [List.append_assoc] using oldOrder)
  have inLeaves : pair ∈ assignments := same.mem_iff.mp (by simp)
  have leafBound : job.representative < s.nr 55 := validLeaves pair inLeaves
  have noRepeat : job.representative ∉ done.map Prod.fst := by
    have nd := (same.map Prod.fst).nodup_iff.mpr unique
    simp only [List.cons_append, List.map_cons, List.nodup_cons, pair] at nd
    intro h
    apply nd.1
    rw [List.map_append]
    exact List.mem_append_left _ h
  have locality : t.nm = Function.update m.nm (s.nr 79 + job.representative) job.owner := by
    simpa [inv.registers 79 (by decide)] using memory
  have control := visitMatchingMember_preservesLoopRegisters one inv.index inv.registers
    (t := t) (fun r list => kept r (by simp at list ⊢; omega))
  have popped : t.nr 87 = jobs.length := by simpa [count] using popCount
  have remains : i + MatchingMemberJob.work (jobs ++ [job]) ≤ 2 * s.nr 55 := inv.pending (by simp)
  have decreases : MatchingMemberJob.work (jobs ++ [job]) = MatchingMemberJob.work jobs + 1 := by
    rw [MatchingMemberJob.work_append]
    simp [MatchingMemberJob.work, MatchingMemberJob.visits, singleton]
  refine ⟨t, run, live, ⟨rfl, live, control.2.1, control.2.2.1.trans inv.zero, control.1,
    control.2.2.2.trans inv.watch, popped, ?_, ?_, same, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro _
    omega
  · intro nested present
    exact inv.tasks nested (List.mem_append_left _ present)
  · intro j hj
    change matchingMemberStackWords t.nm (s.nr 80 + 3 * j) = _
    have idx : j < (jobs ++ [job]).length := by simp; omega
    have earlier : (jobs ++ [job])[j] = jobs[j] := List.getElem_append_left hj
    have untouched (w : ℕ) : s.nr 80 + 3 * j + w ≠ s.nr 79 + job.representative := by omega
    have first : s.nr 80 + 3 * j ≠ s.nr 79 + job.representative := by omega
    simpa [matchingMemberStackWords, locality, Function.update_of_ne first, Function.update_of_ne (untouched 1),
      Function.update_of_ne (untouched 2), earlier] using inv.slots j idx
  · intro other did
    change t.nm (s.nr 79 + other.1) = other.2
    simp only [List.mem_cons] at did
    rcases did with rfl | old
    · simp [locality, pair]
    · have different : other.1 ≠ job.representative := fun equal =>
        noRepeat (equal ▸ List.mem_map_of_mem (f := Prod.fst) old)
      rw [locality, Function.update_of_ne (by omega : s.nr 79 + other.1 ≠ s.nr 79 + job.representative)]
      exact inv.placed other old
  · intro v bound missing
    change t.nm (s.nr 79 + v) = _
    have old : v ∉ done.map Prod.fst := fun h => missing (by simp [h])
    have different : v ≠ job.representative := fun eq => missing (by simp [eq])
    rw [locality, Function.update_of_ne (by omega : s.nr 79 + v ≠ s.nr 79 + job.representative)]
    exact inv.stillEmpty v bound old
  · intro a safe
    change t.nm a = s.nm a
    have away : a ≠ s.nr 79 + job.representative := by rcases safe.1 with low | high <;> omega
    rw [locality, Function.update_of_ne away]
    exact inv.natural a safe
  · unfold matchingMemberWalkCredit
    have freshIndex := control.1
    have freshCount : ({t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)} : ArithmeticState).nr 87 =
        jobs.length := popped
    rw [freshIndex, freshCount, inv.index, count]
    omega

private theorem matchingMember_expandJob {s m : ArithmeticState} {assignments done : List (ℕ × ℕ)}
    {jobs : List MatchingMemberJob} {i : ℕ} {job : MatchingMemberJob} {children : MatchingMemberTree}
    (inv : MatchingMemberWalk s assignments done (jobs ++ [job]) i m) (one : s.nr 9 = 1)
    (assigned : assignments.length ≤ s.nr 55) (validLeaves : ∀ p ∈ assignments, p.1 < s.nr 55)
    (separated : s.nr 79 + s.nr 55 ≤ s.nr 80)
    (nested : job.children = some children) :
    let pushed := children.jobs (some job.owner)
    ∃ t steps, steps ≤ 23 * pushed.length + 16 ∧ BlockRuns visitCycleMemberNode steps m t ∧
      t.halted = false ∧
      let next := {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)}
      MatchingMemberWalk s assignments done (jobs ++ pushed) (i+1) next ∧
        matchingMemberWalkCredit s next + 23 * pushed.length = matchingMemberWalkCredit s m := by
  intro pushed
  have present : job ∈ jobs ++ [job] := by simp
  obtain ⟨proper, oldEncoding, readable, above⟩ := inv.tasks job present
  rw [MatchingMemberJob.proper, nested] at proper
  obtain ⟨positive, _, validChildren⟩ := proper
  have localEncoding := MatchingMemberTree.encoded_congr oldEncoding readable inv.natural
  rw [MatchingMemberJob.tree, nested] at localEncoding oldEncoding readable above
  obtain ⟨headerCount, storedChildren, _, _⟩ := localEncoding
  obtain ⟨headerSafe, _, _, childReadable, _⟩ := readable
  have higher : s.nr 80 + 3 * s.nr 55 ≤ m.nm (s.nr 77 + job.node) := by
    rw [inv.natural _ headerSafe]
    exact above.1
  have same : (done ++ MatchingMemberJob.frontier (jobs ++ pushed)).Perm assignments := by
    rw [show MatchingMemberJob.frontier (jobs ++ pushed) = MatchingMemberJob.frontier (jobs ++ [job]) from
      MatchingMemberJob.appendChildren_frontier jobs job children nested]
    exact inv.remaining
  have correct (j : MatchingMemberJob) (found : j ∈ jobs ++ pushed) : matchingMemberJobValid s j := by
    rcases List.mem_append.mp found with prior | new
    · exact inv.tasks j (List.mem_append_left _ prior)
    · exact ⟨children.jobs_proper (some job.owner) validChildren j new,
        children.jobs_encoded (some job.owner) s.nm (s.nr 77) (s.nr 78) (s.nr 80 + 3 * s.nr 55)
          (outsideMatchingMemberScratch s) oldEncoding.2.2.1 childReadable above.2.1 j new⟩
  have capacity : jobs.length + pushed.length ≤ s.nr 55 := by
    simpa only [List.length_append] using (MatchingMemberJob.length_le_frontier (jobs ++ pushed)
      (fun j there => (correct j there).1)).trans ((MatchingMemberJob.frontier_length_le same).trans assigned)
  have count : m.nr 87 = jobs.length + 1 := by simpa using inv.count
  have atTop := inv.slots jobs.length (by simp)
  have lastJob : (jobs ++ [job])[jobs.length] = job := by simp
  rw [lastJob] at atTop
  have top : matchingMemberStackWords m.nm (matchingCycleStackAddress m (m.nr 87 - 1)) =
      (job.representative, job.node, job.owner) := by
    simpa [matchingCycleStackAddress, inv.registers 80 (by decide), count, matchingMemberJobWords] using atTop
  have room : m.nr 80 + 3 * (m.nr 87 - 1 + pushed.length) ≤ m.nm (m.nr 77 + job.node) := by
    rw [inv.registers 77 (by decide), inv.registers 80 (by decide), count]
    omega
  have size : m.nm (m.nr 78 + job.node) = pushed.length := by
    rw [inv.registers 78 (by decide), headerCount]
    exact (children.jobs_length _).symm
  have rows (j : ℕ) (hj : j < pushed.length) :
      let cell := matchingCycleChildAt m.nm (m.nm (m.nr 77 + job.node) + 4 * j)
      (cell.representative, cell.node) = (pushed[j].representative, pushed[j].node) ∧ pushed[j].owner = job.owner := by
    have matchingRows := matchingMemberJobRows (owner := some job.owner) storedChildren j hj
    simpa [inv.registers 77 (by decide), pushed] using matchingRows
  obtain ⟨t, steps, cost, run, live, appended, written, effect, _, _, kept⟩ :=
    visitCycleMemberBlossom_spec m inv.entry inv.running ((inv.registers 9 (by decide)).trans one)
      inv.zero job.representative job.node job.owner positive pushed top size room rows
  have control := visitMatchingMember_preservesLoopRegisters one inv.index inv.registers
    (t := t) (fun r list => kept r (by simp at list ⊢; omega))
  have grew : t.nr 87 = jobs.length + pushed.length := by simpa only [count, Nat.add_sub_cancel] using appended
  have unchanged (a : ℕ) (there : a < s.nr 80 + 3 * jobs.length ∨ s.nr 80 + 3 * (jobs.length + pushed.length) ≤ a) :
      t.nm a = m.nm a := effect a (by simpa [count, inv.registers 80 (by decide)] using there)
  have potential := inv.pending (by simp)
  have visited := MatchingMemberJob.appendChildren_work jobs job children nested
  have still : (i + 1) + MatchingMemberJob.work (jobs ++ pushed) ≤ 2 * s.nr 55 := by
    change MatchingMemberJob.work (jobs ++ pushed) + 1 = _ at visited
    omega
  have workGe := MatchingMemberJob.length_le_work (jobs ++ pushed)
  have physicalBudget : (i + 1) + jobs.length + pushed.length ≤ 2 * s.nr 55 := by
    simp only [List.length_append] at workGe
    omega
  refine ⟨t, steps, cost, run, live, ⟨rfl, live, control.2.1, control.2.2.1.trans inv.zero, control.1,
    control.2.2.2.trans inv.watch, by simpa using grew, fun _ => still, correct, same, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j hj
    change matchingMemberStackWords t.nm (s.nr 80 + 3 * j) = _
    by_cases earlier : j < jobs.length
    · have old : j < (jobs ++ [job]).length := by simp; omega
      have readBefore := inv.slots j old
      rw [List.getElem_append_left earlier] at readBefore ⊢
      have safe (w : ℕ) (word : w < 3) : t.nm (s.nr 80 + 3 * j + w) = m.nm (s.nr 80 + 3 * j + w) :=
        unchanged _ (.inl (by omega))
      have first := safe 0 (by decide)
      simp only [Nat.add_zero] at first
      simpa only [matchingMemberStackWords, first, safe 1 (by decide), safe 2 (by decide)] using readBefore
    · have past : jobs.length ≤ j := Nat.le_of_not_gt earlier
      have index : j - jobs.length < pushed.length := by simp at hj; omega
      have loc : jobs.length + (j - jobs.length) = j := by omega
      rw [List.getElem_append_right past]
      simpa [inv.registers 80 (by decide), count, loc] using written (j - jobs.length) index
  · intro x hx
    change t.nm (s.nr 79 + x.1) = x.2
    have inAll : x ∈ assignments := same.mem_iff.mp (List.mem_append_left _ hx)
    have outside : s.nr 79 + x.1 < s.nr 80 + 3 * jobs.length := by
      have xBound := validLeaves x inAll
      omega
    exact (unchanged _ (.inl outside)).trans (inv.placed x hx)
  · intro v bound untouched
    change t.nm (s.nr 79 + v) = _
    exact (unchanged _ (.inl (by omega))).trans (inv.stillEmpty v bound untouched)
  · intro a safe
    change t.nm a = s.nm a
    exact (unchanged _ (by rcases safe.2 with before | after <;> omega)).trans (inv.natural a safe)
  · unfold matchingMemberWalkCredit
    have tIndex := control.1
    have tCount : ({t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)} : ArithmeticState).nr 87 =
        jobs.length + pushed.length := grew
    rw [tIndex, tCount, inv.index, count]
    omega

theorem matchingMemberWalk_loop {s start : ArithmeticState} {assignments : List (ℕ × ℕ)}
    (one : s.nr 9 = 1) (unique : (assignments.map Prod.fst).Nodup)
    (validLeaves : ∀ p ∈ assignments, p.1 < s.nr 55)
    (separated : s.nr 79 + s.nr 55 ≤ s.nr 80)
    (entry : start.pc = 0) (running : start.halted = false)
    {initial : List MatchingMemberJob}
    (initialState : MatchingMemberWalk s assignments [] initial 0
      {start with pc := 0, nr := Function.update start.nr 24 0}) :
    ∃ t steps, steps ≤ 42 * s.nr 55 + 23 * (2 * s.nr 55 - initial.length) + 2 ∧
      BlockRuns (countedLoopFromZero 9 24 28 (branchOnUnequal 87 23 visitCycleMemberNode)) steps start t ∧
      t.halted = false ∧ t.nr 87 = 0 ∧ t.nr 23 = 0 ∧
      (∀ p ∈ assignments, t.nm (s.nr 79 + p.1) = p.2) ∧
      (∀ v < s.nr 55, v ∉ assignments.map Prod.fst → t.nm (s.nr 79 + v) = s.nr 55) ∧
      ∀ a, outsideMatchingMemberScratch s a → t.nm a = s.nm a := by
  let inv (i : ℕ) (m : ArithmeticState) := ∃ done jobs, MatchingMemberWalk s assignments done jobs i m
  have assigned := MatchingMemberJob.boundedAssignments_length assignments (s.nr 55) unique validLeaves
  let body := branchOnUnequal 87 23 visitCycleMemberNode
  have step : ∀ i < 2 * s.nr 55, ∀ m, inv i m → ∃ t steps,
      let next := {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)}
      BlockRuns body steps m t ∧ t.halted = false ∧ inv (i + 1) next ∧
        steps + matchingMemberWalkCredit s next ≤ 18 + matchingMemberWalkCredit s m := by
    intro i hi m hm
    obtain ⟨done, jobs, walk⟩ := hm
    cases reverse : jobs.reverse with
    | nil =>
      have empty : jobs = [] := List.reverse_eq_nil_iff.mp reverse
      subst jobs
      have count : m.nr 87 = 0 := walk.count
      have skip := branchOnUnequal_skip 87 23 visitCycleMemberNode m walk.entry walk.running (count.trans walk.zero.symm)
      let t := {m with pc := body.length}
      have run : BlockRuns body 2 m t := skip
      have keeps (r : ℕ) (_ : r ∈ [9, 23, 24, 28, 55, 77, 78, 79, 80]) : t.nr r = m.nr r := rfl
      have ctl := visitMatchingMember_preservesLoopRegisters one walk.index walk.registers keeps
      refine ⟨t, 2, run, walk.running, ⟨done, [], rfl, walk.running, ctl.2.1, ctl.2.2.1.trans walk.zero,
        ctl.1, ctl.2.2.2.trans walk.watch, count, by simp, by simp, walk.remaining, by simp, walk.placed,
        walk.stillEmpty, walk.natural⟩, ?_⟩
      change 2 + 23 * (2 * s.nr 55 - (m.nr 24 + m.nr 9) - m.nr 87) ≤
        18 + 23 * (2 * s.nr 55 - m.nr 24 - m.nr 87)
      rw [walk.index, count, (walk.registers 9 (by decide)).trans one]
      omega
    | cons job earlierReversed =>
      have decomposed : jobs = earlierReversed.reverse ++ [job] := by
        have unfoldReverse := congrArg List.reverse reverse
        simpa only [List.reverse_reverse, List.reverse_cons] using unfoldReverse
      subst jobs
      have unequal : m.nr 87 ≠ m.nr 23 := by simp [walk.count, walk.zero]
      cases subtree : job.children with
      | none =>
        obtain ⟨t, run, live, after, cost⟩ := matchingMember_popLeaf walk one unique validLeaves separated subtree
        have visited := branchOnUnequal_take 87 23 visitCycleMemberNode walk.entry walk.running unequal run
        refine ⟨_, 2 + 13, visited, live, ⟨_, _, after⟩, ?_⟩
        change 2 + 13 + matchingMemberWalkCredit s {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)} ≤
          18 + matchingMemberWalkCredit s m
        rw [cost]
        omega
      | some children =>
        obtain ⟨t, ticks, bound, run, live, after, cost⟩ :=
          matchingMember_expandJob walk one assigned validLeaves separated subtree
        have visited := branchOnUnequal_take 87 23 visitCycleMemberNode walk.entry walk.running unequal run
        refine ⟨_, 2 + ticks, visited, live, ⟨_, _, after⟩, ?_⟩
        change 2 + ticks + matchingMemberWalkCredit s {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)} ≤
          18 + matchingMemberWalkCredit s m
        omega
  obtain ⟨last, steps, stopped, bound, run⟩ := countedLoopFromZero_amortized 9 24 28 (2 * s.nr 55) 18 body
    inv (matchingMemberWalkCredit s) (s := start) entry running ⟨[], initial, initialState⟩
    (fun _ _ ⟨_, _, w⟩ => ⟨w.entry, w.running, w.index, w.watch⟩) step
  obtain ⟨done, pending, final⟩ := stopped
  have empty : pending = [] := by
    by_contra present
    have total := final.pending present
    have nonzero : 0 < pending.length := by
      by_contra h
      exact present (List.eq_nil_of_length_eq_zero (by omega))
    have work := MatchingMemberJob.length_le_work pending
    omega
  subst pending
  have placed : done.Perm assignments := by simpa [MatchingMemberJob.frontier] using final.remaining
  have seededCredit : matchingMemberWalkCredit s {start with pc := 0, nr := Function.update start.nr 24 0} =
      23 * (2 * s.nr 55 - initial.length) := by
    unfold matchingMemberWalkCredit
    rw [initialState.index, initialState.count]
    omega
  refine ⟨_, steps, ?_, run, final.running, final.count, final.zero, ?_, ?_, final.natural⟩
  · rw [seededCredit] at bound
    omega
  · intro p present
    exact final.placed p (placed.mem_iff.mpr present)
  · intro v below missing
    exact final.stillEmpty v below (fun seen => missing ((placed.map Prod.fst).mem_iff.mp seen))

end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberWalkRAM

/-! matching/MatchingMemberMapRAM.lean -/
section RppSource_MatchingMemberMapRAM
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096





/-- The actual DFS produces the immediate-child representative for every leaf,
leaves the sentinel on other originals, and confines natural writes to its map
and traversal stack. Work is linear in the compact original-vertex dimension. -/
theorem mapMatchingCycleNodeMembers_spec (s : ArithmeticState) (children : MatchingMemberTree)
    (root : MatchingMemberRoot s children) (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t steps, steps ≤ 93 * s.nr 55 + 13 ∧ BlockRuns mapMatchingCycleNodeMembers steps s t ∧
      t.halted = false ∧ t.nr 87 = 0 ∧ t.nr 23 = 0 ∧
      (∀ p ∈ matchingMemberAssignments children, t.nm (s.nr 79 + p.1) = p.2) ∧
      (∀ v < s.nr 55, v ∉ children.leaves → t.nm (s.nr 79 + v) = s.nr 55) ∧
      (∀ a, outsideMatchingMemberScratch s a → t.nm a = s.nm a) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 7, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 28, 87] → t.nr r = s.nr r := by
  let seedCode : List ArithmeticInstruction := [.natConst 23 0, .natConst 87 0, .natAdd 28 55 55]
  let seeded := { s with
    pc := 3
    nr := Function.update (Function.update (Function.update s.nr 23 0) 87 0) 28 (2 * s.nr 55) }
  have seed : BlockRuns seedCode 3 s seeded := by
    apply BlockRuns.of_running_exit
    · have twice : s.nr 55 + s.nr 55 = 2 * s.nr 55 := by omega
      simp [seedCode, seeded, entry, running, arithmeticStep, twice, Function.iterate_succ_apply']
    · exact running
    · rfl
  have frameSeed (r : ℕ) (safe : r ∉ [23, 28, 87]) : seeded.nr r = s.nr r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at safe
    obtain ⟨a, b, c⟩ := safe
    simp [seeded, Function.update_of_ne a, Function.update_of_ne b, Function.update_of_ne c]
  let a := {seeded with pc := 0}
  have aOne : a.nr 9 = 1 := (frameSeed 9 (by decide)).trans one
  have aSize : a.nr 55 = s.nr 55 := frameSeed 55 (by decide)
  have aMap : a.nr 79 = s.nr 79 := frameSeed 79 (by decide)
  have aNat : a.nm = s.nm := rfl
  obtain ⟨cleared, clearTicks, clearCost, clear, clearLive, clearedMap, _, _, clearFrame⟩ :=
    clearCycleMemberMap_spec a rfl running aOne
  let b := {cleared with pc := 0}
  have clearedOutside (x : ℕ) (safe : x < s.nr 79 ∨ s.nr 79 + s.nr 55 ≤ x) : b.nm x = s.nm x := by
    have away : ¬(s.nr 79 ≤ x ∧ x < s.nr 79 + s.nr 55) := by omega
    exact (clearedMap x).trans (by simp [aMap, aSize, away, aNat])
  have clearedLeaves (v : ℕ) (inside : v < s.nr 55) : b.nm (s.nr 79 + v) = s.nr 55 := by
    have used : s.nr 79 ≤ s.nr 79 + v ∧ s.nr 79 + v < s.nr 79 + s.nr 55 := by omega
    exact (clearedMap (s.nr 79 + v)).trans (by simp [aMap, aSize, used])
  have bFrame (r : ℕ) (safe : r ∉ [0, 6, 7]) : b.nr r = seeded.nr r := clearFrame r safe
  obtain ⟨header, read, headerLive, headerStart, headerLength, headerNat, _, _, headerFrame⟩ :=
    readMatchingCycleHeader_spec b rfl clearLive
  let c := {header with pc := 0}
  have fromSeed (r : ℕ) (safe : r ∉ [0, 6, 7, 18, 19]) : c.nr r = seeded.nr r :=
    (headerFrame r (by simp at safe ⊢; omega)).trans (bFrame r (by simp at safe ⊢; omega))
  have cOne : c.nr 9 = 1 := (fromSeed 9 (by decide)).trans aOne
  have cZero : c.nr 23 = 0 := (fromSeed 23 (by decide)).trans (by simp [seeded])
  have cStack : c.nr 80 = s.nr 80 := (fromSeed 80 (by decide)).trans (frameSeed 80 (by decide))
  have cCount : c.nr 87 = 0 := (fromSeed 87 (by decide)).trans (by simp [seeded])
  have cNat : c.nm = b.nm := headerNat
  have bStartBase : b.nr 77 = s.nr 77 := (bFrame 77 (by decide)).trans (frameSeed 77 (by decide))
  have bCountBase : b.nr 78 = s.nr 78 := (bFrame 78 (by decide)).trans (frameSeed 78 (by decide))
  have node : b.nr 22 = s.nr 22 := (bFrame 22 (by decide)).trans (frameSeed 22 (by decide))
  have ready := MatchingMemberTree.encoded_congr root.encoded root.readable (fun addr safe => clearedOutside addr safe.1)
  let jobs := children.jobs none
  let assignments := matchingMemberAssignments children
  have vertices : assignments.map Prod.fst = children.leaves := children.jobs_frontier_vertices none
  have unique : (assignments.map Prod.fst).Nodup := vertices.symm ▸ root.unique
  have inside (p : ℕ × ℕ) (present : p ∈ assignments) : p.1 < s.nr 55 := by
    apply root.valid
    rw [← vertices]
    exact List.mem_map_of_mem (f := Prod.fst) present
  have typedJobs (j : MatchingMemberJob) (present : j ∈ jobs) : matchingMemberJobValid s j :=
    ⟨children.jobs_proper none root.proper.2.2.1 j present,
      children.jobs_encoded none s.nm (s.nr 77) (s.nr 78) (s.nr 80 + 3 * s.nr 55)
        (outsideMatchingMemberScratch s) root.encoded.2.2.1 root.readable.2.2.2.1 root.above.2.1 j present⟩
  have capacity : jobs.length ≤ s.nr 55 :=
    (MatchingMemberJob.length_le_frontier jobs (fun j hj => (typedJobs j hj).1)).trans
      (MatchingMemberJob.boundedAssignments_length assignments (s.nr 55) unique inside)
  have cStart : c.nr 18 = b.nm (s.nr 77 + s.nr 22) := by
    change header.nr 18 = _
    rw [headerStart, bStartBase, node]
  have cLength : c.nr 19 = jobs.length := by
    change header.nr 19 = _
    rw [headerLength, bCountBase, node, ready.1, children.jobs_length none]
  have room : matchingMemberChildPushCount c jobs.length ≤ c.nr 18 := by
    rw [matchingMemberChildPushCount, cStack, cCount, cStart, clearedOutside _ root.readable.1.1]
    have dynamic := root.above.1
    omega
  have rows (j : ℕ) (hj : j < jobs.length) :
      let row := matchingCycleChildAt c.nm (c.nr 18 + 4 * j)
      (row.representative, row.node) = (jobs[j].representative, jobs[j].node) ∧
        jobs[j].owner = (if true then jobs[j].representative else c.nr 26) := by
    simpa [cStart, cNat, jobs] using matchingMemberJobRows (owner := none) ready.2.1 j hj
  obtain ⟨prepared, pushTicks, pushCost, push, pushed⟩ :=
    pushMatchingMemberChildren_spec true c jobs rfl headerLive cOne cZero cLength room rows
  let start := {prepared with pc := 0}
  have startMove (r : ℕ) (safe : r ∉ [0, 6, 7, 15, 16, 17, 18, 19, 25, 26, 87]) :
      start.nr r = seeded.nr r :=
    (pushed.registers r (by simp at safe ⊢; omega)).trans (fromSeed r (by simp at safe ⊢; omega))
  have sameEarlier (addr : ℕ) (outside : addr < s.nr 80 ∨ s.nr 80 + 3 * jobs.length ≤ addr) :
      start.nm addr = b.nm addr :=
    (pushed.natural addr (by simpa [matchingMemberChildPushCount, cStack, cCount] using outside)).trans (congrFun cNat addr)
  have initial : MatchingMemberWalk s assignments [] jobs 0 {start with pc := 0, nr := Function.update start.nr 24 0} := by
    refine ⟨rfl, pushed.running, ?_, ?_, by simp, ?_, ?_, ?_, typedJobs, .refl _, ?_, by simp, ?_, ?_⟩
    · intro r inList
      have no : r ≠ 24 := by simp at inList; omega
      exact (Function.update_of_ne no _ _).trans ((startMove r (by simp at inList ⊢; omega)).trans
        (frameSeed r (by simp at inList ⊢; omega)))
    · have zero := (startMove 23 (by decide)).trans (show seeded.nr 23 = 0 by simp [seeded])
      simpa [start] using zero
    · have watch := (startMove 28 (by decide)).trans (show seeded.nr 28 = 2 * s.nr 55 by simp [seeded])
      simpa [start] using watch
    · change start.nr 87 = jobs.length
      exact pushed.count.trans (by rw [cCount, Nat.zero_add])
    · intro _
      rw [Nat.zero_add, children.jobs_work none]
      have treeBound := children.nodes_add_arity_le root.proper.2.2.1
      have leafCount : children.leaves.length = assignments.length := by rw [← vertices, List.length_map]
      have card := MatchingMemberJob.boundedAssignments_length assignments (s.nr 55) unique inside
      omega
    · intro j hj
      change matchingMemberStackWords start.nm _ = _
      simpa [matchingMemberChildPushCount, cStack, cCount] using pushed.stack j hj hj
    · intro v bound _
      exact (sameEarlier _ (.inl (by have sep := root.separated; omega))).trans (clearedLeaves v bound)
    · intro address safe
      exact (sameEarlier address (by rcases safe.2 with low | high <;> omega)).trans (clearedOutside address safe.1)
  obtain ⟨t, walkTicks, walkCost, walk, runningNow, empty, zero, values, sentinel, preserved⟩ :=
    matchingMemberWalk_loop one unique inside root.separated rfl pushed.running initial
  have run : BlockRuns mapMatchingCycleNodeMembers (3 + (clearTicks + (4 + (pushTicks + walkTicks)))) s _ :=
    seed.append (clear.append (read.append (push.append walk)))
  have cost : 3 + (clearTicks + (4 + (pushTicks + walkTicks))) ≤ 93 * s.nr 55 + 13 := by
    rw [aSize] at clearCost
    omega
  have reals := mapMatchingCycleNodeMembers_keeps_reals run
  refine ⟨_, _, cost, run, runningNow, empty, zero, values, ?_, preserved, reals.2, reals.1, ?_⟩
  · intro v bound outside
    exact sentinel v bound (by rwa [vertices])
  · intro r safe
    exact mapMatchingCycleNodeMembers_keeps_register run safe

end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberMapRAM

/-! matching/MatchingMemberTopRAM.lean -/
section RppSource_MatchingMemberTopRAM
namespace VehicleRoutingSurvey.Routing

def topMatchingMemberNodeInput (s : ArithmeticState) : ArithmeticState :=
  let address := s.nr 74 + s.nr 97
  {s with pc := 0, nr := Function.update (Function.update s.nr 6 address) 22 (s.nm address)}

/-- Entry point used by blossom expansion. The selected top representative names
its node in the registry table, then the same verified traversal runs unchanged. -/
theorem mapMatchingCycleMembers_spec (s : ArithmeticState) (children : MatchingMemberTree)
    (root : MatchingMemberRoot (topMatchingMemberNodeInput s) children) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t steps, steps ≤ 93 * s.nr 55 + 15 ∧ BlockRuns mapMatchingCycleMembers steps s t ∧
      t.halted = false ∧ t.nr 87 = 0 ∧ t.nr 23 = 0 ∧
      (∀ p ∈ matchingMemberAssignments children, t.nm (s.nr 79 + p.1) = p.2) ∧
      (∀ v < s.nr 55, v ∉ children.leaves → t.nm (s.nr 79 + v) = s.nr 55) ∧
      (∀ a, outsideMatchingMemberScratch s a → t.nm a = s.nm a) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 7, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 28, 87] → t.nr r = s.nr r := by
  let input := topMatchingMemberNodeInput s
  let loaded := {input with pc := 2}
  have load : BlockRuns [.natAdd 6 74 97, .natLoad 22 6] 2 s loaded := by
    apply BlockRuns.of_running_exit
    · simp [loaded, input, topMatchingMemberNodeInput, arithmeticStep, entry, running, Function.iterate_succ_apply']
    · exact running
    · rfl
  have unchanged (r : ℕ) (six : r ≠ 6 := by decide) (node : r ≠ 22 := by decide) : input.nr r = s.nr r := by
    simp [input, topMatchingMemberNodeInput, Function.update_of_ne six, Function.update_of_ne node]
  obtain ⟨t, steps, bound, scan, live, count, zero, assignments, absent, natural, reals, registers, kept⟩ :=
    mapMatchingCycleNodeMembers_spec input children root rfl running ((unchanged 9).trans one)
  have budget : 2 + steps ≤ 93 * s.nr 55 + 15 := by rw [unchanged 55] at bound; omega
  refine ⟨_, 2 + steps, budget, load.append scan, live, count, zero, ?_, ?_, ?_, reals, registers, ?_⟩
  · intro p assigned
    change t.nm (s.nr 79 + p.1) = p.2
    simpa only [unchanged 79] using assignments p assigned
  · intro v below missing
    change t.nm (s.nr 79 + v) = s.nr 55
    simpa only [unchanged 79, unchanged 55] using absent v (by rwa [unchanged 55]) missing
  · intro a untouched
    exact natural a (by simpa only [outsideMatchingMemberScratch, unchanged 79, unchanged 80, unchanged 55] using untouched)
  · intro r safe
    exact (kept r safe).trans (unchanged r (by simp at safe; omega) (by simp at safe; omega))

end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberTopRAM

/-! matching/MatchingExpansionDirectionRAM.lean -/
section RppSource_MatchingExpansionDirectionRAM
open private chooseEvenExpansionDirection VehicleRoutingSurvey.Routing.chooseEvenExpansionDirection from Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
open private chooseForwardExpansionDistance VehicleRoutingSurvey.Routing.chooseForwardExpansionDistance from Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
open private halveExpansionDistanceCell VehicleRoutingSurvey.Routing.halveExpansionDistanceCell from Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
open private initializeExpansionHalving VehicleRoutingSurvey.Routing.initializeExpansionHalving from Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
namespace VehicleRoutingSurvey.Routing



private theorem halveExpansionDistanceCell_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (two : s.nr 49 = 2) :
    ∃ t ticks, ticks ≤ 4 ∧ BlockRuns halveExpansionDistanceCell ticks s t ∧ t.halted = false ∧
      t.nr 47 = (if 2 ≤ s.nr 47 then s.nr 47 - 2 else s.nr 47) ∧
      t.nr 95 = s.nr 95 + (if 2 ≤ s.nr 47 then 1 else 0) ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
  by_cases more : 2 ≤ s.nr 47
  · let t := (arithmeticStep halveExpansionDistanceCell)^[4] s
    have result : t.pc = halveExpansionDistanceCell.length ∧ t.halted = false ∧
        t.nr 47 = (if 2 ≤ s.nr 47 then s.nr 47 - 2 else s.nr 47) ∧
        t.nr 95 = s.nr 95 + (if 2 ≤ s.nr 47 then 1 else 0) ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
      simp [t, halveExpansionDistanceCell, arithmeticStep, entry, running, one, two, more, Function.iterate_succ_apply']
    exact ⟨t, 4, le_rfl, BlockRuns.of_running_exit rfl result.2.1 result.1, result.2⟩
  · let t := arithmeticStep halveExpansionDistanceCell s
    have result : t.pc = halveExpansionDistanceCell.length ∧ t.halted = false ∧
        t.nr 47 = (if 2 ≤ s.nr 47 then s.nr 47 - 2 else s.nr 47) ∧
        t.nr 95 = s.nr 95 + (if 2 ≤ s.nr 47 then 1 else 0) ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
      simp [t, halveExpansionDistanceCell, arithmeticStep, entry, running, two, more]
    exact ⟨t, 1, by decide, BlockRuns.of_running_exit rfl result.2.1 result.1, result.2⟩





private structure ExpansionHalving (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 24 = i
  registeredTwo : s.nr 49 = 2
  preserved : ∀ r, r ∉ [0, 24, 47, 49, 95] → s.nr r = initial.nr r
  balance : s.nr 47 + 2 * s.nr 95 = initial.nr 46
  progress : 2 ≤ s.nr 47 → i ≤ s.nr 95
  natural : s.nm = initial.nm
  real : s.rm = initial.rm
  realRegisters : s.rr = initial.rr

theorem halveExpansionDistance_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0)
    (bounded : s.nr 46 ≤ s.nr 55) :
    ∃ t steps, steps ≤ 7 * s.nr 55 + 5 ∧ BlockRuns halveExpansionDistance steps s t ∧ t.halted = false ∧
      t.nr 47 + 2 * t.nr 95 = s.nr 46 ∧ t.nr 47 ≤ 1 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 24, 47, 49, 95] → t.nr r = s.nr r := by
  let seeded := { s with
    pc := 3
    nr := Function.update (Function.update (Function.update s.nr 49 2) 47 (s.nr 46)) 95 0 }
  have seed : BlockRuns initializeExpansionHalving 3 s seeded := by
    apply BlockRuns.of_running_exit
    · simp [seeded, initializeExpansionHalving, arithmeticStep, entry, running, zero, Function.iterate_succ_apply']
    · exact running
    · rfl
  let start := {seeded with pc := 0}
  have init : ExpansionHalving s 0 {start with pc := 0, nr := Function.update start.nr 24 0} := by
    refine ⟨rfl, running, by simp, by simp [start, seeded], ?_, by simp [start, seeded], ?_, rfl, rfl, rfl⟩
    · intro r outside
      have a : r ≠ 24 := by simp at outside; omega
      have b : r ≠ 47 := by simp at outside; omega
      have c : r ≠ 49 := by simp at outside; omega
      have d : r ≠ 95 := by simp at outside; omega
      simp [start, seeded, Function.update_of_ne a, Function.update_of_ne b, Function.update_of_ne c, Function.update_of_ne d]
    · intro _
      exact Nat.zero_le _
  have iteration (i : ℕ) (_ : i < s.nr 55) (m : ArithmeticState) (before : ExpansionHalving s i m) :
      ∃ t ticks, ticks ≤ 4 ∧ BlockRuns halveExpansionDistanceCell ticks m t ∧ t.halted = false ∧
        ExpansionHalving s (i + 1) {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)} := by
    have mOne : m.nr 9 = 1 := (before.preserved 9 (by decide)).trans one
    obtain ⟨t, ticks, cost, run, live, residual, count, natural, real, regs⟩ :=
      halveExpansionDistanceCell_spec m before.entry before.running mOne before.registeredTwo
    have keeps (r : ℕ) (outside : r ∉ [0, 47, 95]) : t.nr r = m.nr r := by
      rw [← run.run]
      exact arithmeticRun_keeps_from_destination_list [0, 47, 95] (by decide) outside m ticks
    refine ⟨t, ticks, cost, run, live, rfl, live, ?_, ?_, ?_, ?_, ?_, natural.trans before.natural,
      real.trans before.real, regs.trans before.realRegisters⟩
    · simp [keeps 24 (by decide), keeps 9 (by decide), before.index, mOne]
    · exact (keeps 49 (by decide)).trans before.registeredTwo
    · intro r outside
      have a : r ≠ 24 := by simp at outside; omega
      have b : r ∉ [0, 47, 95] := by simp at outside ⊢; omega
      exact (Function.update_of_ne a _ _).trans ((keeps r b).trans (before.preserved r outside))
    · change t.nr 47 + 2 * t.nr 95 = s.nr 46
      rw [residual, count]
      by_cases more : 2 ≤ m.nr 47 <;> simp [more] <;> have h := before.balance <;> omega
    · change 2 ≤ t.nr 47 → i + 1 ≤ t.nr 95
      rw [residual, count]
      by_cases more : 2 ≤ m.nr 47
      · have prev := before.progress more
        simp [more] <;> omega
      · simp [more]
  obtain ⟨last, ticks, done, cost, complete⟩ := countedLoopFromZero_bounded 9 24 55 (s.nr 55) 4
    halveExpansionDistanceCell (ExpansionHalving s) (s := start) rfl running init
    (fun _ _ h => ⟨h.entry, h.running, h.index, h.preserved 55 (by decide)⟩) iteration
  have small : last.nr 47 ≤ 1 := by
    by_contra big
    have more : 2 ≤ last.nr 47 := by omega
    have count := done.progress more
    have balance := done.balance
    omega
  exact ⟨_, 3 + ticks, by omega, seed.append complete, done.running, done.balance, small, done.natural, done.real,
    done.realRegisters, done.preserved⟩



def expansionForwardDistance (s : ArithmeticState) : ℕ :=
  if s.nr 81 ≤ s.nr 82 then s.nr 82 - s.nr 81 else s.nr 19 - (s.nr 81 - s.nr 82)

private theorem chooseForwardExpansionDistance_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    ∃ t, BlockRuns chooseForwardExpansionDistance 3 s t ∧ t.halted = false ∧
      t.nr 46 = expansionForwardDistance s ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 46] → t.nr r = s.nr r := by
  have fixed {t : ArithmeticState} (run : BlockRuns chooseForwardExpansionDistance 3 s t)
      (r : ℕ) (outside : r ∉ [0, 6, 46]) : t.nr r = s.nr r := by
    rw [← run.run]
    exact arithmeticRun_keeps_from_destination_list [0, 6, 46] (by decide) outside s 3
  by_cases forward : s.nr 81 ≤ s.nr 82
  · let t := {s with pc := 1, nr := Function.update s.nr 46 (s.nr 82 - s.nr 81)}
    have run : BlockRuns [.natSub 46 82 81] 1 s t := by
      apply BlockRuns.of_running_exit
      · simp [t, arithmeticStep, entry, running]
      · exact running
      · rfl
    have routed := branchOnAtMost_left 81 82 [.natSub 46 82 81] [.natSub 6 81 82, .natSub 46 19 6]
      entry running forward run running
    refine ⟨_, routed, running, ?_, rfl, rfl, rfl, fixed routed⟩
    change t.nr 46 = expansionForwardDistance s
    simp [t, expansionForwardDistance, forward]
  · let t := { s with
      pc := 2
      nr := Function.update (Function.update s.nr 6 (s.nr 81 - s.nr 82)) 46 (s.nr 19 - (s.nr 81 - s.nr 82)) }
    have run : BlockRuns [.natSub 6 81 82, .natSub 46 19 6] 2 s t := by
      apply BlockRuns.of_running_exit
      · simp [t, arithmeticStep, entry, running, Function.iterate_succ_apply']
      · exact running
      · rfl
    have routed := branchOnAtMost_right 81 82 [.natSub 46 82 81] [.natSub 6 81 82, .natSub 46 19 6]
      entry running (Nat.lt_of_not_ge forward) run running
    refine ⟨_, routed, running, ?_, rfl, rfl, rfl, fixed routed⟩
    change t.nr 46 = expansionForwardDistance s
    simp [t, expansionForwardDistance, forward]





theorem chooseMatchingExpansionDirection_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0)
    (entryIndex : s.nr 81 < s.nr 19) (baseIndex : s.nr 82 < s.nr 19)
    (oddLength : Odd (s.nr 19)) (smallCycle : s.nr 19 ≤ s.nr 55) :
    ∃ t steps, steps ≤ 14 * s.nr 55 + 16 ∧ BlockRuns chooseMatchingExpansionDirection steps s t ∧ t.halted = false ∧
      t.nr 45 = (if Even (expansionForwardDistance s) then 0 else 1) ∧
      t.nr 46 = (if Even (expansionForwardDistance s) then expansionForwardDistance s else s.nr 19 - expansionForwardDistance s) ∧
      t.nr 46 = 2 * t.nr 95 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
  let d := expansionForwardDistance s
  have dBound : d < s.nr 19 := by
    by_cases order : s.nr 81 ≤ s.nr 82 <;> simp [d, expansionForwardDistance, order] <;> omega
  obtain ⟨first, firstRun, live, forward, natOne, realOne, rrOne, firstKeeps⟩ :=
    chooseForwardExpansionDistance_spec s entry running
  let a := {first with pc := 0}
  have aOne : a.nr 9 = 1 := (firstKeeps 9 (by decide)).trans one
  have aZero : a.nr 23 = 0 := (firstKeeps 23 (by decide)).trans zero
  have aDim : a.nr 55 = s.nr 55 := firstKeeps 55 (by decide)
  have aDist : a.nr 46 = d := forward
  obtain ⟨half, halfSteps, halfBudget, halfRun, halfLive, halfBalance, halfSmall, halfNat, halfReal, halfRR, halfKeeps⟩ :=
    halveExpansionDistance_spec a rfl live aOne aZero (by rw [aDim, aDist]; omega)
  let b := {half with pc := 0}
  have bEntry : b.pc = 0 := rfl
  have bLive : b.halted = false := halfLive
  have bDist : b.nr 46 = d := (halfKeeps 46 (by decide)).trans aDist
  have bZero : b.nr 23 = 0 := (halfKeeps 23 (by decide)).trans aZero
  have bOne : b.nr 9 = 1 := (halfKeeps 9 (by decide)).trans aOne
  have bDim : b.nr 55 = s.nr 55 := (halfKeeps 55 (by decide)).trans aDim
  have bSize : b.nr 19 = s.nr 19 := (halfKeeps 19 (by decide)).trans (firstKeeps 19 (by decide))
  have representation : b.nr 47 + 2 * b.nr 95 = d := halfBalance.trans aDist
  have remBound : b.nr 47 ≤ 1 := halfSmall
  rw [aDim] at halfBudget
  by_cases even : b.nr 47 = 0
  · let t := {b with pc := 1, nr := Function.update b.nr 45 0}
    have step : BlockRuns [.natConst 45 0] 1 b t := by
      apply BlockRuns.of_running_exit
      · simp [t, arithmeticStep, bEntry, bLive]
      · exact bLive
      · rfl
    have ran := branchOnAtMost_left 47 23 [.natConst 45 0]
      (appendBlock [.natConst 45 1, .natSub 46 19 46] halveExpansionDistance) (s := b) rfl halfLive
      (by rw [even, bZero]) step halfLive
    have dEven : Even (expansionForwardDistance s) := ⟨b.nr 95, by change d = _; omega⟩
    refine ⟨_, 3 + (halfSteps + 3), by omega, firstRun.append (halfRun.append ran), halfLive,
      ?_, ?_, ?_, halfNat.trans natOne, halfReal.trans realOne, halfRR.trans rrOne⟩
    · change t.nr 45 = _
      simp [t, dEven]
    · change t.nr 46 = _
      rw [if_pos dEven]
      exact bDist
    · change t.nr 46 = 2 * t.nr 95
      change b.nr 46 = 2 * b.nr 95
      omega
  · have oneLeft : b.nr 47 = 1 := by omega
    have dOdd : ¬Even (expansionForwardDistance s) := by
      rintro ⟨q, eq⟩
      change d = q + q at eq
      omega
    let rev := s.nr 19 - d
    let reversed := { b with
      pc := 2
      nr := Function.update (Function.update b.nr 45 1) 46 rev }
    have turn : BlockRuns [.natConst 45 1, .natSub 46 19 46] 2 b reversed := by
      apply BlockRuns.of_running_exit
      · simp [reversed, rev, arithmeticStep, bEntry, bLive, bSize, bDist, Function.iterate_succ_apply']
      · exact bLive
      · rfl
    let aRev := {reversed with pc := 0}
    have dim : aRev.nr 55 = s.nr 55 := bDim
    have amount : aRev.nr 46 = rev := by simp [aRev, reversed]
    obtain ⟨t, revSteps, revBudget, revRun, revLive, revBalance, revSmall, revNat, revReal, revRR, revKeeps⟩ :=
      halveExpansionDistance_spec aRev rfl halfLive bOne bZero (by rw [amount, dim]; dsimp [rev]; omega)
    have selected := branchOnAtMost_right 47 23 [.natConst 45 0]
      (appendBlock [.natConst 45 1, .natSub 46 19 46] halveExpansionDistance) (s := b) rfl halfLive
      (by rw [oneLeft, bZero] <;> decide) (turn.append revRun) revLive
    have revEven : rev % 2 = 0 := by
      have odd := Nat.odd_iff.mp oddLength
      dsimp [rev]
      omega
    have remain : t.nr 47 = 0 := by omega
    rw [dim] at revBudget
    refine ⟨_, 3 + (halfSteps + (1 + (2 + revSteps))), by omega,
      firstRun.append (halfRun.append selected), revLive, ?_, ?_, ?_,
      revNat.trans (halfNat.trans natOne), revReal.trans (halfReal.trans realOne), revRR.trans (halfRR.trans rrOne)⟩
    · change t.nr 45 = _
      rw [if_neg dOdd, revKeeps 45 (by decide)]
      simp [aRev, reversed]
    · change t.nr 46 = _
      rw [if_neg dOdd, revKeeps 46 (by decide), amount]
    · change t.nr 46 = 2 * t.nr 95
      have counted := revBalance.trans amount
      rw [revKeeps 46 (by decide), amount]
      omega

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionDirectionRAM

/-! matching/MatchingForestWitnessRAM.lean -/
section RppSource_MatchingForestWitnessRAM
namespace VehicleRoutingSurvey.Routing





def writeMatchingForestWitness (memory : ℕ → ℕ) (base child : ℕ) (edge : ℕ × ℕ) : ℕ → ℕ :=
  let addr := forestWitnessAddress base child
  Function.update (Function.update memory addr edge.1) (addr + 1) edge.2

theorem matchingForestWitnessAt_write_same (memory : ℕ → ℕ) (base child : ℕ) (edge : ℕ × ℕ) :
    matchingForestWitnessAt (writeMatchingForestWitness memory base child edge) base child = edge := by
  rcases edge with ⟨u, v⟩
  simp (disch := omega) [matchingForestWitnessAt, writeMatchingForestWitness, forestWitnessAddress,
    Function.update_of_ne]

theorem matchingForestWitnessAt_write_other (memory : ℕ → ℕ) (base child other : ℕ)
    (edge : ℕ × ℕ) (distinct : other ≠ child) :
    matchingForestWitnessAt (writeMatchingForestWitness memory base child edge) base other =
      matchingForestWitnessAt memory base other := by
  simp (disch := omega) [matchingForestWitnessAt, writeMatchingForestWitness, forestWitnessAddress,
    Function.update_of_ne]

































end VehicleRoutingSurvey.Routing
end RppSource_MatchingForestWitnessRAM

/-! matching/MatchingExpansionSearchRAM.lean -/
section RppSource_MatchingExpansionSearchRAM
open private chooseExpansionEntryChild VehicleRoutingSurvey.Routing.chooseExpansionEntryChild from Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
open private fetchExpansionParentWitness VehicleRoutingSurvey.Routing.fetchExpansionParentWitness from Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
namespace VehicleRoutingSurvey.Routing



def expansionEntryOriginal (s : ArithmeticState) : ℕ :=
  let edge := expansionOldParentWitness s
  if s.nm (s.nr 57 + edge.1) = s.nr 97 then edge.1 else edge.2

def expansionEntryChild (s : ArithmeticState) : ℕ := s.nm (s.nr 79 + expansionEntryOriginal s)

















private def expansionWitnessReadState (s : ArithmeticState) : ArithmeticState :=
  let edge := expansionOldParentWitness s
  let zero := Function.update s.nr 23 0
  let parent := Function.update zero 96 (s.nm (s.nr 52 + s.nr 97))
  let mate := Function.update parent 98 (s.nm (s.nr 50 + s.nr 97))
  let witness := Function.update (Function.update mate 43 edge.1) 44 edge.2
  { s with
    pc := 12
    nr := Function.update (Function.update witness 6 (s.nr 57 + edge.1)) 10 (s.nm (s.nr 57 + edge.1)) }

private theorem fetchExpansionParentWitness_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    BlockRuns fetchExpansionParentWitness 12 s (expansionWitnessReadState s) := by
  apply BlockRuns.of_running_exit
  · simp [expansionWitnessReadState, fetchExpansionParentWitness, arithmeticStep, entry, running, one,
      expansionOldParentWitness, matchingForestWitnessAt, forestWitnessAddress, Function.iterate_succ_apply',
      Function.update_idem]
    funext r
    by_cases scratch : r = 6 <;> simp [Function.update_apply, scratch]
  · exact running
  · rfl

private theorem chooseExpansionEntryChild_spec (original : ℕ) (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    let t := { s with
      pc := 2
      nr := Function.update (Function.update s.nr 6 (s.nr 79 + s.nr original)) 27 (s.nm (s.nr 79 + s.nr original)) }
    BlockRuns (chooseExpansionEntryChild original) 2 s t := by
  dsimp only
  apply BlockRuns.of_running_exit
  · simp [chooseExpansionEntryChild, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · exact running
  · rfl

theorem findExpansionEntryChild_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t steps, steps ≤ 18 ∧ BlockRuns findExpansionEntryChild steps s t ∧ t.halted = false ∧
      t.nr 27 = expansionEntryChild s ∧ t.nr 96 = s.nm (s.nr 52 + s.nr 97) ∧
      t.nr 98 = s.nm (s.nr 50 + s.nr 97) ∧ (t.nr 43, t.nr 44) = expansionOldParentWitness s ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧ t.nr 23 = 0 := by
  let p := {expansionWitnessReadState s with pc := 0}
  have fetch := fetchExpansionParentWitness_spec s entry running one
  have readRole : p.nr 10 = s.nm (s.nr 57 + (expansionOldParentWitness s).1) := by simp [p, expansionWitnessReadState]
  have base : p.nr 97 = s.nr 97 := by simp [p, expansionWitnessReadState]
  have parent : p.nr 96 = s.nm (s.nr 52 + s.nr 97) := by simp [p, expansionWitnessReadState]
  have mate : p.nr 98 = s.nm (s.nr 50 + s.nr 97) := by simp [p, expansionWitnessReadState]
  have edge : (p.nr 43, p.nr 44) = expansionOldParentWitness s := by simp [p, expansionWitnessReadState]
  have map : p.nr 79 = s.nr 79 := by simp [p, expansionWitnessReadState]
  have left := chooseExpansionEntryChild_spec 43 p rfl running
  have right := chooseExpansionEntryChild_spec 44 p rfl running
  rcases lt_trichotomy (p.nr 10) (p.nr 97) with below | equal | above
  · have branch := branchOnAtMost_right 97 10 (chooseExpansionEntryChild 43) (chooseExpansionEntryChild 44)
      (s := p) rfl running below right running
    have routed := branchOnAtMost_left 10 97 _ (chooseExpansionEntryChild 44) (s := p) rfl running below.le branch running
    have outside : s.nm (s.nr 57 + (expansionOldParentWitness s).1) ≠ s.nr 97 := by
      simpa only [readRole, base] using below.ne
    refine ⟨_, 12 + (1 + (1 + 2) + 1), by decide, fetch.append routed, running, ?_, parent, mate, edge, rfl, rfl, rfl, rfl⟩
    change p.nm (p.nr 79 + p.nr 44) = expansionEntryChild s
    have rightEdge : p.nr 44 = (expansionOldParentWitness s).2 := congrArg Prod.snd edge
    rw [expansionEntryChild, expansionEntryOriginal, if_neg outside, map, rightEdge] <;> rfl
  · have branch := branchOnAtMost_left 97 10 (chooseExpansionEntryChild 43) (chooseExpansionEntryChild 44)
      (s := p) rfl running equal.ge left running
    have routed := branchOnAtMost_left 10 97 _ (chooseExpansionEntryChild 44) (s := p) rfl running equal.le branch running
    have inside : s.nm (s.nr 57 + (expansionOldParentWitness s).1) = s.nr 97 := by
      simpa only [readRole, base] using equal
    refine ⟨_, 18, le_rfl, fetch.append routed, running, ?_, parent, mate, edge, rfl, rfl, rfl, rfl⟩
    change p.nm (p.nr 79 + p.nr 43) = expansionEntryChild s
    have leftEdge : p.nr 43 = (expansionOldParentWitness s).1 := congrArg Prod.fst edge
    rw [expansionEntryChild, expansionEntryOriginal, if_pos inside, map, leftEdge] <;> rfl
  · have routed := branchOnAtMost_right 10 97 (branchOnAtMost 97 10
      (chooseExpansionEntryChild 43) (chooseExpansionEntryChild 44)) (chooseExpansionEntryChild 44)
      (s := p) rfl running above right running
    have outside : s.nm (s.nr 57 + (expansionOldParentWitness s).1) ≠ s.nr 97 := by
      simpa only [readRole, base] using above.ne'
    refine ⟨_, 15, by decide, fetch.append routed, running, ?_, parent, mate, edge, rfl, rfl, rfl, rfl⟩
    change p.nm (p.nr 79 + p.nr 44) = expansionEntryChild s
    have rightEdge : p.nr 44 = (expansionOldParentWitness s).2 := congrArg Prod.snd edge
    rw [expansionEntryChild, expansionEntryOriginal, if_neg outside, map, rightEdge] <;> rfl

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionSearchRAM

/-! matching/MatchingRebasePair.lean -/
section RppSource_MatchingRebasePair
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing



theorem advanceMatchingCycleIndexBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (inside : s.nr 7 < s.nr 19) :
    let index := (s.nr 7 + 1) % s.nr 19
    let t := {s with pc := 3, nr := Function.update s.nr 7 index}
    ∃ steps ≤ 3, BlockRuns advanceMatchingCycleIndexBlock steps s t := by
  intro index t
  by_cases wraps : s.nr 19 ≤ s.nr 7 + 1
  · have atEnd : s.nr 7 + 1 = s.nr 19 := by omega
    have indexEq : index = 0 := by simp [index, atEnd]
    refine ⟨3, le_rfl, BlockRuns.of_running_exit ?_ (show t.halted = false from running) rfl⟩
    simp [t, advanceMatchingCycleIndexBlock, arithmeticStep, entry, running, one,
      wraps, indexEq, Function.iterate_succ_apply', Function.update_idem]
  · have indexEq : index = s.nr 7 + 1 := Nat.mod_eq_of_lt (lt_of_not_ge wraps)
    refine ⟨2, by decide, BlockRuns.of_running_exit ?_ (show t.halted = false from running) rfl⟩
    simp [t, advanceMatchingCycleIndexBlock, arithmeticStep, entry, running, one,
      wraps, indexEq, Function.iterate_succ_apply']


















end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebasePair

/-! matching/MatchingExpansionEmitRAM.lean -/
section RppSource_MatchingExpansionEmitRAM
namespace VehicleRoutingSurvey.Routing



theorem retreatMatchingCycleIndexBlock_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0) :
    let index := if s.nr 7 = 0 then s.nr 19 - 1 else s.nr 7 - 1
    let t := {s with pc := 4, nr := Function.update s.nr 7 index}
    ∃ steps ≤ 3, BlockRuns retreatMatchingCycleIndexBlock steps s t := by
  intro index t
  by_cases wraps : s.nr 7 = 0
  · refine ⟨2, by decide, BlockRuns.of_running_exit ?_ (show t.halted = false from running) rfl⟩
    simp [t, index, retreatMatchingCycleIndexBlock, arithmeticStep, entry, running, wraps, one, zero,
      Function.iterate_succ_apply']
  · refine ⟨3, le_rfl, BlockRuns.of_running_exit ?_ (show t.halted = false from running) rfl⟩
    simp [t, index, retreatMatchingCycleIndexBlock, arithmeticStep, entry, running, wraps, one, zero,
      Function.iterate_succ_apply']

def expansionPathTripleMemory (s : ArithmeticState) : ℕ → ℕ :=
  let cursor := s.nr 47
  Function.update (Function.update (Function.update s.nm cursor (s.nr 15)) (cursor + 1) (s.nr 16))
    (cursor + 2) (s.nr 17)



theorem writeMatchingExpansionPathTriple_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns writeMatchingExpansionPathTriple 6 s t ∧ t.halted = false ∧
      t.nr 47 = s.nr 47 + 3 ∧ t.nm = expansionPathTripleMemory s ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 47] → t.nr r = s.nr r := by
  let t := (arithmeticStep writeMatchingExpansionPathTriple)^[6] s
  have two : s.nr 47 + 1 + 1 = s.nr 47 + 2 := by omega
  have three : s.nr 47 + 1 + 1 + 1 = s.nr 47 + 3 := by omega
  have effect : t.pc = writeMatchingExpansionPathTriple.length ∧ t.halted = false ∧
      t.nr 47 = s.nr 47 + 3 ∧ t.nm = expansionPathTripleMemory s ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, writeMatchingExpansionPathTriple, expansionPathTripleMemory, arithmeticStep, entry, running, one,
      two, three, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1, effect.2.2.1,
    effect.2.2.2.1, effect.2.2.2.2.1, effect.2.2.2.2.2, ?_⟩
  intro r outside
  exact arithmeticRun_keeps_from_destination_list [0, 47] (by decide) outside s 6









end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionEmitRAM

/-! matching/ExpansionRepresentativeRAM.lean -/
section RppSource_ExpansionRepresentativeRAM
open private publishExpansionRepresentativeCell VehicleRoutingSurvey.Routing.publishExpansionRepresentativeCell from Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
namespace VehicleRoutingSurvey.Routing





def expandedRepresentativeMemory (s : ArithmeticState) (processed : ℕ) : ℕ → ℕ :=
  fun a => if s.nr 57 ≤ a ∧ a < s.nr 57 + processed then
    let child := s.nm (s.nr 79 + (a - s.nr 57))
    if child < s.nr 55 then child else s.nm a
  else s.nm a

private theorem publishExpansionRepresentativeCell_spec {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    let child := s.nm (s.nr 79 + s.nr 7)
    ∃ t, BlockRuns publishExpansionRepresentativeCell 6 s t ∧ t.halted = false ∧
      t.nm = (if child < s.nr 55 then Function.update s.nm (s.nr 57 + s.nr 7) child else s.nm) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ≠ 6 → r ≠ 10 → t.nr r = s.nr r := by
  intro child
  let t := (arithmeticStep publishExpansionRepresentativeCell)^[6] s
  have ran : t.pc = publishExpansionRepresentativeCell.length ∧ t.halted = false ∧
      t.nm = (if child < s.nr 55 then Function.update s.nm (s.nr 57 + s.nr 7) child else s.nm) ∧
      t.rm = s.rm ∧ t.rr = s.rr := by
    by_cases skip : s.nr 55 ≤ s.nm (s.nr 79 + s.nr 7)
    · simp [t, child, publishExpansionRepresentativeCell, arithmeticStep, entry, running,
        skip, Nat.not_lt_of_ge skip, Function.iterate_succ_apply']
    · simp [t, child, publishExpansionRepresentativeCell, arithmeticStep, entry, running,
        skip, Nat.lt_of_not_ge skip, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl ran.2.1 ran.1, ran.2.1, ran.2.2.1,
    ran.2.2.2.1, ran.2.2.2.2, ?_⟩
  intro r except6 except10
  by_cases skip : s.nr 55 ≤ s.nm (s.nr 79 + s.nr 7) <;>
    simp [t, publishExpansionRepresentativeCell, arithmeticStep, entry, running, skip,
      Function.iterate_succ_apply', Function.update_of_ne except6, Function.update_of_ne except10]

private theorem expandedRepresentativeMemory_step (s : ArithmeticState) (i : ℕ)
    (within : i < s.nr 55) (disjoint : s.nr 57 + s.nr 55 ≤ s.nr 79) :
    let memory := expandedRepresentativeMemory s i
    let child := memory (s.nr 79 + i)
    (if child < s.nr 55 then Function.update memory (s.nr 57 + i) child else memory) =
      expandedRepresentativeMemory s (i + 1) := by
  intro memory child
  have originalChild : child = s.nm (s.nr 79 + i) := by
    change expandedRepresentativeMemory s i (s.nr 79 + i) = _
    rw [expandedRepresentativeMemory, if_neg (by omega)]
  funext a
  by_cases current : a = s.nr 57 + i
  · subst a
    have new : s.nr 57 ≤ s.nr 57 + i ∧ s.nr 57 + i < s.nr 57 + (i + 1) := by omega
    have same : s.nr 57 + i - s.nr 57 = i := by omega
    by_cases member : s.nm (s.nr 79 + i) < s.nr 55
    · simp [originalChild, member, expandedRepresentativeMemory, new, same]
    · have old : ¬(s.nr 57 ≤ s.nr 57 + i ∧ s.nr 57 + i < s.nr 57 + i) := by omega
      simp [originalChild, member, memory, expandedRepresentativeMemory, new, old, same]
  · have unaffected : (s.nr 57 ≤ a ∧ a < s.nr 57 + i) ↔ (s.nr 57 ≤ a ∧ a < s.nr 57 + (i + 1)) := by omega
    by_cases member : child < s.nr 55 <;>
      simp [member, memory, expandedRepresentativeMemory, unaffected, Function.update_of_ne current]

private structure ExpansionRepresentativeScan (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  ready : s.halted = false
  index : s.nr 7 = i
  fixed : ∀ r, r ∉ [6, 7, 10] → s.nr r = initial.nr r
  memory : s.nm = expandedRepresentativeMemory initial i
  real : s.rm = initial.rm
  realRegisters : s.rr = initial.rr

/-- The DFS leaves a child representative in range for a vertex inside the
expanded blossom and a sentinel elsewhere. Publish exactly the in-range entries. -/
theorem publishExpansionRepresentatives_spec {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (disjoint : s.nr 57 + s.nr 55 ≤ s.nr 79) :
    ∃ t, BlockRuns publishExpansionRepresentatives (9 * s.nr 55 + 2) s t ∧ t.halted = false ∧
      t.nm = expandedRepresentativeMemory s (s.nr 55) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [6, 7, 10] → t.nr r = s.nr r := by
  let inv := ExpansionRepresentativeScan s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, ?_, rfl, rfl⟩
    · intro r outside
      have safe : r ≠ 7 := fun eq => outside (eq.symm ▸ (by decide : (7 : ℕ) ∈ [6, 7, 10]))
      exact Function.update_of_ne safe _ _
    · funext a
      change s.nm a = expandedRepresentativeMemory s 0 a
      rw [expandedRepresentativeMemory, if_neg (by omega)]
  have control (i : ℕ) (m : ArithmeticState) (h : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 55 = s.nr 55 :=
    ⟨h.entry, h.ready, h.index, h.fixed 55 (by decide)⟩
  have next (i : ℕ) (within : i < s.nr 55) (m : ArithmeticState) (h : inv i m) :
      ∃ t, BlockRuns publishExpansionRepresentativeCell 6 m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    obtain ⟨t, run, ready, natural, real, realRegisters, fixed⟩ := publishExpansionRepresentativeCell_spec h.entry h.ready
    refine ⟨t, run, ready, rfl, ready, ?_, ?_, ?_, real.trans h.real, realRegisters.trans h.realRegisters⟩
    · simp [fixed 7 (by decide) (by decide), h.index, fixed 9 (by decide) (by decide), h.fixed 9 (by decide), one]
    · intro r safe
      have outside (j : ℕ) (used : j ∈ ([6, 7, 10] : List ℕ)) : r ≠ j := fun eq => safe (eq.symm ▸ used)
      change Function.update t.nr 7 (t.nr 7 + t.nr 9) r = s.nr r
      rw [Function.update_of_ne (outside 7 (by decide))]
      exact (fixed r (outside 6 (by decide)) (outside 10 (by decide))).trans (h.fixed r safe)
    · change t.nm = _
      rw [natural, h.memory, h.fixed 55 (by decide), h.fixed 57 (by decide), h.fixed 79 (by decide), h.index]
      exact expandedRepresentativeMemory_step s i within disjoint
  obtain ⟨_, final, run⟩ := countedLoopFromZero_correct 9 7 55 (s.nr 55) 6
    publishExpansionRepresentativeCell inv (s := s) entry running initial control next
  have steps : 1 + (s.nr 55 * (6 + 3) + 1) = 9 * s.nr 55 + 2 := by omega
  rw [steps] at run
  exact ⟨_, run, final.ready, final.memory, final.real, final.realRegisters, final.fixed⟩

theorem expandedRepresentativeMemory_at (s : ArithmeticState) {v : ℕ} (within : v < s.nr 55) :
    expandedRepresentativeMemory s (s.nr 55) (s.nr 57 + v) =
      if s.nm (s.nr 79 + v) < s.nr 55 then s.nm (s.nr 79 + v) else s.nm (s.nr 57 + v) := by
  rw [expandedRepresentativeMemory, if_pos (by omega), show s.nr 57 + v - s.nr 57 = v by omega]

theorem expandedRepresentativeMemory_outside (s : ArithmeticState) {a : ℕ}
    (outside : a < s.nr 57 ∨ s.nr 57 + s.nr 55 ≤ a) :
    expandedRepresentativeMemory s (s.nr 55) a = s.nm a := by
  rw [expandedRepresentativeMemory, if_neg (by omega)]

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionRepresentativeRAM

/-! matching/ExpansionRegistryRAM.lean -/
section RppSource_ExpansionRegistryRAM
open private publishExpansionNodeCell VehicleRoutingSurvey.Routing.publishExpansionNodeCell from Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
open private storeExpansionNode VehicleRoutingSurvey.Routing.storeExpansionNode from Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
namespace VehicleRoutingSurvey.Routing







private theorem storeExpansionNode_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) :
    ∃ t, BlockRuns storeExpansionNode 2 s t ∧ t.halted = false ∧
      t.nm = Function.update s.nm (s.nr 74 + s.nr 15) (s.nr 25) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ≠ 6 → t.nr r = s.nr r := by
  let t := (arithmeticStep storeExpansionNode)^[2] s
  have ready : t.halted = false := by
    simp [t, storeExpansionNode, arithmeticStep, Function.iterate_succ_apply', entry, running]
  have exit : t.pc = storeExpansionNode.length := by
    simp [t, storeExpansionNode, arithmeticStep, Function.iterate_succ_apply', entry, running]
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_⟩
  all_goals first
  | intro r safe
    simp [t, storeExpansionNode, arithmeticStep, Function.iterate_succ_apply', entry, running,
      Function.update_of_ne safe]
  | simp [t, storeExpansionNode, arithmeticStep, Function.iterate_succ_apply', entry, running]

private theorem publishExpansionNodeCell_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns publishExpansionNodeCell 12 s t ∧ t.halted = false ∧
      t.nm = Function.update s.nm (s.nr 74 + (expansionCycleRow s (s.nr 7)).representative)
        (expansionCycleRow s (s.nr 7)).node ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 15, 16, 17, 25] → t.nr r = s.nr r := by
  obtain ⟨m, reads, live, value, nat, real, rr, fixed⟩ := readMatchingCycleChild_spec s entry running one
  let ready := {m with pc := 0}
  obtain ⟨t, writes, stillLive, output, finalReal, finalRr, finalFixed⟩ :=
    storeExpansionNode_spec (s := ready) rfl live
  have owner : m.nr 15 = (expansionCycleRow s (s.nr 7)).representative :=
    congrArg MatchingCycleChild.representative value
  have node : m.nr 25 = (expansionCycleRow s (s.nr 7)).node := congrArg MatchingCycleChild.node value
  refine ⟨_, reads.append writes, stillLive, ?_, finalReal.trans real, finalRr.trans rr, ?_⟩
  · change t.nm = _
    rw [output]
    change Function.update m.nm (m.nr 74 + m.nr 15) (m.nr 25) = _
    rw [nat, fixed 74 (by decide), owner, node]
  · intro r safe
    exact (finalFixed r (by simp at safe; omega)).trans (fixed r safe)

private def expansionNodeScratch : List ℕ := [0, 6, 7, 15, 16, 17, 25]

private structure ExpansionNodeScan (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  ready : s.halted = false
  index : s.nr 7 = i
  fixed : ∀ r, r ∉ expansionNodeScratch → s.nr r = initial.nr r
  records : ∀ j < i, s.nm (initial.nr 74 + (expansionCycleRow initial j).representative) =
    (expansionCycleRow initial j).node
  kept : ∀ a, (∀ j < i, a ≠ initial.nr 74 + (expansionCycleRow initial j).representative) →
    s.nm a = initial.nm a
  real : s.rm = initial.rm
  realRegisters : s.rr = initial.rr



/-- Restore the direct child node ids in the top-level registry. The
persisted cycle remains available for later descent and keeps its orientation. -/
theorem publishExpansionNodes_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (recordAfter : s.nr 74 + s.nr 55 ≤ s.nr 18)
    (inRange : ∀ i < s.nr 19, (expansionCycleRow s i).representative < s.nr 55)
    (distinct : ∀ i < s.nr 19, ∀ j < s.nr 19,
      (expansionCycleRow s i).representative = (expansionCycleRow s j).representative → i = j) :
    ∃ t, BlockRuns publishExpansionNodes (15 * s.nr 19 + 2) s t ∧ t.halted = false ∧
      (∀ j < s.nr 19, t.nm (s.nr 74 + (expansionCycleRow s j).representative) = (expansionCycleRow s j).node) ∧
      (∀ a, (∀ j < s.nr 19, a ≠ s.nr 74 + (expansionCycleRow s j).representative) → t.nm a = s.nm a) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ expansionNodeScratch → t.nr r = s.nr r := by
  let inv := ExpansionNodeScan s
  have first : inv 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, fun i hi => (Nat.not_lt_zero i hi).elim, fun _ _ => rfl, rfl, rfl⟩
    intro r safe
    have notIndex : r ≠ 7 := fun eq => safe (eq.symm ▸ (by decide : (7 : ℕ) ∈ expansionNodeScratch))
    exact Function.update_of_ne notIndex _ _
  have control (i : ℕ) (m : ArithmeticState) (h : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 19 = s.nr 19 :=
    ⟨h.entry, h.ready, h.index, h.fixed 19 (by decide)⟩
  have next (i : ℕ) (within : i < s.nr 19) (m : ArithmeticState) (h : inv i m) :
      ∃ t, BlockRuns publishExpansionNodeCell 12 m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    obtain ⟨t, run, ready, natural, real, rr, fixed⟩ :=
      publishExpansionNodeCell_spec h.entry h.ready ((h.fixed 9 (by decide)).trans one)
    have cycleRead (a : ℕ) (above : s.nr 18 ≤ a) : m.nm a = s.nm a := by
      apply h.kept a
      intro j earlier
      have bounded := inRange j (earlier.trans within)
      omega
    have row : expansionCycleRow m (m.nr 7) = expansionCycleRow s i := by
      rw [h.index]
      unfold expansionCycleRow matchingCycleChildAt
      rw [h.fixed 18 (by decide), cycleRead (s.nr 18 + 4 * i) (by omega),
        cycleRead (s.nr 18 + 4 * i + 1) (by omega), cycleRead (s.nr 18 + 4 * i + 2) (by omega),
        cycleRead (s.nr 18 + 4 * i + 3) (by omega)]
    have effect : t.nm = Function.update m.nm (s.nr 74 + (expansionCycleRow s i).representative)
        (expansionCycleRow s i).node := by rw [natural, h.fixed 74 (by decide), row]
    refine ⟨t, run, ready, rfl, ready, ?_, ?_, ?_, ?_, real.trans h.real, rr.trans h.realRegisters⟩
    · simp [fixed 7 (by decide), h.index, fixed 9 (by decide), h.fixed 9 (by decide), one]
    · intro r safe
      have outside : r ≠ 7 := fun eq => safe (eq.symm ▸ (by decide : (7 : ℕ) ∈ expansionNodeScratch))
      change Function.update t.nr 7 (t.nr 7 + t.nr 9) r = s.nr r
      rw [Function.update_of_ne outside]
      exact (fixed r (by simp [expansionNodeScratch] at safe ⊢; omega)).trans (h.fixed r safe)
    · intro j below
      change t.nm _ = _
      rw [effect]
      by_cases current : j = i
      · subst j
        exact Function.update_self _ _ _
      · have earlier : j < i := by omega
        have different : (expansionCycleRow s j).representative ≠ (expansionCycleRow s i).representative :=
          fun eq => current (distinct j (earlier.trans within) i within eq)
        rw [Function.update_of_ne (by omega)]
        exact h.records j earlier
    · intro address away
      change t.nm address = _
      rw [effect, Function.update_of_ne (away i (by omega))]
      exact h.kept address (fun j hj => away j (by omega))
  obtain ⟨_, final, run⟩ := countedLoopFromZero_correct 9 7 19 (s.nr 19) 12
    publishExpansionNodeCell inv (s := s) entry running first control next
  have steps : 1 + (s.nr 19 * (12 + 3) + 1) = 15 * s.nr 19 + 2 := by omega
  rw [steps] at run
  exact ⟨_, run, final.ready, final.records, final.kept, final.real, final.realRegisters, final.fixed⟩



theorem publishExpansionSplit_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (globalBelowScratch : s.nr 57 + s.nr 55 ≤ s.nr 79)
    (globalBelowRegistry : s.nr 57 + s.nr 55 ≤ s.nr 74) (registryBelowCycle : s.nr 74 + s.nr 55 ≤ s.nr 18)
    (inRange : ∀ i < s.nr 19, (expansionCycleRow s i).representative < s.nr 55)
    (distinct : ∀ i < s.nr 19, ∀ j < s.nr 19,
      (expansionCycleRow s i).representative = (expansionCycleRow s j).representative → i = j) :
    ∃ t, BlockRuns publishExpansionSplit (9 * s.nr 55 + 15 * s.nr 19 + 4) s t ∧ t.halted = false ∧
      (∀ v < s.nr 55, t.nm (s.nr 57 + v) =
        if s.nm (s.nr 79 + v) < s.nr 55 then s.nm (s.nr 79 + v) else s.nm (s.nr 57 + v)) ∧
      (∀ j < s.nr 19, t.nm (s.nr 74 + (expansionCycleRow s j).representative) = (expansionCycleRow s j).node) ∧
      (∀ a, (a < s.nr 57 ∨ s.nr 57 + s.nr 55 ≤ a) →
        (∀ j < s.nr 19, a ≠ s.nr 74 + (expansionCycleRow s j).representative) → t.nm a = s.nm a) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 7, 10, 15, 16, 17, 25] → t.nr r = s.nr r := by
  obtain ⟨m, first, live, natural, real, rr, fixed⟩ :=
    publishExpansionRepresentatives_spec entry running one globalBelowScratch
  let seed := {m with pc := 0}
  have memoryOutside (a : ℕ) (away : a < s.nr 57 ∨ s.nr 57 + s.nr 55 ≤ a) : m.nm a = s.nm a :=
    (congrFun natural a).trans (expandedRepresentativeMemory_outside s away)
  have sameRow (j : ℕ) : expansionCycleRow seed j = expansionCycleRow s j := by
    unfold expansionCycleRow matchingCycleChildAt
    change MatchingCycleChild.mk (m.nm (m.nr 18 + 4 * j)) (m.nm (m.nr 18 + 4 * j + 1))
      (m.nm (m.nr 18 + 4 * j + 2)) (m.nm (m.nr 18 + 4 * j + 3)) = _
    rw [fixed 18 (by decide), memoryOutside (s.nr 18 + 4 * j) (Or.inr (by omega)),
      memoryOutside (s.nr 18 + 4 * j + 1) (Or.inr (by omega)),
      memoryOutside (s.nr 18 + 4 * j + 2) (Or.inr (by omega)),
      memoryOutside (s.nr 18 + 4 * j + 3) (Or.inr (by omega))]
  have lengthEq : seed.nr 19 = s.nr 19 := fixed 19 (by decide)
  have sizeEq : seed.nr 55 = s.nr 55 := fixed 55 (by decide)
  have registryEq : seed.nr 74 = s.nr 74 := fixed 74 (by decide)
  obtain ⟨t, nodes, ready, records, kept, lastReal, lastRr, lastFixed⟩ := publishExpansionNodes_spec
    (s := seed) rfl live ((fixed 9 (by decide)).trans one)
    (by rw [sizeEq, registryEq, show seed.nr 18 = _ from fixed 18 (by decide)]; exact registryBelowCycle)
    (fun j hj => by rw [sameRow, sizeEq]; exact inRange j (lengthEq ▸ hj))
    (fun i hi j hj eq => distinct i (lengthEq ▸ hi) j (lengthEq ▸ hj) (by simpa only [sameRow] using eq))
  have time : (9 * s.nr 55 + 2) + (15 * seed.nr 19 + 2) = 9 * s.nr 55 + 15 * s.nr 19 + 4 := by
    rw [lengthEq]
    omega
  have composed := first.append nodes
  rw [time] at composed
  refine ⟨_, composed, ready, ?_, ?_, ?_, lastReal.trans real, lastRr.trans rr, ?_⟩
  · intro v bounded
    change t.nm (s.nr 57 + v) = _
    rw [kept _ (fun j _ => by rw [registryEq]; omega), natural]
    exact expandedRepresentativeMemory_at s bounded
  · intro j within
    change t.nm (s.nr 74 + (expansionCycleRow s j).representative) = (expansionCycleRow s j).node
    have word := records j (lengthEq.symm ▸ within)
    simpa only [registryEq, sameRow] using word
  · intro a away notWritten
    exact (kept a (fun j hj => by rw [registryEq, sameRow]; exact notWritten j (lengthEq ▸ hj))).trans (memoryOutside a away)
  · intro r untouched
    exact (lastFixed r (by simp [expansionNodeScratch] at untouched ⊢; omega)).trans
      (fixed r (by simp at untouched ⊢; omega))

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionRegistryRAM

/-! matching/AlternatingForestGrowPairs.lean -/
section RppSource_AlternatingForestGrowPairs
namespace VehicleRoutingSurvey.Routing



theorem AlternatingForestState.growPairs_preserves {α : Type*} [DecidableEq α]
    {state : AlternatingForestState α} {source x : α} (vertices : List α) (outside : x ∉ vertices) :
    let result := state.growPairs source vertices
    result.1.role x = state.role x ∧ result.1.depth x = state.depth x := by
  induction vertices using List.twoStepInduction generalizing state source with
  | nil => exact ⟨rfl, rfl⟩
  | singleton _ => exact ⟨rfl, rfl⟩
  | cons_cons inner outer rest ih _ =>
    simp only [List.mem_cons, not_or] at outside
    have unaffected := ih (state := state.grow source inner outer) (source := outer) outside.2.2
    simpa [growPairs, grow, outside.1, outside.2.1] using unaffected

theorem AlternatingForestState.growPairs_valid {α : Type*} [DecidableEq α]
    {state : AlternatingForestState α} {mate : α → Option α} {tight : α → α → Prop} {source : α}
    (valid : state.valid mate tight) (sourceOuter : ∃ parent, state.role source = .outer parent)
    (vertices : List α) (distinct : vertices.Nodup) (even : vertices.length % 2 = 0)
    (unlabelled : ∀ v ∈ vertices, state.role v = .unlabelled)
    (path : (source :: vertices).IsChain tight)
    (oldPairs : ∀ a b, s(a, b) ∈ alternatingEdges vertices → mate a = some b ∧ mate b = some a) :
    let result := state.growPairs source vertices
    result.1.valid mate tight ∧ (∃ parent, result.1.role result.2 = .outer parent) ∧
      result.1.depth result.2 = state.depth source + vertices.length ∧
      (source :: vertices).getLast? = some result.2 := by
  induction vertices using List.twoStepInduction generalizing state source with
  | nil => exact ⟨valid, sourceOuter, by simp [growPairs], rfl⟩
  | singleton a => simp at even
  | cons_cons inner outer rest ih _ =>
    obtain ⟨⟨different, noInner⟩, noOuter, restDistinct⟩ :
        (inner ≠ outer ∧ inner ∉ rest) ∧ outer ∉ rest ∧ rest.Nodup := by
      simpa only [List.nodup_cons, List.mem_cons, not_or] using distinct
    obtain ⟨parent, fromOuter⟩ := sourceOuter
    have incoming := List.isChain_cons_cons.mp path
    have pairPath := List.isChain_cons_cons.mp incoming.2
    have pairMates := oldPairs inner outer List.mem_cons_self
    let grown := state.grow source inner outer
    have grownValid : grown.valid mate tight := grow_valid valid fromOuter
      (unlabelled inner List.mem_cons_self) (unlabelled outer (List.mem_cons_of_mem _ List.mem_cons_self))
      different pairMates.1 pairMates.2 incoming.1 pairPath.1
    have grownOuter : ∃ p, grown.role outer = .outer p := ⟨some inner, by simp [grown, grow, different.symm]⟩
    have restEven : rest.length % 2 = 0 := by
      simp only [List.length_cons] at even
      omega
    have restDormant : ∀ v ∈ rest, grown.role v = .unlabelled := by
      intro v hv
      have notInner : v ≠ inner := fun eq => noInner (eq ▸ hv)
      have notOuter : v ≠ outer := fun eq => noOuter (eq ▸ hv)
      simpa [grown, grow, notInner, notOuter] using
        unlabelled v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv))
    have restPairs : ∀ a b, s(a, b) ∈ alternatingEdges rest → mate a = some b ∧ mate b = some a :=
      fun a b h => oldPairs a b (List.mem_cons_of_mem _ h)
    obtain ⟨newValid, newOuter, depthEq, endAt⟩ := ih (state := grown) (source := outer) grownValid
      grownOuter restDistinct restEven restDormant pairPath.2 restPairs
    change let result := grown.growPairs outer rest
      result.1.valid mate tight ∧ (∃ parent, result.1.role result.2 = .outer parent) ∧
        result.1.depth result.2 = state.depth source + (inner :: outer :: rest).length ∧
        (source :: inner :: outer :: rest).getLast? = some result.2
    refine ⟨newValid, newOuter, ?_, ?_⟩
    · have secondDepth : grown.depth outer = state.depth source + 2 := by
        simp [grown, grow, different.symm]
      rw [depthEq, secondDepth]
      simp only [List.length_cons]
      omega
    · simpa only [List.getLast?_cons_cons] using endAt

end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestGrowPairs

/-! matching/AlternatingForestExpand.lean -/
section RppSource_AlternatingForestExpand
namespace VehicleRoutingSurvey.Routing



private theorem shiftedForestDepth_strict (threshold extra : ℕ) : StrictMono (shiftedForestDepth threshold extra) := by
  intro a b earlier
  by_cases left : threshold ≤ a <;> by_cases right : threshold ≤ b <;>
    simp [shiftedForestDepth, left, right] <;> omega



private theorem AlternatingForestState.reserveDepths_valid {α : Type*}
    {state : AlternatingForestState α} {mate : α → Option α} {tight : α → α → Prop}
    (valid : state.valid mate tight) (threshold extra : ℕ) : (state.reserveDepths threshold extra).valid mate tight := by
  intro v
  have former := valid v
  try simp only [reserveDepths]
  cases role : state.role v with
  | unlabelled => trivial
  | outer p =>
    try rw [role] at former
    cases p with
    | none => exact former
    | some parent =>
      obtain ⟨inner, first, second, edge, earlier⟩ := former
      exact ⟨inner, first, second, edge, shiftedForestDepth_strict threshold extra earlier⟩
  | inner p =>
    try rw [role] at former
    obtain ⟨outer, unmatched, child, edge, earlier⟩ := former
    exact ⟨outer, unmatched, child, edge, shiftedForestDepth_strict threshold extra earlier⟩



private theorem AlternatingForestState.reattachInner_valid {α : Type*} [DecidableEq α]
    {state : AlternatingForestState α} {mate : α → Option α} {tight : α → α → Prop}
    (valid : state.valid mate tight) {base predecessor original : α}
    (baseInner : state.role base = .inner original) {previous : Option α}
    (predOuter : state.role predecessor = .outer previous) (predDepth : state.depth predecessor < state.depth base)
    (predUnmatched : mate base ≠ some predecessor) (edge : tight predecessor base) :
    (state.reattachInner base predecessor).valid mate tight := by
  let after := state.reattachInner base predecessor
  have keepOuter {x p} (outer : state.role x = .outer p) : after.role x = .outer p := by
    have different : x ≠ base := by
      intro equal
      have wrong := baseInner.symm.trans (equal ▸ outer)
      cases wrong
    simp [after, reattachInner, different, outer]
  have updated : after.role base = .inner predecessor := by simp [after, reattachInner]
  change after.valid mate tight
  intro v
  by_cases isBase : v = base
  · subst v
    rw [updated]
    have old := valid base
    rw [baseInner] at old
    obtain ⟨child, childMate, childOuter⟩ := old.2.2.1
    exact ⟨⟨previous, keepOuter predOuter⟩, predUnmatched,
      ⟨child, childMate, keepOuter childOuter⟩, edge, predDepth⟩
  have same : after.role v = state.role v := by simp [after, reattachInner, isBase]
  rw [same]
  have old := valid v
  cases role : state.role v with
  | unlabelled => trivial
  | outer p =>
    try rw [role] at old
    cases p with
    | none => exact old
    | some parent =>
      obtain ⟨⟨prior, inner⟩, first, second, tightEdge, earlier⟩ := old
      refine ⟨?_, first, second, tightEdge, earlier⟩
      by_cases isParent : parent = base
      · exact ⟨predecessor, isParent.symm ▸ updated⟩
      · exact ⟨prior, by simp [after, reattachInner, isParent, inner]⟩
  | inner p =>
    try rw [role] at old
    obtain ⟨⟨prior, outer⟩, notMate, ⟨child, childMate, childOuter⟩, tightEdge, earlier⟩ := old
    exact ⟨⟨prior, keepOuter outer⟩, notMate, ⟨child, childMate, keepOuter childOuter⟩, tightEdge, earlier⟩



theorem AlternatingForestState.expandAlong_valid {α : Type*} [DecidableEq α]
    {state : AlternatingForestState α} {mate : α → Option α} {tight : α → α → Prop}
    (valid : state.valid mate tight) {source base : α} (baseInner : state.role base = .inner source)
    (vertices : List α) (distinct : vertices.Nodup) (even : vertices.length % 2 = 0)
    (unlabelled : ∀ v ∈ vertices, state.role v = .unlabelled)
    (path : (source :: (vertices ++ [base])).IsChain tight)
    (oldPairs : ∀ a b, s(a, b) ∈ alternatingEdges vertices → mate a = some b ∧ mate b = some a) :
    (state.expandAlong source base vertices).valid mate tight := by
  have original := valid base
  rw [baseInner] at original
  obtain ⟨sourceOuter, oldUnmatched, ⟨oldChild, oldMate, oldChildOuter⟩, _, oldDepth⟩ := original
  have avoidsBase : base ∉ vertices := by
    intro member
    have impossible := baseInner.symm.trans (unlabelled base member)
    cases impossible
  let raised := state.reserveDepths (state.depth base) vertices.length
  let grown := raised.growPairs source vertices
  have longer : ((source :: vertices) ++ [base]).IsChain tight := by simpa only [List.cons_append] using path
  obtain ⟨grownValid, ⟨parent, grownOuter⟩, grownDepth, grownLast⟩ :=
    growPairs_valid (reserveDepths_valid valid (state.depth base) vertices.length) sourceOuter vertices distinct even
      unlabelled longer.left_of_append oldPairs
  have baseStill : grown.1.role base = .inner source ∧ grown.1.depth base = raised.depth base :=
    ⟨(growPairs_preserves (state := raised) (source := source) vertices avoidsBase).1.trans baseInner,
      (growPairs_preserves (state := raised) (source := source) vertices avoidsBase).2⟩
  change (grown.1.reattachInner base grown.2).valid mate tight
  refine reattachInner_valid grownValid baseStill.1 grownOuter ?_ ?_ ?_
  · change grown.1.depth grown.2 < grown.1.depth base
    have depthUpdate : grown.1.depth grown.2 = raised.depth source + vertices.length := grownDepth
    rw [baseStill.2, depthUpdate]
    simpa [raised, reserveDepths, shiftedForestDepth, not_le_of_gt oldDepth] using
      Nat.add_lt_add_right oldDepth vertices.length
  · intro opposite
    have member : grown.2 ∈ source :: vertices := List.mem_of_getLast? grownLast
    rcases List.mem_cons.mp member with old | new
    · exact oldUnmatched (old ▸ opposite)
    · have equal : oldChild = grown.2 := Option.some.inj (oldMate.symm.trans opposite)
      have different := oldChildOuter.symm.trans (equal.symm ▸ unlabelled grown.2 new)
      cases different
  · have chosenLast : (source :: vertices).getLast? = some grown.2 := grownLast
    exact (List.isChain_append.mp longer).2.2 grown.2 (by simp [chosenLast]) base (by simp)

end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestExpand

/-! matching/ExpansionDepthRAM.lean -/
section RppSource_ExpansionDepthRAM
open private readExpansionDepths VehicleRoutingSurvey.Routing.readExpansionDepths from Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
open private scanExpansionDepths VehicleRoutingSurvey.Routing.scanExpansionDepths from Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
open private shiftExpansionDepthCell VehicleRoutingSurvey.Routing.shiftExpansionDepthCell from Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
namespace VehicleRoutingSurvey.Routing

/-- Reserve space in the depth order above the old blossom base. -/
def shiftedExpansionDepths (memory : ℕ → ℕ) (depths threshold extra processed : ℕ) : ℕ → ℕ :=
  fun address => if depths ≤ address ∧ address < depths + processed then
    memory address + (if threshold ≤ memory address then extra else 0)
  else memory address





private theorem readExpansionDepths_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) :
    ∃ t, BlockRuns readExpansionDepths 3 s t ∧ t.halted = false ∧
      t.nr 11 = s.nm (s.nr 53 + s.nr 97) ∧ t.nr 12 = s.nr 95 + s.nr 95 ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [10, 11, 12] → t.nr r = s.nr r := by
  let t := (arithmeticStep readExpansionDepths)^[3] s
  have ready : t.halted = false := by
    simp [t, readExpansionDepths, arithmeticStep, Function.iterate_succ_apply', entry, running]
  have exit : t.pc = readExpansionDepths.length := by
    simp [t, readExpansionDepths, arithmeticStep, Function.iterate_succ_apply', entry, running]
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
  | intro r fixed
    apply arithmeticRun_keeps_register
    simp [readExpansionDepths, naturalDestination] at fixed ⊢ <;> omega
  | simp [t, readExpansionDepths, arithmeticStep, Function.iterate_succ_apply', entry, running]

private theorem shiftExpansionDepthCell_spec {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    let address := s.nr 53 + s.nr 15
    ∃ t, BlockRuns shiftExpansionDepthCell 6 s t ∧ t.halted = false ∧
      t.nm = Function.update s.nm address
        (s.nm address + (if s.nr 11 ≤ s.nm address then s.nr 12 else 0)) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ≠ 10 → r ≠ 16 → t.nr r = s.nr r := by
  intro address
  let t := (arithmeticStep shiftExpansionDepthCell)^[6] s
  have ready : t.halted = false := by
    by_cases raises : s.nr 11 ≤ s.nm address <;>
      simp [t, address, shiftExpansionDepthCell, arithmeticStep, Function.iterate_succ_apply', entry, running, raises]
  have exit : t.pc = shiftExpansionDepthCell.length := by
    by_cases raises : s.nr 11 ≤ s.nm address <;>
      simp [t, address, shiftExpansionDepthCell, arithmeticStep, Function.iterate_succ_apply', entry, running, raises]
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_⟩
  · by_cases raises : s.nr 11 ≤ s.nm address <;>
      simp [t, address, shiftExpansionDepthCell, arithmeticStep, Function.iterate_succ_apply', entry, running,
        raises, Function.update_eq_self]
  · by_cases raises : s.nr 11 ≤ s.nm address <;>
      simp [t, address, shiftExpansionDepthCell, arithmeticStep, Function.iterate_succ_apply', entry, running, raises]
  · by_cases raises : s.nr 11 ≤ s.nm address <;>
      simp [t, address, shiftExpansionDepthCell, arithmeticStep, Function.iterate_succ_apply', entry, running, raises]
  · intro r except10 except16
    by_cases raises : s.nr 11 ≤ s.nm address <;>
      simp [t, address, shiftExpansionDepthCell, arithmeticStep, Function.iterate_succ_apply', entry, running,
        raises, Function.update_of_ne except10, Function.update_of_ne except16]

private theorem shiftedExpansionDepths_step (memory : ℕ → ℕ) (depths threshold extra i : ℕ) :
    let prefixMemory := shiftedExpansionDepths memory depths threshold extra i
    let address := depths + i
    Function.update prefixMemory address
      (prefixMemory address + (if threshold ≤ prefixMemory address then extra else 0)) =
      shiftedExpansionDepths memory depths threshold extra (i + 1) := by
  intro prefixMemory address
  have fresh : prefixMemory address = memory address := by
    simp [prefixMemory, address, shiftedExpansionDepths]
  funext cell
  by_cases current : cell = address
  · subst cell
    rw [Function.update_self, fresh]
    have inNew : depths ≤ address ∧ address < depths + (i + 1) := by dsimp [address]; omega
    simp [shiftedExpansionDepths, inNew]
  · rw [Function.update_of_ne current]
    have same : (depths ≤ cell ∧ cell < depths + i) ↔ (depths ≤ cell ∧ cell < depths + (i + 1)) := by
      dsimp [address] at current
      omega
    simp only [prefixMemory, shiftedExpansionDepths, same]





private structure ExpansionDepthScanState (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 15 = i
  fixed : ∀ r, r ∉ [10, 15, 16] → s.nr r = initial.nr r
  natural : s.nm = shiftedExpansionDepths initial.nm (initial.nr 53) (initial.nr 11) (initial.nr 12) i
  real : s.rm = initial.rm
  realRegisters : s.rr = initial.rr

private theorem scanExpansionDepths_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns scanExpansionDepths (9 * s.nr 55 + 2) s t ∧ t.halted = false ∧
      t.nm = shiftedExpansionDepths s.nm (s.nr 53) (s.nr 11) (s.nr 12) (s.nr 55) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [10, 15, 16] → t.nr r = s.nr r := by
  let inv := ExpansionDepthScanState s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 15 0} := by
    refine ⟨rfl, running, by simp, ?_, ?_, rfl, rfl⟩
    · intro r fixed
      have notIndex : r ≠ 15 := fun h => fixed (h.symm ▸ (by decide : (15 : ℕ) ∈ [10, 15, 16]))
      exact Function.update_of_ne notIndex _ _
    · funext address
      change s.nm address = shiftedExpansionDepths s.nm (s.nr 53) (s.nr 11) (s.nr 12) 0 address
      rw [shiftedExpansionDepths, if_neg (by omega)]
  have control (i : ℕ) (m : ArithmeticState) (state : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 15 = i ∧ m.nr 55 = s.nr 55 :=
    ⟨state.entry, state.running, state.index, state.fixed 55 (by decide)⟩
  have iterate (i : ℕ) (_ : i < s.nr 55) (m : ArithmeticState) (state : inv i m) :
      ∃ t, BlockRuns shiftExpansionDepthCell 6 m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 15 (t.nr 15 + t.nr 9)} := by
    obtain ⟨t, run, ready, memory, real, realRegisters, fixed⟩ :=
      shiftExpansionDepthCell_spec state.entry state.running
    refine ⟨t, run, ready, rfl, ready, ?_, ?_, ?_, real.trans state.real,
      realRegisters.trans state.realRegisters⟩
    · simp [fixed 15 (by decide) (by decide), fixed 9 (by decide) (by decide),
        state.index, state.fixed 9 (by decide), one]
    · intro r keep
      have outside (x : ℕ) (used : x ∈ ([10, 15, 16] : List ℕ)) : r ≠ x :=
        fun same => keep (same.symm ▸ used)
      change Function.update t.nr 15 (t.nr 15 + t.nr 9) r = s.nr r
      rw [Function.update_of_ne (outside 15 (by decide))]
      exact (fixed r (outside 10 (by decide)) (outside 16 (by decide))).trans (state.fixed r keep)
    · change t.nm = _
      rw [memory, state.natural, state.fixed 53 (by decide), state.index,
        state.fixed 11 (by decide), state.fixed 12 (by decide)]
      exact shiftedExpansionDepths_step _ _ _ _ _
  obtain ⟨_, complete, run⟩ := countedLoopFromZero_correct 9 15 55 (s.nr 55) 6
    shiftExpansionDepthCell inv (s := s) entry running initial control iterate
  have steps : 1 + (s.nr 55 * (6 + 3) + 1) = 9 * s.nr 55 + 2 := by omega
  rw [steps] at run
  exact ⟨_, run, complete.running, complete.natural, complete.real, complete.realRegisters, complete.fixed⟩

theorem reserveExpansionDepthsBlock_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns reserveExpansionDepthsBlock (9 * s.nr 55 + 5) s t ∧ t.halted = false ∧
      t.nm = shiftedExpansionDepths s.nm (s.nr 53) (s.nm (s.nr 53 + s.nr 97)) (s.nr 95 + s.nr 95) (s.nr 55) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [10, 11, 12, 15, 16] → t.nr r = s.nr r := by
  obtain ⟨r, reads, readReady, threshold, extra, natural, real, rr, fixed⟩ :=
    readExpansionDepths_spec entry running
  let start := {r with pc := 0}
  obtain ⟨t, scan, ready, shifted, tReal, tRr, tFixed⟩ :=
    scanExpansionDepths_spec (s := start) rfl readReady ((fixed 9 (by decide)).trans one)
  have dim : start.nr 55 = s.nr 55 := fixed 55 (by decide)
  have sum : 3 + (9 * start.nr 55 + 2) = 9 * s.nr 55 + 5 := by rw [dim]; omega
  have finished := reads.append scan
  rw [sum] at finished
  refine ⟨_, finished, ready, ?_, tReal.trans real, tRr.trans rr, ?_⟩
  · change t.nm = _
    rw [shifted, show start.nm = s.nm from natural, dim, show start.nr 53 = s.nr 53 from fixed 53 (by decide),
      show start.nr 11 = _ from threshold, show start.nr 12 = _ from extra]
  · intro reg keep
    exact (tFixed reg (by simp at keep ⊢; omega)).trans (fixed reg (by simp at keep ⊢; omega))

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionDepthRAM

/-! matching/ExpansionPathRAM.lean -/
section RppSource_ExpansionPathRAM
open private readExpansionPair VehicleRoutingSurvey.Routing.readExpansionPair from Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
open private writeExpansionPair VehicleRoutingSurvey.Routing.writeExpansionPair from Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
namespace VehicleRoutingSurvey.Routing

/-- A child representative and the original endpoints of its new parent edge. -/
structure ExpansionPathRecord (k : ℕ) where
  vertex : Fin k
  edge : Fin k × Fin k

def ExpansionPathRecord.witness {k : ℕ} (record : ExpansionPathRecord k) : ℕ × ℕ :=
  (record.edge.1.val, record.edge.2.val)

def ExpansionPathMemory {k : ℕ} (memory : ℕ → ℕ) (address : ℕ) : List (ExpansionPathRecord k) → Prop
  | [] => True
  | record :: rest => memory address = record.vertex.val ∧
      memory (address + 1) = record.witness.1 ∧ memory (address + 2) = record.witness.2 ∧
      ExpansionPathMemory memory (address + 3) rest

theorem ExpansionPathMemory.preserved {k : ℕ} {old new : ℕ → ℕ} {address : ℕ}
    {records : List (ExpansionPathRecord k)} (encoded : ExpansionPathMemory old address records)
    (keeps : ∀ cell ≥ address, new cell = old cell) : ExpansionPathMemory new address records := by
  induction records generalizing address with
  | nil => trivial
  | cons record rest ih =>
    obtain ⟨vertex, first, second, tail⟩ := encoded
    exact ⟨(keeps _ le_rfl).trans vertex, (keeps _ (by omega)).trans first,
      (keeps _ (by omega)).trans second, ih tail (fun cell after => keeps cell (by omega))⟩





private theorem readExpansionPair_spec {k : ℕ} {s : ArithmeticState}
    {inner outer : ExpansionPathRecord k} {rest : List (ExpansionPathRecord k)}
    (encoded : ExpansionPathMemory s.nm (s.nr 23) (inner :: outer :: rest))
    (one : s.nr 9 = 1) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns readExpansionPair 12 s t ∧ t.halted = false ∧
      t.nr 1 = inner.vertex.val ∧ t.nr 2 = outer.vertex.val ∧
      t.nr 17 = inner.witness.1 ∧ t.nr 18 = inner.witness.2 ∧
      t.nr 19 = outer.witness.1 ∧ t.nr 22 = outer.witness.2 ∧ t.nr 23 = s.nr 23 + 6 ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [1, 2, 17, 18, 19, 22, 23] → t.nr r = s.nr r := by
  obtain ⟨inVertex, inFirst, inSecond, outVertex, outFirst, outSecond, _⟩ := encoded
  have words : s.nm (s.nr 23 + 3) = outer.vertex.val ∧
      s.nm (s.nr 23 + 4) = outer.witness.1 ∧ s.nm (s.nr 23 + 5) = outer.witness.2 := by
    exact ⟨outVertex, by simpa [Nat.add_assoc] using outFirst, by simpa [Nat.add_assoc] using outSecond⟩
  let t := (arithmeticStep readExpansionPair)^[12] s
  have ready : t.halted = false := by
    simp [t, readExpansionPair, arithmeticStep, Function.iterate_succ_apply', entry, running]
  have exit : t.pc = readExpansionPair.length := by
    simp [t, readExpansionPair, arithmeticStep, Function.iterate_succ_apply', entry, running]
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
  | intro r fixed
    apply arithmeticRun_keeps_register
    simp [readExpansionPair, naturalDestination] at fixed ⊢ <;> omega
  | simp [t, readExpansionPair, arithmeticStep, Function.iterate_succ_apply', entry, running, one,
      Nat.add_assoc, inVertex, inFirst, inSecond, words.1, words.2.1, words.2.2]

private theorem writeExpansionPair_spec {s : ArithmeticState} (one : s.nr 9 = 1)
    (zero : s.nr 14 = 0) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns writeExpansionPair 11 s t ∧ t.halted = false ∧ t.nr 0 = s.nr 2 ∧
      t.nm = writeMatchingForestWitness (writeMatchingForestWitness s.nm (s.nr 90) (s.nr 1) (s.nr 17, s.nr 18))
        (s.nr 90) (s.nr 2) (s.nr 19, s.nr 22) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ≠ 0 → r ≠ 6 → t.nr r = s.nr r := by
  let t := (arithmeticStep writeExpansionPair)^[11] s
  have ready : t.halted = false := by
    simp [t, writeExpansionPair, arithmeticStep, Function.iterate_succ_apply', entry, running]
  have exit : t.pc = writeExpansionPair.length := by
    simp [t, writeExpansionPair, arithmeticStep, Function.iterate_succ_apply', entry, running]
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
  | intro r away0 away6
    apply arithmeticRun_keeps_register
    simp [writeExpansionPair, naturalDestination, away0.symm, away6.symm]
  | simp [t, writeExpansionPair, arithmeticStep, writeMatchingForestWitness, forestWitnessAddress,
      Function.iterate_succ_apply', entry, running, one, zero]

theorem expansionGrowMemory_preserves {k : ℕ} {s : ArithmeticState} {forestBase : ℕ}
    (roleBase : s.nr 3 = forestBase) (parentBase : s.nr 4 = forestBase + k)
    (depthBase : s.nr 5 = forestBase + k + k) (inner : s.nr 1 < k) (outer : s.nr 2 < k)
    {address : ℕ} (outside : address < forestBase ∨ forestBase + k + k + k ≤ address) :
    alternatingForestGrownMemory s address = s.nm address := by
  simp (disch := omega) [alternatingForestGrownMemory, roleBase, parentBase, depthBase, Function.update_of_ne]

theorem vertexWitnessMemory_preserves {k base child address : ℕ} {memory : ℕ → ℕ} {edge : ℕ × ℕ}
    (within : child < k) (outside : address < base ∨ base + k + k ≤ address) :
    writeMatchingForestWitness memory base child edge address = memory address := by
  simp (disch := omega) [writeMatchingForestWitness, forestWitnessAddress, Function.update_of_ne]



theorem expansionGrowPairBlock_spec {k : ℕ} {forest : AlternatingForestState (Fin k)}
    {forestBase witnessBase : ℕ} {s : ArithmeticState} {source : Fin k}
    {inner outer : ExpansionPathRecord k} {rest : List (ExpansionPathRecord k)}
    (encoding : AlternatingForestMemory forest forestBase s.nm)
    (path : ExpansionPathMemory s.nm (s.nr 23) (inner :: outer :: rest))
    (different : inner.vertex ≠ outer.vertex) (sourceAt : s.nr 0 = source.val)
    (roleBase : s.nr 3 = forestBase) (parentBase : s.nr 4 = forestBase + k)
    (depthBase : s.nr 5 = forestBase + k + k) (witnessAt : s.nr 90 = witnessBase)
    (gap : forestBase + k + k + k ≤ witnessBase) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns expansionGrowPairBlock 41 s t ∧ t.halted = false ∧
      AlternatingForestMemory (forest.grow source inner.vertex outer.vertex) forestBase t.nm ∧
      t.nr 0 = outer.vertex.val ∧ t.nr 23 = s.nr 23 + 6 ∧
      matchingForestWitnessAt t.nm witnessBase inner.vertex.val = inner.witness ∧
      matchingForestWitnessAt t.nm witnessBase outer.vertex.val = outer.witness ∧
      (∀ v : Fin k, v ≠ inner.vertex → v ≠ outer.vertex → matchingForestWitnessAt t.nm witnessBase v.val =
        matchingForestWitnessAt s.nm witnessBase v.val) ∧
      (∀ a, (a < forestBase ∨ forestBase + k + k + k ≤ a) →
        (a < witnessBase ∨ witnessBase + k + k ≤ a) → t.nm a = s.nm a) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 1, 2, 6, 7, 8, 17, 18, 19, 22, 23] → t.nr r = s.nr r := by
  obtain ⟨r, loads, loadReady, innerAt, outerAt, innerA, innerB, outerA, outerB, cursor,
    loadNm, loadRm, loadRr, loadFixed⟩ := readExpansionPair_spec path one entry running
  let grow := {r with pc := 0}
  let grown := (arithmeticStep alternatingForestGrowBlock)^[18] grow
  obtain ⟨growth, growNm, growRm, growRr, keptArgs⟩ := alternatingForestGrowBlock_spec grow rfl loadReady
  have growFixed (r : ℕ) (keep : r ∉ ([6, 7, 8] : List ℕ)) : grown.nr r = grow.nr r := by
    by_cases argument : r < 6
    · exact keptArgs r argument
    · apply arithmeticRun_keeps_register
      simp [alternatingForestGrowBlock, naturalDestination] at keep ⊢ <;> omega
  have growReady : grown.halted = false :=
    no_halt_from_running (s := grow) loadReady growth.inside (by simp [alternatingForestGrowBlock])
  have roleAt : grow.nr 3 = forestBase := (loadFixed 3 (by decide)).trans roleBase
  have parentsAt : grow.nr 4 = forestBase + k := (loadFixed 4 (by decide)).trans parentBase
  have depthsAt : grow.nr 5 = forestBase + k + k := (loadFixed 5 (by decide)).trans depthBase
  have liveForest : AlternatingForestMemory forest forestBase grow.nm := loadNm.symm ▸ encoding
  have grownForest : AlternatingForestMemory (forest.grow source inner.vertex outer.vertex) forestBase grown.nm :=
    growNm.symm ▸ alternatingForestGrownMemory_encodes liveForest ((loadFixed 0 (by decide)).trans sourceAt)
      innerAt outerAt roleAt parentsAt depthsAt different
  have grownOutside (a : ℕ) (outside : a < forestBase ∨ forestBase + k + k + k ≤ a) : grown.nm a = s.nm a := by
    rw [growNm, expansionGrowMemory_preserves roleAt parentsAt depthsAt
      (innerAt.symm ▸ inner.vertex.isLt) (outerAt.symm ▸ outer.vertex.isLt) outside]
    exact congrFun loadNm a
  let write := {grown with pc := 0}
  obtain ⟨t, writes, ready, finalSource, writeNm, writeRm, writeRr, writeFixed⟩ :=
    writeExpansionPair_spec (s := write)
      ((growFixed 9 (by decide)).trans ((loadFixed 9 (by decide)).trans one))
      ((growFixed 14 (by decide)).trans ((loadFixed 14 (by decide)).trans zero)) rfl growReady
  have witnesses : t.nm = writeMatchingForestWitness
      (writeMatchingForestWitness grown.nm witnessBase inner.vertex.val inner.witness)
      witnessBase outer.vertex.val outer.witness := by
    rw [writeNm]
    change writeMatchingForestWitness (writeMatchingForestWitness grown.nm (grown.nr 90) (grown.nr 1)
      (grown.nr 17, grown.nr 18)) (grown.nr 90) (grown.nr 2) (grown.nr 19, grown.nr 22) = _
    rw [(growFixed 90 (by decide)).trans ((loadFixed 90 (by decide)).trans witnessAt),
      (growFixed 1 (by decide)).trans innerAt, (growFixed 2 (by decide)).trans outerAt,
      (growFixed 17 (by decide)).trans innerA, (growFixed 18 (by decide)).trans innerB,
      (growFixed 19 (by decide)).trans outerA, (growFixed 22 (by decide)).trans outerB] <;> rfl
  have preservedWitnessWrites (a : ℕ) (outside : a < witnessBase ∨ witnessBase + k + k ≤ a) :
      t.nm a = grown.nm a := by
    rw [witnesses, vertexWitnessMemory_preserves outer.vertex.isLt outside,
      vertexWitnessMemory_preserves inner.vertex.isLt outside]
  have finalForest : AlternatingForestMemory (forest.grow source inner.vertex outer.vertex) forestBase t.nm := by
    intro v
    have inBounds := v.isLt
    exact ⟨(preservedWitnessWrites (forestBase + v.val) (Or.inl (by omega))).trans (grownForest v).1,
      (preservedWitnessWrites (forestBase + k + v.val) (Or.inl (by omega))).trans (grownForest v).2.1,
      (preservedWitnessWrites (forestBase + k + k + v.val) (Or.inl (by omega))).trans (grownForest v).2.2⟩
  have sameWitness (v : Fin k) : matchingForestWitnessAt grown.nm witnessBase v.val =
      matchingForestWitnessAt s.nm witnessBase v.val := by
    unfold matchingForestWitnessAt
    dsimp only
    rw [grownOutside (forestWitnessAddress witnessBase v.val) (Or.inr (by unfold forestWitnessAddress; omega)),
      grownOutside (forestWitnessAddress witnessBase v.val + 1) (Or.inr (by unfold forestWitnessAddress; omega))]
  have event := loads.append (growth.append writes)
  refine ⟨_, event, ready, finalForest, finalSource.trans ((growFixed 2 (by decide)).trans outerAt),
    (writeFixed 23 (by decide) (by decide)).trans ((growFixed 23 (by decide)).trans cursor), ?_, ?_, ?_,
    fun a outsideForest outsideWitness => (preservedWitnessWrites a outsideWitness).trans (grownOutside a outsideForest),
    (writeRm.trans growRm).trans loadRm, (writeRr.trans growRr).trans loadRr, ?_⟩
  · change matchingForestWitnessAt t.nm _ _ = _
    rw [witnesses, matchingForestWitnessAt_write_other _ _ _ _ _ (fun eq => different (Fin.ext eq)),
      matchingForestWitnessAt_write_same]
  · change matchingForestWitnessAt t.nm _ _ = _
    rw [witnesses, matchingForestWitnessAt_write_same]
  · intro v awayInner awayOuter
    change matchingForestWitnessAt t.nm _ _ = _
    rw [witnesses, matchingForestWitnessAt_write_other _ _ _ _ _ (fun eq => awayOuter (Fin.ext eq)),
      matchingForestWitnessAt_write_other _ _ _ _ _ (fun eq => awayInner (Fin.ext eq))]
    exact sameWitness v
  · intro r untouched
    exact ((writeFixed r (by simp at untouched ⊢; omega) (by simp at untouched ⊢; omega)).trans
      (growFixed r (by simp at untouched ⊢; omega))).trans (loadFixed r (by simp at untouched ⊢; omega))

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionPathRAM

/-! matching/ExpansionPairLoop.lean -/
section RppSource_ExpansionPairLoop
namespace VehicleRoutingSurvey.Routing



def expansionPairScratch : List ℕ := [0, 1, 2, 6, 7, 8, 15, 17, 18, 19, 22, 23]

private structure ExpansionPairState {k : ℕ} (initial : ArithmeticState) (forestBase witnessBase : ℕ)
    (initialForest : AlternatingForestState (Fin k)) (initialSource : Fin k)
    (records : List (ExpansionPathRecord k)) (lastRecord : ExpansionPathRecord k)
    (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  ready : s.halted = false
  index : s.nr 15 = i
  fixed : ∀ r, r ∉ expansionPairScratch → s.nr r = initial.nr r
  keeps : ∀ a, (a < forestBase ∨ forestBase + k + k + k ≤ a) →
    (a < witnessBase ∨ witnessBase + k + k ≤ a) → s.nm a = initial.nm a
  real : s.rm = initial.rm
  realRegisters : s.rr = initial.rr
  path : ∃ (done pending : List (ExpansionPathRecord k)) (forest : AlternatingForestState (Fin k)) (source : Fin k),
    records = done ++ pending ∧ done.length = i + i ∧ s.nr 0 = source.val ∧
    s.nr 23 = initial.nr 23 + 3 * done.length ∧ AlternatingForestMemory forest forestBase s.nm ∧
    forest.growPairs source (pending.map ExpansionPathRecord.vertex) =
      initialForest.growPairs initialSource (records.map ExpansionPathRecord.vertex) ∧
    ExpansionPathMemory s.nm (s.nr 23) (pending ++ [lastRecord]) ∧
    (∀ record ∈ done, matchingForestWitnessAt s.nm witnessBase record.vertex.val = record.witness) ∧
    ∀ v : Fin k, v ∉ done.map ExpansionPathRecord.vertex →
      matchingForestWitnessAt s.nm witnessBase v.val = matchingForestWitnessAt initial.nm witnessBase v.val

/-- Grow the path pairs in order. The cursor ends at the original base's
record, and every other parent witness outside the selected path is retained. -/
theorem expandForestPairsBlock_spec {k : ℕ} {s : ArithmeticState} {forestBase witnessBase : ℕ}
    {forest : AlternatingForestState (Fin k)} {source : Fin k}
    {records : List (ExpansionPathRecord k)} {lastRecord : ExpansionPathRecord k}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (sourceAt : s.nr 0 = source.val) (rolesAt : s.nr 3 = forestBase)
    (parentsAt : s.nr 4 = forestBase + k) (depthsAt : s.nr 5 = forestBase + k + k)
    (witnessAt : s.nr 90 = witnessBase) (forestGap : forestBase + k + k + k ≤ witnessBase)
    (pathGap : witnessBase + k + k ≤ s.nr 23)
    (length : records.length = s.nr 95 + s.nr 95)
    (distinct : (records.map ExpansionPathRecord.vertex).Nodup)
    (encoding : AlternatingForestMemory forest forestBase s.nm)
    (path : ExpansionPathMemory s.nm (s.nr 23) (records ++ [lastRecord])) :
    let grown := forest.growPairs source (records.map ExpansionPathRecord.vertex)
    ∃ t, BlockRuns expandForestPairsBlock (44 * s.nr 95 + 2) s t ∧ t.halted = false ∧
      AlternatingForestMemory grown.1 forestBase t.nm ∧ t.nr 0 = grown.2.val ∧
      t.nr 23 = s.nr 23 + 3 * records.length ∧ ExpansionPathMemory t.nm (t.nr 23) [lastRecord] ∧
      (∀ record ∈ records, matchingForestWitnessAt t.nm witnessBase record.vertex.val = record.witness) ∧
      (∀ v : Fin k, v ∉ records.map ExpansionPathRecord.vertex →
        matchingForestWitnessAt t.nm witnessBase v.val = matchingForestWitnessAt s.nm witnessBase v.val) ∧
      (∀ a, (a < forestBase ∨ forestBase + k + k + k ≤ a) →
        (a < witnessBase ∨ witnessBase + k + k ≤ a) → t.nm a = s.nm a) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ expansionPairScratch → t.nr r = s.nr r := by
  intro grown
  let inv := ExpansionPairState s forestBase witnessBase forest source records lastRecord
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 15 0} := by
    refine ⟨rfl, running, by simp, ?_, fun _ _ _ => rfl, rfl, rfl,
      [], records, forest, source, by simp, rfl, ?_, ?_, encoding, rfl, ?_, ?_, fun _ _ => rfl⟩
    · intro r keep
      have different : r ≠ 15 := fun eq => keep (eq.symm ▸ (by decide : (15 : ℕ) ∈ expansionPairScratch))
      exact Function.update_of_ne different _ _
    · simpa using sourceAt
    · simp
    · simpa using path
    · simp
  have control (i : ℕ) (m : ArithmeticState) (state : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 15 = i ∧ m.nr 95 = s.nr 95 :=
    ⟨state.entry, state.ready, state.index, state.fixed 95 (by decide)⟩
  have iterate (i : ℕ) (less : i < s.nr 95) (m : ArithmeticState) (state : inv i m) :
      ∃ t, BlockRuns expansionGrowPairBlock 41 m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 15 (t.nr 15 + t.nr 9)} := by
    obtain ⟨done, pending, oldForest, currentSource, split, doneLength, fromAt, cursor, oldEncoding, agrees,
      oldPath, earlier, untouched⟩ := state.path
    have pendingSize : 2 ≤ pending.length := by
      have sum := congrArg List.length split
      simp only [List.length_append] at sum
      omega
    obtain ⟨inner, pending, rfl⟩ := List.exists_cons_of_ne_nil (l := pending)
      (fun empty => by simp [empty] at pendingSize)
    obtain ⟨outer, rest, rfl⟩ := List.exists_cons_of_ne_nil (l := pending)
      (fun empty => by simp [empty] at pendingSize)
    have ordered : (done.map ExpansionPathRecord.vertex ++
        inner.vertex :: outer.vertex :: rest.map ExpansionPathRecord.vertex).Nodup := by
      simpa only [split, List.map_append, List.map_cons] using distinct
    obtain ⟨_, laterUnique, separated⟩ := List.nodup_append.mp ordered
    have different : inner.vertex ≠ outer.vertex := by
      intro equal
      exact (List.nodup_cons.mp laterUnique).1 (by simp [equal])
    obtain ⟨t, step, ready, stepForest, nextSource, stepCursor, innerWitness, outerWitness, keptWitness,
      keeps, real, realRegisters, fixed⟩ :=
      expansionGrowPairBlock_spec oldEncoding oldPath different fromAt
        ((state.fixed 3 (by decide)).trans rolesAt) ((state.fixed 4 (by decide)).trans parentsAt)
        ((state.fixed 5 (by decide)).trans depthsAt) ((state.fixed 90 (by decide)).trans witnessAt)
        forestGap ((state.fixed 9 (by decide)).trans one) ((state.fixed 14 (by decide)).trans zero)
        state.entry state.ready
    have newRecords : ExpansionPathMemory t.nm (t.nr 23) (rest ++ [lastRecord]) := by
      rw [stepCursor]
      have tail : ExpansionPathMemory m.nm (m.nr 23 + 6) (rest ++ [lastRecord]) := oldPath.2.2.2.2.2.2
      apply tail.preserved
      intro a after
      have enough : witnessBase + k + k ≤ a := by omega
      exact keeps a (Or.inr (by omega)) (Or.inr enough)
    refine ⟨t, step, ready, rfl, ready, ?_, ?_, fun a f w => (keeps a f w).trans (state.keeps a f w),
      real.trans state.real, realRegisters.trans state.realRegisters, ?_⟩
    · simp [fixed 15 (by decide), fixed 9 (by decide), state.index, state.fixed 9 (by decide), one]
    · intro r keep
      have noIndex : r ≠ 15 := fun eq => keep (eq.symm ▸ (by decide : (15 : ℕ) ∈ expansionPairScratch))
      change Function.update t.nr 15 (t.nr 15 + t.nr 9) r = s.nr r
      rw [Function.update_of_ne noIndex]
      exact (fixed r (by simp [expansionPairScratch] at keep ⊢; omega)).trans (state.fixed r keep)
    · refine ⟨done ++ [inner, outer], rest, oldForest.grow currentSource inner.vertex outer.vertex, outer.vertex,
        ?_, ?_, ?_, ?_, stepForest, agrees, newRecords, ?_, ?_⟩
      · simpa only [List.append_assoc, List.cons_append, List.nil_append] using split
      · simp [doneLength] <;> omega
      · simpa using nextSource
      · change t.nr 23 = _
        rw [stepCursor, cursor]
        simp <;> omega
      · intro record member
        change matchingForestWitnessAt t.nm witnessBase record.vertex.val = record.witness
        rcases List.mem_append.mp member with past | pair
        · have previous : record.vertex ∈ done.map ExpansionPathRecord.vertex := List.mem_map_of_mem past
          exact (keptWitness record.vertex (separated _ previous _ (by simp))
            (separated _ previous _ (by simp))).trans (earlier record past)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at pair
          rcases pair with rfl | rfl
          · exact innerWitness
          · exact outerWitness
      · intro v outside
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false, not_or] at outside
        exact (keptWitness v outside.2.1 outside.2.2).trans (untouched v outside.1)
  obtain ⟨last, complete, run⟩ := countedLoopFromZero_correct 9 15 95 (s.nr 95) 41
    expansionGrowPairBlock inv (s := s) entry running initial control iterate
  have work : 1 + (s.nr 95 * (41 + 3) + 1) = 44 * s.nr 95 + 2 := by omega
  rw [work] at run
  obtain ⟨done, pending, result, now, split, doneLength, nowAt, cursor, finalEncoding, agrees,
    lastRecordAt, witness, restWitness⟩ := complete.path
  have noPending : pending = [] := by
    apply List.length_eq_zero_iff.mp
    have sum := congrArg List.length split
    simp only [List.length_append] at sum
    omega
  subst pending
  have allDone : done = records := by simpa using split.symm
  subst done
  have same : (result, now) = grown := agrees
  have encoded : AlternatingForestMemory grown.1 forestBase last.nm := by rw [← same]; exact finalEncoding
  have atLast : last.nr 0 = grown.2.val := by rw [← same]; exact nowAt
  exact ⟨_, run, complete.ready, encoded, atLast, cursor, lastRecordAt, witness, restWitness,
    complete.keeps, complete.real, complete.realRegisters, complete.fixed⟩

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionPairLoop

/-! matching/ExpansionBaseRAM.lean -/
section RppSource_ExpansionBaseRAM
namespace VehicleRoutingSurvey.Routing



theorem prepareExpansionPairsBlock_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 14 = 0) :
    ∃ t, BlockRuns prepareExpansionPairsBlock 5 s t ∧ t.halted = false ∧
      t.nr 0 = s.nr 96 ∧ t.nr 23 = s.nr 94 ∧ t.nr 3 = s.nr 51 ∧ t.nr 4 = s.nr 52 ∧ t.nr 5 = s.nr 53 ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 3, 4, 5, 23] → t.nr r = s.nr r := by
  let t := (arithmeticStep prepareExpansionPairsBlock)^[5] s
  have ready : t.halted = false := by
    simp [t, prepareExpansionPairsBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  have exit : t.pc = prepareExpansionPairsBlock.length := by
    simp [t, prepareExpansionPairsBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
  | intro r stable
    apply arithmeticRun_keeps_register
    simp [prepareExpansionPairsBlock, naturalDestination] at stable ⊢ <;> omega
  | simp [t, prepareExpansionPairsBlock, arithmeticStep, Function.iterate_succ_apply', entry, running, zero]



theorem reattachExpansionBaseBlock_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns reattachExpansionBaseBlock 11 s t ∧ t.halted = false ∧
      t.nm = writeMatchingForestWitness (Function.update s.nm (s.nr 52 + s.nr 97) (s.nr 0))
        (s.nr 90) (s.nr 97) (s.nm (s.nr 23 + 1), s.nm (s.nr 23 + 2)) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r ≥ 30, t.nr r = s.nr r := by
  let t := (arithmeticStep reattachExpansionBaseBlock)^[11] s
  have ready : t.halted = false := by
    simp [t, reattachExpansionBaseBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  have exit : t.pc = reattachExpansionBaseBlock.length := by
    simp [t, reattachExpansionBaseBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_⟩
  all_goals first
  | intro r high
    apply arithmeticRun_keeps_high_register
    intro ins belongs
    have destinations : reattachExpansionBaseBlock.all (fun x => decide (naturalDestination x < 30)) = true := by decide
    exact (of_decide_eq_true (List.all_eq_true.mp destinations ins belongs) : naturalDestination ins < 30).trans_le high
  | simp [t, reattachExpansionBaseBlock, arithmeticStep, Function.iterate_succ_apply', entry, running, one,
      writeMatchingForestWitness, forestWitnessAddress, Nat.add_assoc]

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionBaseRAM

/-! matching/ExpansionForestRAM.lean -/
section RppSource_ExpansionForestRAM
namespace VehicleRoutingSurvey.Routing

structure ExpansionForestFrame (k forestBase witnessBase pathBase : ℕ) (s : ArithmeticState) : Prop where
  dimension : s.nr 55 = k
  one : s.nr 9 = 1
  zero : s.nr 14 = 0
  roles : s.nr 51 = forestBase
  parents : s.nr 52 = forestBase + k
  depths : s.nr 53 = forestBase + k + k
  witnesses : s.nr 90 = witnessBase
  path : s.nr 94 = pathBase
  forestGap : forestBase + k + k + k ≤ witnessBase
  pathGap : witnessBase + k + k ≤ pathBase



/-- Relabel the forest along a chosen expansion path. The buffer stores
the even list of child records and then the original base's record. Each
record supplies the original endpoints of the new parent edge. -/
theorem expandAlternatingForestBlock_spec {k forestBase witnessBase pathBase : ℕ} {s : ArithmeticState}
    (frame : ExpansionForestFrame k forestBase witnessBase pathBase s)
    {forest : AlternatingForestState (Fin k)} {source base : Fin k}
    {records : List (ExpansionPathRecord k)} {lastEdge : Fin k × Fin k}
    (entry : s.pc = 0) (running : s.halted = false)
    (sourceAt : s.nr 96 = source.val) (baseAt : s.nr 97 = base.val)
    (length : records.length = s.nr 95 + s.nr 95)
    (distinct : (records.map ExpansionPathRecord.vertex).Nodup)
    (avoidsBase : base ∉ records.map ExpansionPathRecord.vertex)
    (baseInner : forest.role base = .inner source)
    (encoding : AlternatingForestMemory forest forestBase s.nm)
    (encodedPath : ExpansionPathMemory s.nm pathBase (records ++ [⟨base, lastEdge⟩])) :
    ∃ t, BlockRuns expandAlternatingForestBlock (9 * k + 44 * s.nr 95 + 23) s t ∧ t.halted = false ∧
      AlternatingForestMemory (forest.expandAlong source base (records.map ExpansionPathRecord.vertex)) forestBase t.nm ∧
      (∀ record ∈ records ++ [⟨base, lastEdge⟩],
        matchingForestWitnessAt t.nm witnessBase record.vertex.val = record.witness) ∧
      (∀ v : Fin k, v ≠ base → v ∉ records.map ExpansionPathRecord.vertex →
        matchingForestWitnessAt t.nm witnessBase v.val = matchingForestWitnessAt s.nm witnessBase v.val) ∧
      (∀ a, (a < forestBase ∨ forestBase + k + k + k ≤ a) →
        (a < witnessBase ∨ witnessBase + k + k ≤ a) → t.nm a = s.nm a) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r ≥ 30, t.nr r = s.nr r := by
  let vertices := records.map ExpansionPathRecord.vertex
  let lastRecord : ExpansionPathRecord k := ⟨base, lastEdge⟩
  let raised : AlternatingForestState (Fin k) :=
    { forest with
      depth := fun v => forest.depth v + (if forest.depth base ≤ forest.depth v then vertices.length else 0) }
  obtain ⟨d, reserve, reserveReady, reserveMemory, reserveReal, reserveRr, reserveFixed⟩ :=
    reserveExpansionDepthsBlock_spec entry running frame.one
  have lengthEq : vertices.length = s.nr 95 + s.nr 95 := by simpa [vertices] using length
  have reservedMemory : d.nm = shiftedExpansionDepths s.nm (forestBase + k + k) (forest.depth base) vertices.length k := by
    rw [reserveMemory, frame.depths, baseAt, (encoding base).2.2, ← lengthEq, frame.dimension]
  have depthKeeps (a : ℕ) (outside : a < forestBase + k + k ∨ forestBase + k + k + k ≤ a) : d.nm a = s.nm a := by
    rw [reservedMemory, shiftedExpansionDepths, if_neg (by omega)]
  have reservedEncoding : AlternatingForestMemory raised forestBase d.nm := by
    intro v
    have isLt := v.isLt
    refine ⟨(depthKeeps (forestBase + v.val) (Or.inl (by omega))).trans (encoding v).1,
      (depthKeeps (forestBase + k + v.val) (Or.inl (by omega))).trans (encoding v).2.1, ?_⟩
    change d.nm (forestBase + k + k + v.val) = raised.depth v
    rw [reservedMemory, shiftedExpansionDepths, if_pos (by omega), (encoding v).2.2] <;> rfl
  let setup := {d with pc := 0}
  obtain ⟨p, prepares, prepReady, prepSource, prepCursor, prepRoles, prepParents, prepDepths, prepNat,
    prepReal, prepRr, prepFixed⟩ := prepareExpansionPairsBlock_spec (s := setup) rfl reserveReady
      ((reserveFixed 14 (by decide)).trans frame.zero)
  let pairEntry := {p with pc := 0}
  have prepKeeps (r : ℕ) (stable : r ∉ ([0, 3, 4, 5, 10, 11, 12, 15, 16, 23] : List ℕ)) :
      pairEntry.nr r = s.nr r :=
    (prepFixed r (by simp at stable ⊢; omega)).trans (reserveFixed r (by simp at stable ⊢; omega))
  have pairCount : pairEntry.nr 95 = s.nr 95 := prepKeeps 95 (by decide)
  have pairCursor : pairEntry.nr 23 = pathBase := (prepCursor.trans (reserveFixed 94 (by decide))).trans frame.path
  have pairEncoding : AlternatingForestMemory raised forestBase pairEntry.nm := prepNat.symm ▸ reservedEncoding
  have livePath : ExpansionPathMemory pairEntry.nm (pairEntry.nr 23) (records ++ [lastRecord]) := by
    rw [pairCursor]
    apply encodedPath.preserved
    intro a after
    exact (congrFun prepNat a).trans (depthKeeps a (Or.inr (by
      have lower := frame.forestGap
      have ahead := frame.pathGap
      omega)))
  obtain ⟨g, grows, grownReady, grownEncoding, predecessor, _, finalRecord, witness, witnessKeeps,
    pairMemoryKeeps, pairReal, pairRr, pairFixed⟩ := expandForestPairsBlock_spec (s := pairEntry)
      rfl prepReady ((prepKeeps 9 (by decide)).trans frame.one) ((prepKeeps 14 (by decide)).trans frame.zero)
      ((prepSource.trans (reserveFixed 96 (by decide))).trans sourceAt)
      ((prepRoles.trans (reserveFixed 51 (by decide))).trans frame.roles)
      ((prepParents.trans (reserveFixed 52 (by decide))).trans frame.parents)
      ((prepDepths.trans (reserveFixed 53 (by decide))).trans frame.depths)
      ((prepKeeps 90 (by decide)).trans frame.witnesses) frame.forestGap
      (by rw [pairCursor]; exact frame.pathGap) (by rw [pairCount]; exact length) distinct pairEncoding livePath
  let grown := raised.growPairs source vertices
  let attach := {g with pc := 0}
  have grownHigh (r : ℕ) (high : 30 ≤ r) : attach.nr r = s.nr r :=
    (pairFixed r (by simp [expansionPairScratch] <;> omega)).trans (prepKeeps r (by simp <;> omega))
  obtain ⟨t, reattaches, ready, attachNat, attachReal, attachRr, attachFixed⟩ :=
    reattachExpansionBaseBlock_spec (s := attach) rfl grownReady
      ((pairFixed 9 (by decide)).trans ((prepKeeps 9 (by decide)).trans frame.one))
  obtain ⟨_, witnessA, witnessB, _⟩ := finalRecord
  have finalMemory : t.nm = writeMatchingForestWitness
        (Function.update g.nm (forestBase + k + base.val) grown.2.val)
        witnessBase base.val lastRecord.witness := by
    rw [attachNat]
    change writeMatchingForestWitness (Function.update g.nm (g.nr 52 + g.nr 97) (g.nr 0))
      (g.nr 90) (g.nr 97) (g.nm (g.nr 23 + 1), g.nm (g.nr 23 + 2)) = _
    rw [(grownHigh 52 (by decide)).trans frame.parents, (grownHigh 97 (by decide)).trans baseAt,
      (grownHigh 90 (by decide)).trans frame.witnesses, predecessor, witnessA, witnessB] <;> rfl
  let changed := Function.update g.nm (forestBase + k + base.val) grown.2.val
  have outsideWitness (a : ℕ) (away : a < witnessBase ∨ witnessBase + k + k ≤ a) :
      t.nm a = changed a := by
    rw [finalMemory, vertexWitnessMemory_preserves base.isLt away]
  have otherAddress (a : ℕ) (outside : a ≠ forestBase + k + base.val)
      (away : a < witnessBase ∨ witnessBase + k + k ≤ a) : t.nm a = g.nm a := by
    rw [outsideWitness a away]
    exact Function.update_of_ne outside _ _
  let reattached : AlternatingForestState (Fin k) :=
    {grown.1 with role := Function.update grown.1.role base (.inner grown.2)}
  have exactForest : forest.expandAlong source base vertices = reattached := rfl
  have wasInner : grown.1.role base = .inner source :=
    ((AlternatingForestState.growPairs_preserves (state := raised) (source := source) vertices avoidsBase).1).trans baseInner
  have forestEnd : AlternatingForestMemory (forest.expandAlong source base vertices) forestBase t.nm := by
    rw [exactForest]
    intro v
    have inBounds := v.isLt
    have baseInBounds := base.isLt
    have below := frame.forestGap
    have roleMemory := otherAddress (forestBase + v.val) (by omega) (Or.inl (by omega))
    have depthMemory := otherAddress (forestBase + k + k + v.val) (by omega) (Or.inl (by omega))
    have nowDepth := depthMemory.trans (grownEncoding v).2.2
    by_cases isBase : v = base
    · subst v
      have newRole : reattached.role base = .inner grown.2 := by simp [reattached]
      have formerRole := (grownEncoding base).1
      rw [wasInner] at formerRole
      refine ⟨?_, ?_, nowDepth⟩
      · rw [newRole]
        exact roleMemory.trans formerRole
      · rw [newRole, outsideWitness _ (Or.inl (by omega))]
        exact Function.update_self _ _ _
    · have sameRole : reattached.role v = grown.1.role v := Function.update_of_ne isBase _ _
      have atOther : v.val ≠ base.val := fun eq => isBase (Fin.ext eq)
      have parentMemory := otherAddress (forestBase + k + v.val) (by omega) (Or.inl (by omega))
      refine ⟨?_, ?_, nowDepth⟩
      · rw [sameRole]
        exact roleMemory.trans (grownEncoding v).1
      · rw [sameRole]
        exact parentMemory.trans (grownEncoding v).2.1
  have keepsOldWitness (v : Fin k) (outside : v ≠ base) :
      matchingForestWitnessAt t.nm witnessBase v.val = matchingForestWitnessAt g.nm witnessBase v.val := by
    have different : v.val ≠ base.val := fun eq => outside (Fin.ext eq)
    rw [finalMemory, matchingForestWitnessAt_write_other _ _ _ _ _ different]
    unfold matchingForestWitnessAt forestWitnessAddress
    dsimp only
    have below := frame.forestGap
    have inBounds := base.isLt
    rw [Function.update_of_ne (show witnessBase + (v.val + v.val) ≠ forestBase + k + base.val by omega),
      Function.update_of_ne (show witnessBase + (v.val + v.val) + 1 ≠ forestBase + k + base.val by omega)]
  have originalWitness (v : Fin k) : matchingForestWitnessAt pairEntry.nm witnessBase v.val =
      matchingForestWitnessAt s.nm witnessBase v.val := by
    change matchingForestWitnessAt p.nm _ _ = _
    rw [prepNat]
    unfold matchingForestWitnessAt forestWitnessAddress
    dsimp only
    have below := frame.forestGap
    rw [depthKeeps (witnessBase + (v.val + v.val)) (Or.inr (by omega)),
      depthKeeps (witnessBase + (v.val + v.val) + 1) (Or.inr (by omega))]
  have exactSteps : (9 * s.nr 55 + 5) + (5 + ((44 * pairEntry.nr 95 + 2) + 11)) =
      9 * k + 44 * s.nr 95 + 23 := by rw [frame.dimension, pairCount]; omega
  have run := reserve.append (prepares.append (grows.append reattaches))
  rw [exactSteps] at run
  refine ⟨_, run, ready, forestEnd, ?_, ?_, ?_, ((attachReal.trans pairReal).trans prepReal).trans reserveReal,
    ((attachRr.trans pairRr).trans prepRr).trans reserveRr,
    fun r high => (attachFixed r high).trans (grownHigh r high)⟩
  · intro record member
    change matchingForestWitnessAt t.nm witnessBase record.vertex.val = record.witness
    rcases List.mem_append.mp member with earlier | final
    · have away : record.vertex ≠ base := fun same => avoidsBase (same ▸ List.mem_map_of_mem earlier)
      exact (keepsOldWitness record.vertex away).trans (witness record earlier)
    · have equal : record = lastRecord := List.mem_singleton.mp final
      subst record
      rw [finalMemory, matchingForestWitnessAt_write_same]
  · intro v away before
    exact ((keepsOldWitness v away).trans (witnessKeeps v before)).trans (originalWitness v)
  · intro a outsideForest outsideWitnessArray
    have oldBase := base.isLt
    exact ((otherAddress a (by omega) outsideWitnessArray).trans (pairMemoryKeeps a outsideForest outsideWitnessArray)).trans
      ((congrFun prepNat a).trans (depthKeeps a (by omega)))

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionForestRAM

/-! matching/ExpansionLookupCell.lean -/
section RppSource_ExpansionLookupCell
namespace VehicleRoutingSurvey.Routing

theorem readExpansionRepresentative_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) :
    ∃ t, BlockRuns readExpansionRepresentative 4 s t ∧ t.halted = false ∧
      t.nr 15 = s.nm (s.nr 18 + 4 * s.nr 7) ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [6, 15] → t.nr r = s.nr r := by
  let t := (arithmeticStep readExpansionRepresentative)^[4] s
  have ready : t.halted = false := by
    simp [t, readExpansionRepresentative, arithmeticStep, Function.iterate_succ_apply', entry, running]
  have exit : t.pc = readExpansionRepresentative.length := by
    simp [t, readExpansionRepresentative, arithmeticStep, Function.iterate_succ_apply', entry, running]
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
  | intro r safe
    exact arithmeticRun_keeps_from_destination_list [6, 15] (by decide) safe s 4
  | have address : s.nr 7 + s.nr 7 + (s.nr 7 + s.nr 7) = 4 * s.nr 7 := by omega
    simp [t, readExpansionRepresentative, arithmeticStep, Function.iterate_succ_apply', entry, running, address]

private theorem rememberExpansionIndex_spec (representative output : ℕ) {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (zero : s.nr 23 = 0) :
    ∃ t steps, BlockRuns (rememberExpansionIndex representative output) steps s t ∧
      steps ≤ 5 ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      t.nr = if s.nr 15 = s.nr representative then Function.update s.nr output (s.nr 7) else s.nr := by
  let write : List ArithmeticInstruction := [.natAdd output 7 23]
  let written := {s with pc := 1, nr := Function.update s.nr output (s.nr 7)}
  have writes : BlockRuns write 1 s written := by
    apply BlockRuns.of_running_exit
    · simp [write, written, arithmeticStep, entry, running, zero]
    · exact running
    · rfl
  have empty : BlockRuns [] 0 s s := ⟨fun i h => (Nat.not_lt_zero i h).elim, rfl, entry⟩
  rcases lt_trichotomy (s.nr 15) (s.nr representative) with earlier | same | later
  · have nested := branchOnAtMost_right representative 15 write [] entry running earlier empty running
    have ran := branchOnAtMost_left 15 representative (branchOnAtMost representative 15 write []) []
      entry running earlier.le nested running
    exact ⟨_, _, ran, by decide, running, rfl, rfl, rfl, (if_neg earlier.ne).symm⟩
  · have nested := branchOnAtMost_left representative 15 write [] entry running same.ge writes running
    have ran := branchOnAtMost_left 15 representative (branchOnAtMost representative 15 write []) []
      entry running same.le nested running
    exact ⟨_, _, ran, by decide, running, rfl, rfl, rfl, (if_pos same).symm⟩
  · have ran := branchOnAtMost_right 15 representative (branchOnAtMost representative 15 write []) []
      entry running later empty running
    exact ⟨_, _, ran, by decide, running, rfl, rfl, rfl, (if_neg later.ne').symm⟩

private theorem expansionRememberedIndex_keeps {s t : ArithmeticState} {representative output : ℕ}
    (effect : t.nr = if s.nr 15 = s.nr representative then Function.update s.nr output (s.nr 7) else s.nr)
    {r : ℕ} (different : r ≠ output) : t.nr r = s.nr r := by
  rw [effect]
  split <;> simp [Function.update_of_ne different]

theorem considerExpansionIndex_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 23 = 0) :
    let owner := s.nm (s.nr 18 + 4 * s.nr 7)
    ∃ t steps, BlockRuns considerExpansionIndex steps s t ∧ steps ≤ 14 ∧ t.halted = false ∧
      t.nr 81 = (if owner = s.nr 27 then s.nr 7 else s.nr 81) ∧
      t.nr 82 = (if owner = s.nr 97 then s.nr 7 else s.nr 82) ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 15, 81, 82] → t.nr r = s.nr r := by
  intro owner
  obtain ⟨m, reads, live, current, nat, real, rr, fixed⟩ := readExpansionRepresentative_spec entry running
  let first := {m with pc := 0}
  obtain ⟨p, firstSteps, remembers, firstCost, firstLive, firstNat, firstReal, firstRr, firstUpdate⟩ :=
    rememberExpansionIndex_spec 27 81 (s := first) rfl live ((fixed 23 (by decide)).trans zero)
  let second := {p with pc := 0}
  have beforeSecond (r : ℕ) (safe : r ≠ 81) : second.nr r = first.nr r :=
    expansionRememberedIndex_keeps firstUpdate safe
  obtain ⟨t, secondSteps, continues, secondCost, secondLive, secondNat, secondReal, secondRr, secondUpdate⟩ :=
    rememberExpansionIndex_spec 97 82 (s := second) rfl firstLive
      ((beforeSecond 23 (by decide)).trans ((fixed 23 (by decide)).trans zero))
  have firstIndex : p.nr 81 = if owner = s.nr 27 then s.nr 7 else s.nr 81 := by
    rw [firstUpdate]
    have equalities : first.nr 15 = owner ∧ first.nr 27 = s.nr 27 ∧ first.nr 7 = s.nr 7 ∧
        first.nr 81 = s.nr 81 := ⟨current, fixed 27 (by decide), fixed 7 (by decide), fixed 81 (by decide)⟩
    rw [equalities.1, equalities.2.1, equalities.2.2.1]
    split <;> simp [equalities.2.2.2]
  have secondIndex : t.nr 82 = if owner = s.nr 97 then s.nr 7 else s.nr 82 := by
    rw [secondUpdate]
    have equalities : second.nr 15 = owner ∧ second.nr 97 = s.nr 97 ∧ second.nr 7 = s.nr 7 ∧
        second.nr 82 = s.nr 82 := ⟨(beforeSecond 15 (by decide)).trans current,
          (beforeSecond 97 (by decide)).trans (fixed 97 (by decide)),
          (beforeSecond 7 (by decide)).trans (fixed 7 (by decide)),
          (beforeSecond 82 (by decide)).trans (fixed 82 (by decide))⟩
    rw [equalities.1, equalities.2.1, equalities.2.2.1]
    split <;> simp [equalities.2.2.2]
  refine ⟨_, _, reads.append (remembers.append continues), by omega, secondLive,
    (expansionRememberedIndex_keeps secondUpdate (by decide : (81 : ℕ) ≠ 82)).trans firstIndex, secondIndex,
    (secondNat.trans firstNat).trans nat, (secondReal.trans firstReal).trans real,
    (secondRr.trans firstRr).trans rr, ?_⟩
  intro r safe
  exact ((expansionRememberedIndex_keeps secondUpdate (by simp at safe; omega)).trans
    (beforeSecond r (by simp at safe; omega))).trans (fixed r (by simp at safe ⊢; omega))

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionLookupCell

/-! matching/MatchingExpansionLookup.lean -/
section RppSource_MatchingExpansionLookup
namespace VehicleRoutingSurvey.Routing







private theorem readExpansionHeader_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 23 = 0) :
    ∃ t, BlockRuns readExpansionHeader 8 s t ∧ t.halted = false ∧
      t.nr 18 = expansionRegisteredCycleBase s ∧ t.nr 19 = expansionRegisteredCycleLength s ∧
      t.nr 81 = s.nr 55 ∧ t.nr 82 = s.nr 55 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 18, 19, 22, 81, 82] → t.nr r = s.nr r := by
  let t := (arithmeticStep readExpansionHeader)^[8] s
  have computed : t.pc = readExpansionHeader.length ∧ t.halted = false ∧
      t.nr 18 = expansionRegisteredCycleBase s ∧ t.nr 19 = expansionRegisteredCycleLength s ∧
      t.nr 81 = s.nr 55 ∧ t.nr 82 = s.nr 55 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, readExpansionHeader, readMatchingCycleHeader, appendBlock, relocateInstruction,
      expansionRegisteredCycleBase, expansionRegisteredCycleLength, expansionOldNode,
      arithmeticStep, Function.iterate_succ_apply', entry, running, zero]
  refine ⟨t, BlockRuns.of_running_exit rfl computed.2.1 computed.1, computed.2.1, computed.2.2.1,
    computed.2.2.2.1, computed.2.2.2.2.1, computed.2.2.2.2.2.1, computed.2.2.2.2.2.2.1,
    computed.2.2.2.2.2.2.2.1, computed.2.2.2.2.2.2.2.2, ?_⟩
  intro r safe
  exact arithmeticRun_keeps_from_destination_list [0, 6, 18, 19, 22, 81, 82] (by decide) safe s 8

private def expansionSearchScratch : List ℕ := [0, 6, 7, 15, 81, 82]

private structure ExpansionIndexScan (initial : ArithmeticState) (entryIndex baseIndex i : ℕ)
    (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  ready : s.halted = false
  index : s.nr 7 = i
  fixed : ∀ r, r ∉ expansionSearchScratch → s.nr r = initial.nr r
  entrySlot : s.nr 81 = if entryIndex < i then entryIndex else initial.nr 81
  baseSlot : s.nr 82 = if baseIndex < i then baseIndex else initial.nr 82
  natural : s.nm = initial.nm
  real : s.rm = initial.rm
  realRegisters : s.rr = initial.rr

private theorem expansionIndex_after {i selected previous : ℕ} :
    (if i = selected then i else if selected < i then selected else previous) =
      if selected < i + 1 then selected else previous := by
  by_cases current : i = selected
  · subst i
    simp
  · by_cases before : selected < i
    · simp [current, before, show selected < i + 1 by omega]
    · simp [current, before, show ¬(selected < i + 1) by omega]

private theorem scanExpansionIndices_spec {s : ArithmeticState} {entryIndex baseIndex : ℕ}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0)
    (entryWithin : entryIndex < s.nr 19) (baseWithin : baseIndex < s.nr 19)
    (entryUnique : ∀ i < s.nr 19, s.nm (s.nr 18 + 4 * i) = s.nr 27 ↔ i = entryIndex)
    (baseUnique : ∀ i < s.nr 19, s.nm (s.nr 18 + 4 * i) = s.nr 97 ↔ i = baseIndex) :
    ∃ t steps, BlockRuns (countedLoopFromZero 9 7 19 considerExpansionIndex) steps s t ∧
      steps ≤ 17 * s.nr 19 + 2 ∧ t.halted = false ∧ t.nr 81 = entryIndex ∧ t.nr 82 = baseIndex ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ expansionSearchScratch → t.nr r = s.nr r := by
  let inv := ExpansionIndexScan s entryIndex baseIndex
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, by simp, by simp, rfl, rfl, rfl⟩
    intro r safe
    have notIndex : r ≠ 7 := fun eq => safe (eq.symm ▸ (by decide : (7 : ℕ) ∈ expansionSearchScratch))
    exact Function.update_of_ne notIndex _ _
  have control (i : ℕ) (m : ArithmeticState) (h : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 19 = s.nr 19 :=
    ⟨h.entry, h.ready, h.index, h.fixed 19 (by decide)⟩
  have next (i : ℕ) (within : i < s.nr 19) (m : ArithmeticState) (h : inv i m) :
      ∃ t steps, steps ≤ 14 ∧ BlockRuns considerExpansionIndex steps m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    obtain ⟨t, steps, reads, bound, ready, outEntry, outBase, natural, real, rr, fixed⟩ :=
      considerExpansionIndex_spec h.entry h.ready ((h.fixed 23 (by decide)).trans zero)
    refine ⟨t, steps, bound, reads, ready, rfl, ready, ?_, ?_, ?_, ?_, natural.trans h.natural,
      real.trans h.real, rr.trans h.realRegisters⟩
    · simp [fixed 7 (by decide), fixed 9 (by decide), h.index, h.fixed 9 (by decide), one]
    · intro r safe
      have notIndex : r ≠ 7 := fun eq => safe (eq.symm ▸ (by decide : (7 : ℕ) ∈ expansionSearchScratch))
      change Function.update t.nr 7 (t.nr 7 + t.nr 9) r = s.nr r
      rw [Function.update_of_ne notIndex]
      exact (fixed r (by simp [expansionSearchScratch] at safe ⊢; omega)).trans (h.fixed r safe)
    · have condition : (m.nm (m.nr 18 + 4 * i) = m.nr 27) ↔ i = entryIndex := by
        rw [h.natural, h.fixed 18 (by decide), h.fixed 27 (by decide)]
        exact entryUnique i within
      change t.nr 81 = _
      rw [outEntry, h.index, h.entrySlot]
      simpa only [condition] using
        (expansionIndex_after (i := i) (selected := entryIndex) (previous := s.nr 81))
    · have condition : (m.nm (m.nr 18 + 4 * i) = m.nr 97) ↔ i = baseIndex := by
        rw [h.natural, h.fixed 18 (by decide), h.fixed 97 (by decide)]
        exact baseUnique i within
      change t.nr 82 = _
      rw [outBase, h.index, h.baseSlot]
      simpa only [condition] using
        (expansionIndex_after (i := i) (selected := baseIndex) (previous := s.nr 82))
  obtain ⟨last, actual, done, bound, run⟩ := countedLoopFromZero_bounded 9 7 19 (s.nr 19) 14
    considerExpansionIndex inv (s := s) entry running initial control next
  have entryAt : last.nr 81 = entryIndex := done.entrySlot.trans (if_pos entryWithin)
  have baseAt : last.nr 82 = baseIndex := done.baseSlot.trans (if_pos baseWithin)
  exact ⟨_, actual, run, by omega, done.ready, entryAt, baseAt, done.natural, done.real, done.realRegisters, done.fixed⟩

structure ExpansionLookupResult (initial final : ArithmeticState) (entryIndex baseIndex : ℕ) : Prop where
  cycleStart : final.nr 18 = expansionRegisteredCycleBase initial
  cycleLength : final.nr 19 = expansionRegisteredCycleLength initial
  entrySlot : final.nr 81 = entryIndex
  baseSlot : final.nr 82 = baseIndex
  oldWitness : (final.nr 43, final.nr 44) = expansionOldParentWitness initial
  parent : final.nr 96 = initial.nm (initial.nr 52 + initial.nr 97)
  mate : final.nr 98 = initial.nm (initial.nr 50 + initial.nr 97)
  zero : final.nr 23 = 0
  natural : final.nm = initial.nm
  real : final.rm = initial.rm
  realRegisters : final.rr = initial.rr
  fixed : ∀ r, r ∉ [0, 6, 7, 10, 15, 18, 19, 22, 23, 27, 43, 44, 81, 82, 96, 98] → final.nr r = initial.nr r

/-- Identify the entry and old base positions without modifying the child
map or any registry cells. The scan visits the cycle once. -/
theorem locateMatchingExpansionEndpoints_spec {s : ArithmeticState} {entryIndex baseIndex : ℕ}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (entryWithin : entryIndex < expansionRegisteredCycleLength s)
    (baseWithin : baseIndex < expansionRegisteredCycleLength s)
    (entryUnique : ∀ i < expansionRegisteredCycleLength s,
      s.nm (expansionRegisteredCycleBase s + 4 * i) = expansionEntryChild s ↔ i = entryIndex)
    (baseUnique : ∀ i < expansionRegisteredCycleLength s,
      s.nm (expansionRegisteredCycleBase s + 4 * i) = s.nr 97 ↔ i = baseIndex) :
    ∃ t steps, BlockRuns locateMatchingExpansionEndpoints steps s t ∧ t.halted = false ∧
      steps ≤ 17 * expansionRegisteredCycleLength s + 28 ∧ ExpansionLookupResult s t entryIndex baseIndex := by
  obtain ⟨m, findSteps, findBound, finds, findReady, child, parent, mate, witness, natural, real, rr, findZero⟩ :=
    findExpansionEntryChild_spec s entry running one
  let header := {m with pc := 0}
  have findFixed (r : ℕ) (safe : r ∉ [0, 6, 10, 23, 27, 43, 44, 96, 98]) : m.nr r = s.nr r := by
    rw [← finds.run]
    exact arithmeticRun_keeps_from_destination_list [0, 6, 10, 23, 27, 43, 44, 96, 98]
      (by decide) safe s findSteps
  have node : expansionOldNode header = expansionOldNode s := by
    change m.nm (m.nr 74 + m.nr 97) = _
    rw [natural, findFixed 74 (by decide), findFixed 97 (by decide)] <;> rfl
  have headerStart : expansionRegisteredCycleBase header = expansionRegisteredCycleBase s := by
    unfold expansionRegisteredCycleBase
    rw [show header.nm = s.nm from natural, show header.nr 77 = s.nr 77 from findFixed 77 (by decide), node]
  have headerLength : expansionRegisteredCycleLength header = expansionRegisteredCycleLength s := by
    unfold expansionRegisteredCycleLength
    rw [show header.nm = s.nm from natural, show header.nr 78 = s.nr 78 from findFixed 78 (by decide), node]
  obtain ⟨h, headers, headerReady, started, size, _, _, storedNat, storedReal, storedRr, headerFixed⟩ :=
    readExpansionHeader_spec (s := header) rfl findReady findZero
  let scan := {h with pc := 0}
  have startAt : scan.nr 18 = expansionRegisteredCycleBase s := started.trans headerStart
  have countAt : scan.nr 19 = expansionRegisteredCycleLength s := size.trans headerLength
  have readTable : scan.nm = s.nm := storedNat.trans natural
  have target : scan.nr 27 = expansionEntryChild s := (headerFixed 27 (by decide)).trans child
  have baseTarget : scan.nr 97 = s.nr 97 := (headerFixed 97 (by decide)).trans (findFixed 97 (by decide))
  obtain ⟨t, scanSteps, scans, scanBound, ready, atEntry, atBase, lastNat, lastReal, lastRr, scanFixed⟩ :=
    scanExpansionIndices_spec (s := scan) rfl headerReady
      ((headerFixed 9 (by decide)).trans ((findFixed 9 (by decide)).trans one))
      ((headerFixed 23 (by decide)).trans findZero)
      (countAt.symm ▸ entryWithin) (countAt.symm ▸ baseWithin)
      (fun i within => by rw [readTable, startAt, target]; exact entryUnique i (countAt ▸ within))
      (fun i within => by rw [readTable, startAt, baseTarget]; exact baseUnique i (countAt ▸ within))
  have throughScan (r : ℕ) (hs : r ∉ expansionSearchScratch)
      (hh : r ∉ ([0, 6, 18, 19, 22, 81, 82] : List ℕ)) : t.nr r = m.nr r :=
    (scanFixed r hs).trans (headerFixed r hh)
  have outsideNat : t.nm = s.nm := lastNat.trans readTable
  have outsideReal : t.rm = s.rm := (lastReal.trans storedReal).trans real
  have outsideRr : t.rr = s.rr := (lastRr.trans storedRr).trans rr
  have total : findSteps + (8 + scanSteps) ≤ 17 * expansionRegisteredCycleLength s + 28 := by
    rw [countAt] at scanBound
    omega
  refine ⟨_, _, finds.append (headers.append scans), ready, total,
    (scanFixed 18 (by decide)).trans startAt, (scanFixed 19 (by decide)).trans countAt, atEntry, atBase,
    ?_, (throughScan 96 (by decide) (by decide)).trans parent, (throughScan 98 (by decide) (by decide)).trans mate,
    (throughScan 23 (by decide) (by decide)).trans findZero, outsideNat, outsideReal, outsideRr, ?_⟩
  · change (t.nr 43, t.nr 44) = _
    rw [throughScan 43 (by decide) (by decide), throughScan 44 (by decide) (by decide)]
    exact witness
  · intro r safe
    exact (throughScan r (by simp [expansionSearchScratch] at safe ⊢; omega)
      (by simp at safe ⊢; omega)).trans (findFixed r (by simp at safe ⊢; omega))

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionLookup

/-! matching/ExpansionEmitterStep.lean -/
section RppSource_ExpansionEmitterStep
namespace VehicleRoutingSurvey.Routing

def writeExpansionTripleWords (memory : ℕ → ℕ) (address : ℕ) (words : ℕ × ℕ × ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update memory address words.1) (address + 1) words.2.1)
    (address + 2) words.2.2

def expansionEmitterStepScratch : List ℕ := [0, 6, 7, 15, 16, 17, 25, 47]

def expansionNextRegistryIndex (s : ArithmeticState) : ℕ :=
  if s.nr 45 ≤ s.nr 23 then (s.nr 7 + 1) % s.nr 19
  else if s.nr 7 = 0 then s.nr 19 - 1 else s.nr 7 - 1

def expansionNextTriple (s : ArithmeticState) : ℕ × ℕ × ℕ :=
  let incoming := matchingCycleChildAt s.nm (s.nr 18 + 4 * s.nr 7)
  let next := matchingCycleChildAt s.nm (s.nr 18 + 4 * expansionNextRegistryIndex s)
  if s.nr 45 ≤ s.nr 23 then (next.representative, incoming.endpointA, incoming.endpointB)
  else (next.representative, next.endpointB, next.endpointA)

def expansionPreviousIndex (length index : ℕ) : ℕ := if index = 0 then length - 1 else index - 1

private theorem writeExpansionPathForward_spec {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (inside : s.nr 7 < s.nr 19) :
    let index := (s.nr 7 + 1) % s.nr 19
    let old := matchingCycleChildAt s.nm (s.nr 18 + 4 * s.nr 7)
    let words := (s.nm (s.nr 18 + 4 * index), old.endpointA, old.endpointB)
    ∃ t steps, BlockRuns writeExpansionPathForward steps s t ∧ steps ≤ 23 ∧ t.halted = false ∧
      t.nr 7 = index ∧ t.nr 47 = s.nr 47 + 3 ∧ t.nm = writeExpansionTripleWords s.nm (s.nr 47) words ∧
      t.rm = s.rm ∧ t.rr = s.rr := by
  intro index old words
  obtain ⟨a, reads, rLive, row, rNat, rReal, rRr, rFixed⟩ := readMatchingCycleChild_spec s entry running one
  let advance := {a with pc := 0}
  let next := {advance with pc := 3, nr := Function.update advance.nr 7 ((advance.nr 7 + 1) % advance.nr 19)}
  have indexAt : next.nr 7 = index := by simp [next, advance, rFixed 7 (by decide), rFixed 19 (by decide), index]
  have advanceOne : advance.nr 9 = 1 := (rFixed 9 (by decide)).trans one
  have advanceInside : advance.nr 7 < advance.nr 19 := by
    change a.nr 7 < a.nr 19
    rwa [rFixed 7 (by decide), rFixed 19 (by decide)]
  obtain ⟨advanceSteps, advanceBound, moves⟩ := advanceMatchingCycleIndexBlock_correct
    (s := advance) rfl rLive advanceOne advanceInside
  let readNode := {next with pc := 0}
  obtain ⟨b, finds, fLive, found, fNat, fReal, fRr, fFixed⟩ := readExpansionRepresentative_spec (s := readNode) rfl rLive
  have readFixed (r : ℕ) (outside : r ≠ 7) : readNode.nr r = a.nr r := Function.update_of_ne outside _ _
  have readStart : readNode.nr 18 = s.nr 18 := (readFixed 18 (by decide)).trans (rFixed 18 (by decide))
  have rep : b.nr 15 = words.1 := by
    rw [found, readStart, show readNode.nr 7 = index from indexAt, show readNode.nm = s.nm from rNat] <;> rfl
  have endpointA : b.nr 16 = old.endpointA :=
    (fFixed 16 (by decide)).trans ((readFixed 16 (by decide)).trans (congrArg MatchingCycleChild.endpointA row))
  have endpointB : b.nr 17 = old.endpointB :=
    (fFixed 17 (by decide)).trans ((readFixed 17 (by decide)).trans (congrArg MatchingCycleChild.endpointB row))
  have bCursor : b.nr 47 = s.nr 47 :=
    (fFixed 47 (by decide)).trans ((readFixed 47 (by decide)).trans (rFixed 47 (by decide)))
  have bOne : b.nr 9 = 1 := (fFixed 9 (by decide)).trans ((readFixed 9 (by decide)).trans advanceOne)
  let write := {b with pc := 0}
  obtain ⟨t, writes, ready, cursor, effect, naturalReal, naturalRr, fixed⟩ :=
    writeMatchingExpansionPathTriple_spec write rfl fLive bOne
  refine ⟨_, _, reads.append (moves.append (finds.append writes)), by omega, ready, ?_, cursor.trans (by rw [bCursor]),
    ?_, (naturalReal.trans fReal).trans rReal, (naturalRr.trans fRr).trans rRr⟩
  · exact (fixed 7 (by decide)).trans ((fFixed 7 (by decide)).trans indexAt)
  · change t.nm = _
    rw [effect]
    change writeExpansionTripleWords b.nm (b.nr 47) (b.nr 15, b.nr 16, b.nr 17) = _
    rw [fNat, show readNode.nm = s.nm from rNat, bCursor, rep, endpointA, endpointB] <;> rfl

private theorem writeExpansionPathBackward_spec {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0) :
    let index := expansionPreviousIndex (s.nr 19) (s.nr 7)
    let row := matchingCycleChildAt s.nm (s.nr 18 + 4 * index)
    let words := (row.representative, row.endpointB, row.endpointA)
    ∃ t steps, BlockRuns writeExpansionPathBackward steps s t ∧ steps ≤ 22 ∧ t.halted = false ∧
      t.nr 7 = index ∧ t.nr 47 = s.nr 47 + 3 ∧ t.nm = writeExpansionTripleWords s.nm (s.nr 47) words ∧
      t.rm = s.rm ∧ t.rr = s.rr := by
  intro index row words
  let prev := {s with pc := 4, nr := Function.update s.nr 7 index}
  obtain ⟨retreatSteps, retreatBound, retreats⟩ := retreatMatchingCycleIndexBlock_spec s entry running one zero
  let readNode := {prev with pc := 0}
  have before (r : ℕ) (outside : r ≠ 7) : readNode.nr r = s.nr r := Function.update_of_ne outside _ _
  have indexAt : readNode.nr 7 = index := by simp [readNode, prev]
  obtain ⟨a, reads, rLive, found, rNat, rReal, rRr, rFixed⟩ :=
    readMatchingCycleChild_spec readNode rfl running ((before 9 (by decide)).trans one)
  have asRow : readMatchingCycleChildValue a = row := by
    rw [found, before 18 (by decide), indexAt] <;> rfl
  let swap : List ArithmeticInstruction := [.natAdd 6 16 23, .natAdd 16 17 23, .natAdd 17 6 23]
  let swapEntry := {a with pc := 0}
  let b := (arithmeticStep swap)^[3] swapEntry
  have zeroAt : a.nr 23 = 0 := (rFixed 23 (by decide)).trans ((before 23 (by decide)).trans zero)
  have swapped : b.pc = swap.length ∧ b.halted = false ∧ b.nm = a.nm ∧ b.rm = a.rm ∧ b.rr = a.rr ∧
      b.nr 16 = a.nr 17 ∧ b.nr 17 = a.nr 16 := by
    simp [swap, swapEntry, b, zeroAt, rLive, arithmeticStep, Function.iterate_succ_apply']
  have swaps : BlockRuns swap 3 swapEntry b := BlockRuns.of_running_exit rfl swapped.2.1 swapped.1
  have keeps (r : ℕ) (outside : r ∉ [6, 16, 17]) : b.nr r = a.nr r :=
    arithmeticRun_keeps_from_destination_list _ (by decide) outside swapEntry 3
  have oneAt : b.nr 9 = 1 := (keeps 9 (by decide)).trans ((rFixed 9 (by decide)).trans ((before 9 (by decide)).trans one))
  have cursorAt : b.nr 47 = s.nr 47 :=
    (keeps 47 (by decide)).trans ((rFixed 47 (by decide)).trans (before 47 (by decide)))
  let write := {b with pc := 0}
  obtain ⟨t, writes, ready, cursor, effect, real, rr, fixed⟩ :=
    writeMatchingExpansionPathTriple_spec write rfl swapped.2.1 oneAt
  refine ⟨_, _, retreats.append (reads.append (swaps.append writes)), by omega, ready, ?_,
    cursor.trans (by rw [cursorAt]), ?_, (real.trans swapped.2.2.2.1).trans rReal,
    (rr.trans swapped.2.2.2.2.1).trans rRr⟩
  · exact (fixed 7 (by decide)).trans ((keeps 7 (by decide)).trans ((rFixed 7 (by decide)).trans indexAt))
  · change t.nm = _
    rw [effect]
    change writeExpansionTripleWords b.nm (b.nr 47) (b.nr 15, b.nr 16, b.nr 17) = _
    have rep : a.nr 15 = row.representative := congrArg MatchingCycleChild.representative asRow
    have endpointA : a.nr 16 = row.endpointA := congrArg MatchingCycleChild.endpointA asRow
    have endpointB : a.nr 17 = row.endpointB := congrArg MatchingCycleChild.endpointB asRow
    rw [swapped.2.2.1, rNat, cursorAt, keeps 15 (by decide), rep,
      swapped.2.2.2.2.2.1, swapped.2.2.2.2.2.2, endpointB, endpointA] <;> rfl

theorem writeExpansionArcStep_spec {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0)
    (inside : s.nr 7 < s.nr 19) :
    ∃ t steps, BlockRuns (branchOnAtMost 45 23 writeExpansionPathForward writeExpansionPathBackward) steps s t ∧
      steps ≤ 25 ∧ t.halted = false ∧ t.nr 7 = expansionNextRegistryIndex s ∧ t.nr 47 = s.nr 47 + 3 ∧
      t.nm = writeExpansionTripleWords s.nm (s.nr 47) (expansionNextTriple s) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ expansionEmitterStepScratch → t.nr r = s.nr r := by
  have fixed {t : ArithmeticState} {ticks : ℕ}
      (run : BlockRuns (branchOnAtMost 45 23 writeExpansionPathForward writeExpansionPathBackward) ticks s t)
      (r : ℕ) (outside : r ∉ expansionEmitterStepScratch) : t.nr r = s.nr r := by
    rw [← run.run]
    exact arithmeticRun_keeps_from_destination_list expansionEmitterStepScratch (by decide) outside s ticks
  by_cases forward : s.nr 45 ≤ s.nr 23
  · obtain ⟨t, steps, body, bound, ready, index, cursor, effect, real, rr⟩ :=
      writeExpansionPathForward_spec entry running one inside
    have ran := branchOnAtMost_left 45 23 writeExpansionPathForward writeExpansionPathBackward
      entry running forward body ready
    refine ⟨_, _, ran, by omega, ready, index.trans (if_pos forward).symm, cursor, ?_, real, rr, fixed ran⟩
    change t.nm = _
    rw [effect, expansionNextTriple, if_pos forward, expansionNextRegistryIndex, if_pos forward] <;> rfl
  · obtain ⟨t, steps, body, bound, ready, index, cursor, effect, real, rr⟩ :=
      writeExpansionPathBackward_spec entry running one zero
    have ran := branchOnAtMost_right 45 23 writeExpansionPathForward writeExpansionPathBackward
      entry running (Nat.lt_of_not_ge forward) body ready
    refine ⟨_, _, ran, by omega, ready, index.trans (if_neg forward).symm, cursor, ?_, real, rr, fixed ran⟩
    change t.nm = _
    rw [effect, expansionNextTriple, if_neg forward, expansionNextRegistryIndex, if_neg forward] <;> rfl

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionEmitterStep

/-! matching/MatchingExpansionEmitter.lean -/
section RppSource_MatchingExpansionEmitter
namespace VehicleRoutingSurvey.Routing

def expansionEmissionIndex (s : ArithmeticState) (i : ℕ) : ℕ :=
  (if s.nr 45 ≤ s.nr 23 then s.nr 81 + i else s.nr 81 + s.nr 19 - i) % s.nr 19

def expansionEmittedTriple (s : ArithmeticState) (i : ℕ) : ℕ × ℕ × ℕ :=
  let row := matchingCycleChildAt s.nm (s.nr 18 + 4 * expansionEmissionIndex s i)
  if i = 0 then (row.representative, s.nr 43, s.nr 44)
  else if s.nr 45 ≤ s.nr 23 then
    let edge := matchingCycleChildAt s.nm (s.nr 18 + 4 * expansionEmissionIndex s (i - 1))
    (row.representative, edge.endpointA, edge.endpointB)
  else (row.representative, row.endpointB, row.endpointA)



theorem expansionTripleAt_write (memory : ℕ → ℕ) (address : ℕ) (words : ℕ × ℕ × ℕ) :
    expansionTripleAt (writeExpansionTripleWords memory address words) address = words := by
  rcases words with ⟨a, b, c⟩
  simp (disch := omega) [expansionTripleAt, writeExpansionTripleWords, Function.update_of_ne]

theorem writeExpansionTripleWords_outside (memory : ℕ → ℕ) (address : ℕ) (words : ℕ × ℕ × ℕ)
    {a : ℕ} (outside : a < address ∨ address + 3 ≤ a) :
    writeExpansionTripleWords memory address words a = memory a := by
  simp (disch := omega) [writeExpansionTripleWords, Function.update_of_ne]

private theorem expansionEmissionIndex_start {s : ArithmeticState} (entryWithin : s.nr 81 < s.nr 19) :
    expansionEmissionIndex s 0 = s.nr 81 := by
  by_cases forward : s.nr 45 ≤ s.nr 23 <;>
    simp [expansionEmissionIndex, forward, Nat.mod_eq_of_lt entryWithin]

private theorem predecessor_mod {m a : ℕ} (positive : 0 < m) (nonzero : 0 < a) :
    expansionPreviousIndex m (a % m) = (a - 1) % m := by
  by_cases atStart : a % m = 0
  · have contains : m ≤ a := by
      by_contra! tooSmall
      rw [Nat.mod_eq_of_lt tooSmall] at atStart
      omega
    have multiple : (a - m) % m = 0 := (Nat.mod_eq_sub_mod contains).symm.trans atStart
    have tail : m - 1 < m := by omega
    rw [expansionPreviousIndex, if_pos atStart, show a - 1 = (a - m) + (m - 1) by omega,
      ← Nat.mod_add_mod, multiple, Nat.zero_add, Nat.mod_eq_of_lt tail]
  · have enough : 1 ≤ a % m := by omega
    rw [expansionPreviousIndex, if_neg atStart]
    exact Nat.mod_sub_of_le enough

theorem expansionEmissionIndex_succ {s : ArithmeticState} {i : ℕ} (within : i < s.nr 19) :
    (if s.nr 45 ≤ s.nr 23 then (expansionEmissionIndex s i + 1) % s.nr 19
      else expansionPreviousIndex (s.nr 19) (expansionEmissionIndex s i)) = expansionEmissionIndex s (i + 1) := by
  by_cases forward : s.nr 45 ≤ s.nr 23
  · simp [expansionEmissionIndex, forward, Nat.add_assoc]
  · rw [if_neg forward]
    change expansionPreviousIndex (s.nr 19)
      ((if s.nr 45 ≤ s.nr 23 then s.nr 81 + i else s.nr 81 + s.nr 19 - i) % s.nr 19) = _
    rw [if_neg forward, predecessor_mod (Nat.zero_lt_of_lt within) (by omega),
      expansionEmissionIndex, if_neg forward, show s.nr 81 + s.nr 19 - i - 1 = s.nr 81 + s.nr 19 - (i + 1) by omega]

private theorem prepareExpansionPathFirst_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 23 = 0) :
    ∃ t, BlockRuns prepareExpansionPathFirst 5 s t ∧ t.halted = false ∧
      t.nr 7 = s.nr 81 ∧ t.nr 47 = s.nr 86 ∧ t.nr 94 = s.nr 86 ∧ t.nr 16 = s.nr 43 ∧ t.nr 17 = s.nr 44 ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [7, 16, 17, 47, 94] → t.nr r = s.nr r := by
  let t := (arithmeticStep prepareExpansionPathFirst)^[5] s
  have ready : t.halted = false := by
    simp [t, prepareExpansionPathFirst, arithmeticStep, Function.iterate_succ_apply', entry, running]
  have exit : t.pc = prepareExpansionPathFirst.length := by
    simp [t, prepareExpansionPathFirst, arithmeticStep, Function.iterate_succ_apply', entry, running]
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
  | intro r safe
    exact arithmeticRun_keeps_from_destination_list [7, 16, 17, 47, 94] (by decide) safe s 5
  | simp [t, prepareExpansionPathFirst, arithmeticStep, Function.iterate_succ_apply', entry, running, zero]

def expansionEmitterScratch : List ℕ := [0, 6, 7, 15, 16, 17, 24, 25, 47, 94]

private structure ExpansionEmissionState (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  ready : s.halted = false
  index : s.nr 24 = i
  current : s.nr 7 = expansionEmissionIndex initial i
  base : s.nr 94 = initial.nr 86
  cursor : s.nr 47 = initial.nr 86 + 3 * (i + 1)
  written : ∀ j ≤ i, expansionTripleAt s.nm (initial.nr 86 + 3 * j) = expansionEmittedTriple initial j
  natural : ∀ a, (a < initial.nr 86 ∨ initial.nr 86 + 3 * (i + 1) ≤ a) → s.nm a = initial.nm a
  real : s.rm = initial.rm
  realRegisters : s.rr = initial.rr
  fixed : ∀ r, r ∉ expansionEmitterScratch → s.nr r = initial.nr r

/-- Emit the ordered path triples from the physical cycle without altering
the persistent registry. Backward steps reverse the original edge orientation. -/
theorem emitMatchingExpansionPath_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0)
    (entryWithin : s.nr 81 < s.nr 19) (arcWithin : s.nr 46 < s.nr 19)
    (pathBelowCycle : s.nr 86 + 3 * (s.nr 46 + 1) ≤ s.nr 18) :
    ∃ t steps, BlockRuns emitMatchingExpansionPath steps s t ∧ t.halted = false ∧
      steps ≤ 28 * s.nr 46 + 17 ∧ t.nr 94 = s.nr 86 ∧
      (∀ j ≤ s.nr 46, expansionTripleAt t.nm (t.nr 94 + 3 * j) = expansionEmittedTriple s j) ∧
      (∀ a, (a < s.nr 86 ∨ s.nr 86 + 3 * (s.nr 46 + 1) ≤ a) → t.nm a = s.nm a) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ expansionEmitterScratch → t.nr r = s.nr r := by
  obtain ⟨a, prepares, aReady, aIndex, aCursor, aBase, aFirst, aSecond, aNat, aReal, aRr, aFixed⟩ :=
    prepareExpansionPathFirst_spec entry running zero
  let read := {a with pc := 0}
  obtain ⟨b, reads, bReady, found, bNat, bReal, bRr, bFixed⟩ := readExpansionRepresentative_spec (s := read) rfl aReady
  let write := {b with pc := 0}
  have bOne : b.nr 9 = 1 := (bFixed 9 (by decide)).trans ((aFixed 9 (by decide)).trans one)
  obtain ⟨c, first, cReady, nextCursor, firstEffect, cReal, cRr, cFixed⟩ :=
    writeMatchingExpansionPathTriple_spec write rfl bReady bOne
  let loop := {c with pc := 0}
  have bCursor : b.nr 47 = s.nr 86 := (bFixed 47 (by decide)).trans aCursor
  have headWords : b.nr 15 = (expansionEmittedTriple s 0).1 := by
    rw [found, show read.nm = s.nm from aNat, show read.nr 7 = s.nr 81 from aIndex,
      show read.nr 18 = s.nr 18 from aFixed 18 (by decide)]
    simp [expansionEmittedTriple, expansionEmissionIndex_start entryWithin, matchingCycleChildAt]
  have headMemory : c.nm = writeExpansionTripleWords s.nm (s.nr 86) (expansionEmittedTriple s 0) := by
    rw [firstEffect]
    change writeExpansionTripleWords b.nm (b.nr 47) (b.nr 15, b.nr 16, b.nr 17) = _
    rw [bNat.trans aNat, bCursor, headWords, (bFixed 16 (by decide)).trans aFirst, (bFixed 17 (by decide)).trans aSecond]
    simp [expansionEmittedTriple]
  let inv := ExpansionEmissionState s
  have initial : inv 0 {loop with pc := 0, nr := Function.update loop.nr 24 0} := by
    refine ⟨rfl, cReady, by simp, ?_, ?_, ?_, ?_, ?_, (cReal.trans bReal).trans aReal,
      (cRr.trans bRr).trans aRr, ?_⟩
    · have reg : c.nr 7 = s.nr 81 := (cFixed 7 (by decide)).trans ((bFixed 7 (by decide)).trans aIndex)
      simpa [loop, expansionEmissionIndex_start entryWithin] using reg
    · have reg : c.nr 94 = s.nr 86 := (cFixed 94 (by decide)).trans ((bFixed 94 (by decide)).trans aBase)
      simpa [loop] using reg
    · have reg : c.nr 47 = s.nr 86 + 3 := nextCursor.trans (by rw [bCursor])
      simpa [loop] using reg
    · intro j bounded
      have origin : j = 0 := by omega
      subst j
      change expansionTripleAt c.nm (s.nr 86 + 3 * 0) = _
      rw [headMemory, Nat.mul_zero, Nat.add_zero, expansionTripleAt_write]
    · intro addr outside
      change c.nm addr = _
      rw [headMemory, writeExpansionTripleWords_outside _ _ _ (by omega)]
    · intro r safe
      have notIndex : r ≠ 24 := fun eq => safe (eq.symm ▸ (by decide : (24 : ℕ) ∈ expansionEmitterScratch))
      change Function.update c.nr 24 0 r = s.nr r
      rw [Function.update_of_ne notIndex]
      exact ((cFixed r (by simp [expansionEmitterScratch] at safe ⊢; omega)).trans
        (bFixed r (by simp [expansionEmitterScratch] at safe ⊢; omega))).trans
        (aFixed r (by simp [expansionEmitterScratch] at safe ⊢; omega))
  have control (i : ℕ) (m : ArithmeticState) (h : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 24 = i ∧ m.nr 46 = s.nr 46 :=
    ⟨h.entry, h.ready, h.index, h.fixed 46 (by decide)⟩
  have next (i : ℕ) (within : i < s.nr 46) (m : ArithmeticState) (h : inv i m) :
      ∃ t steps, steps ≤ 25 ∧
        BlockRuns (branchOnAtMost 45 23 writeExpansionPathForward writeExpansionPathBackward) steps m t ∧
        t.halted = false ∧ inv (i + 1) {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)} := by
    have modBound : expansionEmissionIndex s i < s.nr 19 := Nat.mod_lt _ (Nat.zero_lt_of_lt entryWithin)
    have inCycle : m.nr 7 < m.nr 19 := by rw [h.current, h.fixed 19 (by decide)]; exact modBound
    obtain ⟨t, steps, runs, bound, ready, moved, advanced, effect, real, rr, fixed⟩ :=
      writeExpansionArcStep_spec h.entry h.ready ((h.fixed 9 (by decide)).trans one)
        ((h.fixed 23 (by decide)).trans zero) inCycle
    have nextAt : expansionNextRegistryIndex m = expansionEmissionIndex s (i + 1) := by
      rw [expansionNextRegistryIndex, h.fixed 45 (by decide), h.fixed 23 (by decide), h.current, h.fixed 19 (by decide)]
      exact expansionEmissionIndex_succ (within.trans arcWithin)
    have lookup (j : ℕ) : matchingCycleChildAt m.nm (s.nr 18 + 4 * j) =
        matchingCycleChildAt s.nm (s.nr 18 + 4 * j) := by
      unfold matchingCycleChildAt
      have later (l : ℕ) : s.nr 86 + 3 * (i + 1) ≤ s.nr 18 + 4 * j + l := by omega
      rw [h.natural (s.nr 18 + 4 * j) (Or.inr (by omega)),
        h.natural _ (Or.inr (later 1)), h.natural _ (Or.inr (later 2)), h.natural _ (Or.inr (later 3))]
    have words : expansionNextTriple m = expansionEmittedTriple s (i + 1) := by
      rw [expansionNextTriple, expansionEmittedTriple, h.fixed 18 (by decide), h.fixed 45 (by decide),
        h.fixed 23 (by decide), h.current, nextAt, lookup, lookup]
      simp [show i + 1 ≠ 0 by omega]
    have memory : t.nm = writeExpansionTripleWords m.nm (s.nr 86 + 3 * (i + 1)) (expansionEmittedTriple s (i + 1)) := by
      rw [effect, h.cursor, words]
    refine ⟨t, steps, bound, runs, ready, rfl, ready, ?_, ?_, ?_, ?_, ?_, ?_, real.trans h.real,
      rr.trans h.realRegisters, ?_⟩
    · simp [fixed 24 (by decide), fixed 9 (by decide), h.index, h.fixed 9 (by decide), one]
    · have reg := moved.trans nextAt
      simpa using reg
    · exact (fixed 94 (by decide)).trans h.base
    · change t.nr 47 = _
      rw [advanced, h.cursor]
      omega
    · intro j written
      change expansionTripleAt t.nm _ = _
      by_cases latest : j = i + 1
      · subst j
        rw [memory, expansionTripleAt_write]
      · have earlier : j ≤ i := by omega
        rw [memory]
        unfold expansionTripleAt
        rw [writeExpansionTripleWords_outside _ _ _ (Or.inl (by omega)),
          writeExpansionTripleWords_outside _ _ _ (Or.inl (by omega)),
          writeExpansionTripleWords_outside _ _ _ (Or.inl (by omega))]
        exact h.written j earlier
    · intro addr outside
      change t.nm addr = _
      rw [memory, writeExpansionTripleWords_outside _ _ _ (by omega)]
      exact h.natural addr (by omega)
    · intro r untouched
      have notIndex : r ≠ 24 := fun eq => untouched (eq.symm ▸ (by decide : (24 : ℕ) ∈ expansionEmitterScratch))
      change Function.update t.nr 24 (t.nr 24 + t.nr 9) r = s.nr r
      rw [Function.update_of_ne notIndex]
      exact (fixed r (by simp [expansionEmitterStepScratch, expansionEmitterScratch] at untouched ⊢; omega)).trans
        (h.fixed r untouched)
  obtain ⟨last, actual, final, bound, steps⟩ := countedLoopFromZero_bounded 9 24 46 (s.nr 46) 25
    (branchOnAtMost 45 23 writeExpansionPathForward writeExpansionPathBackward) inv (s := loop) rfl cReady initial control next
  refine ⟨_, _, prepares.append (reads.append (first.append steps)), final.ready, by omega, final.base,
    ?_, final.natural, final.real, final.realRegisters, final.fixed⟩
  intro j written
  change expansionTripleAt last.nm (last.nr 94 + 3 * j) = _
  rw [final.base]
  exact final.written j written

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionEmitter

/-! matching/TightBlossomRematch.lean -/
section RppSource_TightBlossomRematch
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



/-- A simple cycle is tight if its edges are tight, including the wraparound edge. -/
def CycleEdgesTight {n : ℕ} (vertices : List (Fin n)) (tight : Sym2 (Fin n) → Prop) : Prop :=
  ∀ i (hi : i < vertices.length),
    tight s(vertices[i], vertices[(i + 1) % vertices.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi)))







end VehicleRoutingSurvey.Routing
end RppSource_TightBlossomRematch

/-! matching/TightBlossomExpansion.lean -/
section RppSource_TightBlossomExpansion
namespace VehicleRoutingSurvey.Routing

private theorem closed_chain_of_tight_cycle {n : ℕ} {vertices : List (Fin n)} {base : Fin n}
    {tight : Sym2 (Fin n) → Prop} (head : vertices.head? = some base)
    (cycle : CycleEdgesTight vertices tight) : (vertices ++ [base]).IsChain (fun a b => tight s(a, b)) := by
  have chain : vertices.IsChain (fun a b => tight s(a, b)) := by
    apply List.isChain_iff_getElem.mpr
    intro i next
    simpa only [Nat.mod_eq_of_lt next] using cycle i (by omega)
  refine chain.append (List.IsChain.singleton _) ?_
  intro last hLast first hFirst
  have lastEq : vertices.getLast? = some last := hLast
  have firstEq : base = first := by simpa only [List.head?_cons, Option.mem_some_iff] using hFirst
  subst first
  have positive := List.length_pos_of_mem (List.mem_of_getLast? lastEq)
  have lastIndex : vertices.length - 1 < vertices.length := by omega
  have wrap : (vertices.length - 1 + 1) % vertices.length = 0 := by
    rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
  have wrapped : vertices[(vertices.length - 1 + 1) % vertices.length]'(Nat.mod_lt _ positive) =
      vertices[0]'positive := getElem_congr_idx wrap
  have firstValue : vertices[0] = base := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem positive] at head
    exact Option.some.inj head
  have lastValue : vertices[vertices.length - 1] = last := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem lastIndex] at lastEq
    exact Option.some.inj lastEq
  simpa only [wrapped, firstValue, lastValue] using cycle (vertices.length - 1) lastIndex



theorem blossomExpansionPath_spec {n : ℕ} {vertices : List (Fin n)} {base : Fin n} {entry : ℕ}
    (head : vertices.head? = some base) (entryIndex : entry < vertices.length)
    (distinct : vertices.Nodup) (odd : Odd vertices.length)
    (tight : Sym2 (Fin n) → Prop) (cycle : CycleEdgesTight vertices tight) :
    let path := blossomExpansionPath base vertices entry
    path.head? = some vertices[entry] ∧ path.getLast? = some base ∧ path.Nodup ∧ Odd path.length ∧
      path.IsChain (fun a b => tight s(a, b)) := by
  have closed := closed_chain_of_tight_cycle head cycle
  dsimp only [blossomExpansionPath]
  by_cases evenEntry : entry % 2 = 0
  · rw [if_pos evenEntry]
    have linear : vertices.IsChain (fun a b => tight s(a, b)) := closed.left_of_append
    have forward := linear.take (entry + 1)
    refine ⟨?_, ?_, List.nodup_reverse.mpr (List.Nodup.sublist (List.take_sublist _ _) distinct), ?_, ?_⟩
    · simp [List.head?_reverse, List.getLast?_take, List.getElem?_eq_getElem entryIndex]
    · simp [List.getLast?_reverse, List.head?_take, head]
    · rw [Nat.odd_iff, List.length_reverse, List.length_take, Nat.min_eq_left (by omega)]
      omega
    · apply List.isChain_reverse.mpr
      exact forward.imp (fun _ _ h => Sym2.eq_swap ▸ h)
  · rw [if_neg evenEntry]
    have notZero : entry ≠ 0 := fun equal => evenEntry (equal.symm ▸ rfl)
    have beforeLast : base ∉ vertices.drop entry := by
      obtain ⟨tail, shape⟩ := List.head?_eq_some_iff.mp head
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero notZero
      have notTail : base ∉ tail := (List.nodup_cons.mp (shape ▸ distinct)).1
      rw [shape, List.drop_succ_cons]
      exact fun h => notTail ((List.drop_sublist _ _).subset h)
    refine ⟨?_, by simp, ?_, ?_, ?_⟩
    · simp [List.head?_append, List.getElem?_eq_getElem entryIndex]
    · refine List.nodup_append.mpr ⟨List.Nodup.sublist (List.drop_sublist _ _) distinct, by simp, ?_⟩
      intro a ha b hb equal
      have hbBase : b = base := by simpa only [List.mem_singleton] using hb
      exact beforeLast (hbBase ▸ equal ▸ ha)
    · rw [Nat.odd_iff, List.length_append, List.length_drop]
      simp only [List.length_cons, List.length_nil]
      have oddSize := Nat.odd_iff.mp odd
      omega
    · rw [← List.drop_append_of_le_length entryIndex.le]
      exact closed.drop entry

theorem alternatingEdges_append_even {α : Type*} (left right : List α)
    (even : left.length % 2 = 0) : alternatingEdges (left ++ right) =
      alternatingEdges left ++ alternatingEdges right := by
  induction left using List.twoStepInduction with
  | nil => rfl
  | singleton a => simp at even
  | cons_cons a b rest ih _ =>
    have restEven : rest.length % 2 = 0 := by
      simp only [List.length_cons] at even
      omega
    simpa only [List.cons_append, alternatingEdges] using congrArg (List.cons s(a, b)) (ih restEven)

theorem alternatingEdges_reverse_even {α : Type*} (vertices : List α)
    (even : vertices.length % 2 = 0) : alternatingEdges vertices.reverse = (alternatingEdges vertices).reverse := by
  induction vertices using List.twoStepInduction with
  | nil => rfl
  | singleton a => simp at even
  | cons_cons a b rest ih _ =>
    have restEven : rest.length % 2 = 0 := by
      simp only [List.length_cons] at even
      omega
    have reverseEven : rest.reverse.length % 2 = 0 := by simpa only [List.length_reverse] using restEven
    calc
      _ = alternatingEdges (rest.reverse ++ [b, a]) := by simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      _ = (alternatingEdges rest).reverse ++ [s(b, a)] := by
        simp only [alternatingEdges_append_even _ _ reverseEven, ih restEven, alternatingEdges]
      _ = _ := by simp only [alternatingEdges, List.reverse_cons, Sym2.eq_swap (a := b) (b := a)]

private theorem alternatingEdges_split_even {α : Type*} (vertices : List α) (i : ℕ)
    (within : i ≤ vertices.length) (even : i % 2 = 0) :
    alternatingEdges vertices = alternatingEdges (vertices.take i) ++ alternatingEdges (vertices.drop i) := by
  calc
    _ = alternatingEdges (vertices.take i ++ vertices.drop i) :=
      congrArg alternatingEdges (List.take_append_drop i vertices).symm
    _ = _ := alternatingEdges_append_even _ _ (by simpa only [List.length_take, Nat.min_eq_left within] using even)

/-- The restored route starts with an old matched edge and follows old matched edges at
alternate positions. The final base remains attached to its original external mate. -/
theorem blossomExpansionPath_uses_old_pairs {α : Type*} (base : α) (tail : List α)
    (entry : ℕ) (within : entry < (base :: tail).length) (tailEven : tail.length % 2 = 0) :
    ∀ e ∈ alternatingEdges (blossomExpansionPath base (base :: tail) entry), e ∈ alternatingEdges tail := by
  have single : alternatingEdges [base] = [] := rfl
  intro e he
  by_cases even : entry % 2 = 0
  · have entryBound : entry ≤ tail.length := by
      simp only [List.length_cons] at within
      omega
    have evenTake : (tail.take entry).length % 2 = 0 := by
      simpa only [List.length_take, Nat.min_eq_left entryBound] using even
    have evenReversed : (tail.take entry).reverse.length % 2 = 0 := by
      simpa only [List.length_reverse] using evenTake
    rw [blossomExpansionPath, if_pos even, List.take_succ_cons, List.reverse_cons,
      alternatingEdges_append_even _ _ evenReversed, single, List.append_nil,
      alternatingEdges_reverse_even _ evenTake] at he
    rw [alternatingEdges_split_even tail entry entryBound even]
    exact List.mem_append_left _ (List.mem_reverse.mp he)
  · have positive : entry ≠ 0 := by intro zero; exact even (zero.symm ▸ rfl)
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero positive
    have evenDrop : i % 2 = 0 := by omega
    have iBound : i ≤ tail.length := by
      simp only [List.length_cons] at within
      omega
    have evenRemaining : (tail.drop i).length % 2 = 0 := by
      rw [List.length_drop]
      omega
    rw [blossomExpansionPath, if_neg even, List.drop_succ_cons,
      alternatingEdges_append_even _ _ evenRemaining, single, List.append_nil] at he
    rw [alternatingEdges_split_even tail i iBound evenDrop]
    exact List.mem_append_right _ he

end VehicleRoutingSurvey.Routing
end RppSource_TightBlossomExpansion

/-! matching/MatchingExpansionRotation.lean -/
section RppSource_MatchingExpansionRotation
namespace VehicleRoutingSurvey.Routing









def matchingExpansionPhysicalPath {α : Type*} (cycle : List α) (entry base : Fin cycle.length) : List α :=
  List.ofFn (fun i : Fin (expansionArcLength cycle.length entry.val base.val + 1) =>
    cycle[expansionArcIndex cycle.length entry.val base.val i.val]'(Nat.mod_lt _ (Nat.zero_lt_of_lt entry.isLt)))

@[simp] theorem matchingExpansionPhysicalPath_length {α : Type*} (cycle : List α) (entry base : Fin cycle.length) :
    (matchingExpansionPhysicalPath cycle entry base).length = expansionArcLength cycle.length entry.val base.val + 1 := by
  simp [matchingExpansionPhysicalPath]

theorem matchingExpansionPhysicalPath_get {α : Type*} (cycle : List α) (entry base : Fin cycle.length)
    (i : ℕ) (within : i < (matchingExpansionPhysicalPath cycle entry base).length) :
    (matchingExpansionPhysicalPath cycle entry base)[i] =
    cycle[expansionArcIndex cycle.length entry.val base.val i]'(Nat.mod_lt _ (Nat.zero_lt_of_lt entry.isLt)) := by
  simp only [matchingExpansionPhysicalPath, List.getElem_ofFn]

private theorem expansion_rotation_offsets {m e b : ℕ} (entryWithin : e < m) (baseWithin : b < m) :
    let r := expansionEntryFromBase m e b
    let d := expansionForwardArcDistance m e b
    (r + b = e ∨ r + b = e + m) ∧ ((r = 0 ∧ d = 0) ∨ r + d = m) ∧ d < m := by
  intro r d
  by_cases forward : e ≤ b
  · have distance : d = b - e := by simp [d, expansionForwardArcDistance, forward]
    by_cases atBase : e = b
    · have offset : r = 0 := by
        dsimp [r, expansionEntryFromBase]
        rw [atBase, show b + m - b = m by omega, Nat.mod_self]
      omega
    · have offset : r = e + m - b := by
        exact Nat.mod_eq_of_lt (by omega)
      omega
  · have distance : d = m - (e - b) := by simp [d, expansionForwardArcDistance, forward]
    have offset : r = e - b := by
      dsimp [r, expansionEntryFromBase]
      rw [show e + m - b = (e - b) + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The modulo-indexed physical route is the abstract even expansion path
in the cycle rotated to begin at its current base. -/
theorem matchingExpansionPhysicalPath_eq_rotated {α : Type*} (cycle : List α)
    (entry base : Fin cycle.length) (odd : Odd cycle.length) :
    matchingExpansionPhysicalPath cycle entry base = blossomExpansionPath cycle[base.val]
      (cycle.rotate base.val) (expansionEntryFromBase cycle.length entry.val base.val) := by
  let m := cycle.length
  let b := base.val
  let e := entry.val
  let r := expansionEntryFromBase m e b
  let d := expansionForwardArcDistance m e b
  let rotated := cycle.rotate b
  have entryWithin : e < m := entry.isLt
  have baseWithin : b < m := base.isLt
  have positive : 0 < m := Nat.zero_lt_of_lt entryWithin
  have relative : r < m := Nat.mod_lt _ positive
  have rotatedLength : rotated.length = m := List.length_rotate _ _
  obtain ⟨offset, distance, distanceWithin⟩ := expansion_rotation_offsets entryWithin baseWithin
  change r + b = e ∨ r + b = e + m at offset
  change (r = 0 ∧ d = 0) ∨ r + d = m at distance
  change d < m at distanceWithin
  have oddLength : m % 2 = 1 := Nat.odd_iff.mp odd
  have forwardIndex (i : ℕ) : (e + i) % m = (r + i + b) % m := by
    rcases offset with same | wrapped
    · rw [show r + i + b = e + i by omega]
    · rw [show r + i + b = (e + i) + m by omega, Nat.add_mod_right]
  have backwardIndex (i : ℕ) (within : i ≤ r) : (e + m - i) % m = (r - i + b) % m := by
    rcases offset with same | wrapped
    · rw [show e + m - i = (r - i + b) + m by omega, Nat.add_mod_right]
    · rw [show e + m - i = r - i + b by omega]
  change matchingExpansionPhysicalPath cycle entry base = blossomExpansionPath cycle[base.val] rotated r
  by_cases evenOffset : r % 2 = 0
  · have size : expansionArcLength m e b = r := by
      change (if d % 2 = 0 then d else m - d) = r
      rcases distance with ⟨origin, zero⟩ | around
      · simp [origin, zero]
      · have oddDistance : ¬(d % 2 = 0) := by omega
        rw [if_neg oddDistance]
        omega
    have index (i : ℕ) (within : i ≤ r) : expansionArcIndex m e b i = (r - i + b) % m := by
      change (if d % 2 = 0 then e + i else e + m - i) % m = _
      by_cases evenDistance : d % 2 = 0
      · have noAdvance : r = 0 := by
          rcases distance with ⟨origin, _⟩ | around
          · exact origin
          · omega
        have atStart : i = 0 := by omega
        rw [if_pos evenDistance, atStart, Nat.add_zero, Nat.sub_zero]
        exact forwardIndex 0
      · rw [if_neg evenDistance]
        exact backwardIndex i within
    have takes : (rotated.take (r + 1)).length = r + 1 := by
      rw [List.length_take, rotatedLength, Nat.min_eq_left (by omega)]
    rw [blossomExpansionPath, if_pos evenOffset]
    apply List.ext_getElem
    · rw [matchingExpansionPhysicalPath_length, show expansionArcLength cycle.length entry.val base.val = r from size,
        List.length_reverse, takes]
    · intro i physicalWithin _
      have stepWithin : i ≤ r := by
        rw [matchingExpansionPhysicalPath_length, show expansionArcLength cycle.length entry.val base.val = r from size]
          at physicalWithin
        omega
      rw [matchingExpansionPhysicalPath_get, List.getElem_reverse, List.getElem_take]
      dsimp only [rotated]
      rw [List.getElem_rotate]
      apply getElem_congr_idx
      have takesExact : (List.take (r + 1) (cycle.rotate base.val)).length = r + 1 := takes
      rw [takesExact, show r + 1 - 1 - i = r - i by omega]
      exact index i stepWithin
  · have around : r + d = m := by
      rcases distance with ⟨origin, _⟩ | yes
      · exact (evenOffset (origin.symm ▸ rfl)).elim
      · exact yes
    have evenDistance : d % 2 = 0 := by omega
    have size : expansionArcLength m e b = d := if_pos evenDistance
    have index (i : ℕ) : expansionArcIndex m e b i = (e + i) % m := by
      exact congrArg (fun j => j % m) (show (if d % 2 = 0 then e + i else e + m - i) = e + i from if_pos evenDistance)
    have drops : (rotated.drop r).length = d := by
      rw [List.length_drop, rotatedLength]
      omega
    rw [blossomExpansionPath, if_neg evenOffset]
    apply List.ext_getElem
    · rw [matchingExpansionPhysicalPath_length, show expansionArcLength cycle.length entry.val base.val = d from size,
        List.length_append, List.length_singleton, drops]
    · intro i within _
      have bounded : i ≤ d := by
        rw [matchingExpansionPhysicalPath_length, show expansionArcLength cycle.length entry.val base.val = d from size]
          at within
        omega
      rw [matchingExpansionPhysicalPath_get]
      have indexed : cycle[expansionArcIndex cycle.length entry.val base.val i]'(Nat.mod_lt _ positive) =
          cycle[(e + i) % m]'(Nat.mod_lt _ positive) := getElem_congr_idx (index i)
      apply indexed.trans
      by_cases beforeBase : i < d
      · rw [List.getElem_append_left (show i < (rotated.drop r).length by rwa [drops]), List.getElem_drop]
        dsimp only [rotated]
        rw [List.getElem_rotate]
        exact getElem_congr_idx (forwardIndex i)
      · have final : i = d := by omega
        rw [List.getElem_append_right (show (rotated.drop r).length ≤ i by rw [drops, final]), List.getElem_singleton]
        apply getElem_congr_idx
        rw [forwardIndex i, show r + i + b = m + b by omega, Nat.add_mod_left, Nat.mod_eq_of_lt baseWithin]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionRotation

/-! matching/ExpansionArcRAM.lean -/
section RppSource_ExpansionArcRAM
namespace VehicleRoutingSurvey.Routing







theorem expansionArcLength_lt {m e b : ℕ} (eWithin : e < m) (bWithin : b < m) :
    expansionArcLength m e b < m := by
  let d := expansionForwardArcDistance m e b
  have dSmall : d < m := by
    by_cases later : e ≤ b <;> simp [d, expansionForwardArcDistance, later] <;> omega
  change (if d % 2 = 0 then d else m - d) < m
  split <;> omega

theorem prepareMatchingExpansionArc_spec {s : ArithmeticState} {e b : ℕ}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (eWithin : e < expansionRegisteredCycleLength s) (bWithin : b < expansionRegisteredCycleLength s)
    (entryUnique : ∀ i < expansionRegisteredCycleLength s,
      s.nm (expansionRegisteredCycleBase s + 4 * i) = expansionEntryChild s ↔ i = e)
    (baseUnique : ∀ i < expansionRegisteredCycleLength s,
      s.nm (expansionRegisteredCycleBase s + 4 * i) = s.nr 97 ↔ i = b)
    (odd : Odd (expansionRegisteredCycleLength s)) (small : expansionRegisteredCycleLength s ≤ s.nr 55)
    (room : s.nr 86 + 3 * expansionRegisteredCycleLength s ≤ expansionRegisteredCycleBase s) :
    ∃ t steps, BlockRuns prepareMatchingExpansionArc steps s t ∧ t.halted = false ∧
      steps ≤ 59 * s.nr 55 + 61 ∧ ExpansionArcReady s t e b := by
  let m := expansionRegisteredCycleLength s
  let d := expansionForwardArcDistance m e b
  let len := expansionArcLength m e b
  have lenSmall : len < m := expansionArcLength_lt eWithin bWithin
  obtain ⟨l, locateSteps, located, lLive, locateCost, loc⟩ :=
    locateMatchingExpansionEndpoints_spec entry running one eWithin bWithin entryUnique baseUnique
  let c := {l with pc := 0}
  have cOne : c.nr 9 = 1 := (loc.fixed 9 (by decide)).trans one
  have cZero : c.nr 23 = 0 := loc.zero
  have cLength : c.nr 19 = m := loc.cycleLength
  have cEntry : c.nr 81 = e := loc.entrySlot
  have cBase : c.nr 82 = b := loc.baseSlot
  have cDim : c.nr 55 = s.nr 55 := loc.fixed 55 (by decide)
  have cForward : expansionForwardDistance c = d := by
    simp only [expansionForwardDistance, d, expansionForwardArcDistance, cLength, cEntry, cBase]
  obtain ⟨q, choiceSteps, choiceCost, chosen, qLive, direction, distance, pairs, qNat, qReal, qRr⟩ :=
    chooseMatchingExpansionDirection_spec c rfl lLive cOne cZero
      (by rwa [cEntry, cLength]) (by rwa [cBase, cLength]) (by rwa [cLength]) (by rwa [cLength, cDim])
  let p := {q with pc := 0}
  have choiceKeeps (r : ℕ) (safe : r ∉ [0, 6, 24, 45, 46, 47, 49, 95]) : p.nr r = c.nr r := by
    change q.nr r = c.nr r
    rw [← chosen.run]
    exact arithmeticRun_keeps_from_destination_list [0, 6, 24, 45, 46, 47, 49, 95] (by decide) safe c choiceSteps
  have pLen : p.nr 46 = len := by
    change q.nr 46 = _
    rw [distance, cForward, cLength]
    simp only [Nat.even_iff, len, expansionArcLength, d]
  have pChoice : p.nr 45 ≤ p.nr 23 ↔ d % 2 = 0 := by
    change q.nr 45 ≤ p.nr 23 ↔ _
    simp only [direction, cForward, choiceKeeps 23 (by decide), cZero, Nat.even_iff]
    by_cases h : d % 2 = 0 <;> simp [h]
  have pBase : p.nr 86 = s.nr 86 := (choiceKeeps 86 (by decide)).trans (loc.fixed 86 (by decide))
  have pCycle : p.nr 18 = expansionRegisteredCycleBase s := (choiceKeeps 18 (by decide)).trans loc.cycleStart
  have pSize : p.nr 19 = m := (choiceKeeps 19 (by decide)).trans cLength
  have pEntry : p.nr 81 = e := (choiceKeeps 81 (by decide)).trans cEntry
  have pNat : p.nm = s.nm := qNat.trans loc.natural
  have emitted (i : ℕ) : expansionEmittedTriple p i = expansionArcWords s e b i := by
    have pWitnessA : p.nr 43 = (expansionOldParentWitness s).1 :=
      (choiceKeeps 43 (by decide)).trans (congrArg Prod.fst loc.oldWitness)
    have pWitnessB : p.nr 44 = (expansionOldParentWitness s).2 :=
      (choiceKeeps 44 (by decide)).trans (congrArg Prod.snd loc.oldWitness)
    simp only [expansionEmittedTriple, expansionArcWords, expansionEmissionIndex, expansionArcIndex,
      pWitnessA, pWitnessB, pCycle, pEntry, pChoice, pSize, pNat, d] <;> rfl
  obtain ⟨t, emitSteps, emittedRun, tLive, emitCost, tPath, words, nat, real, rr, emitKeeps⟩ :=
    emitMatchingExpansionPath_spec (s := p) rfl qLive ((choiceKeeps 9 (by decide)).trans cOne)
      ((choiceKeeps 23 (by decide)).trans cZero) (by rwa [pEntry, pSize]) (by rwa [pLen, pSize])
      (by rw [pBase, pLen, pCycle]; omega)
  have pPairs : 2 * p.nr 95 = len := pairs.symm.trans pLen
  rw [pLen] at emitCost
  rw [cDim] at choiceCost
  have exactArc : ExpansionArcReady s t e b := by
    refine ⟨(emitKeeps 18 (by decide)).trans pCycle, (emitKeeps 19 (by decide)).trans pSize, tPath.trans pBase,
    ?_, ?_, ?_, ?_, ?_, real.trans (qReal.trans loc.real), rr.trans (qRr.trans loc.realRegisters), ?_⟩
    · rw [emitKeeps 95 (by decide)]
      exact pPairs
    · exact (emitKeeps 96 (by decide)).trans ((choiceKeeps 96 (by decide)).trans loc.parent)
    · exact (emitKeeps 98 (by decide)).trans ((choiceKeeps 98 (by decide)).trans loc.mate)
    · intro i within
      exact (words i (pLen.symm ▸ within)).trans (emitted i)
    · intro a away
      apply (nat a ?_).trans (congrFun pNat a)
      rwa [pBase, pLen]
    · intro r safe
      exact (emitKeeps r (by simp [expansionArcScratch, expansionEmitterScratch] at safe ⊢; omega)).trans
        ((choiceKeeps r (by simp [expansionArcScratch] at safe ⊢; omega)).trans
          (loc.fixed r (by simp [expansionArcScratch] at safe ⊢; omega)))
  exact ⟨_, _, located.append (chosen.append emittedRun), tLive, by omega,
    exactArc.cycleStart, exactArc.cycleLength, exactArc.pathBase, exactArc.arcLength, exactArc.parent,
    exactArc.mate, exactArc.words, exactArc.natural, exactArc.real, exactArc.realRegisters, exactArc.fixed⟩

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionArcRAM

/-! matching/ExpansionParentModel.lean -/
section RppSource_ExpansionParentModel
namespace VehicleRoutingSurvey.Routing

private theorem growPairs_parent_chain {α : Type*} [DecidableEq α]
    {forest : AlternatingForestState α} {source : α} (vertices : List α) (distinct : vertices.Nodup)
    (even : vertices.length % 2 = 0) :
    let grown := forest.growPairs source vertices
    (source :: vertices).IsChain (fun p c => (grown.1.role c).parent = some p) ∧
      (source :: vertices).getLast? = some grown.2 := by
  induction vertices using List.twoStepInduction generalizing forest source with
  | nil => simp [AlternatingForestState.growPairs]
  | singleton a => simp at even
  | cons_cons inner outer rest ih _ =>
    obtain ⟨⟨different, noInner⟩, noOuter, restDistinct⟩ :
        (inner ≠ outer ∧ inner ∉ rest) ∧ outer ∉ rest ∧ rest.Nodup := by
      simpa only [List.nodup_cons, List.mem_cons, not_or] using distinct
    have restEven : rest.length % 2 = 0 := by simp only [List.length_cons] at even; omega
    let first := forest.grow source inner outer
    let grown := first.growPairs outer rest
    obtain ⟨links, last⟩ := ih (forest := first) (source := outer) restDistinct restEven
    have innerRole : grown.1.role inner = .inner source :=
      ((AlternatingForestState.growPairs_preserves (state := first) (source := outer) rest noInner).1).trans
        (by simp [first, AlternatingForestState.grow])
    have outerRole : grown.1.role outer = .outer (some inner) :=
      ((AlternatingForestState.growPairs_preserves (state := first) (source := outer) rest noOuter).1).trans
        (by simp [first, AlternatingForestState.grow, different.symm])
    change (source :: inner :: outer :: rest).IsChain (fun p c => (grown.1.role c).parent = some p) ∧
      (source :: inner :: outer :: rest).getLast? = some grown.2
    refine ⟨List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr ⟨?_, links⟩⟩, ?_⟩
    · simp [innerRole, AlternatingForestRole.parent]
    · simp [outerRole, AlternatingForestRole.parent]
    · simpa only [List.getLast?_cons_cons] using last

/-- Each new parent points to its predecessor on the expansion route,
including the original blossom base at the end. -/
theorem AlternatingForestState.expandAlong_parent_chain {α : Type*} [DecidableEq α]
    (forest : AlternatingForestState α) (source base : α) (vertices : List α)
    (distinct : vertices.Nodup) (avoidsBase : base ∉ vertices) (even : vertices.length % 2 = 0) :
    (source :: (vertices ++ [base])).IsChain
      (fun p c => ((forest.expandAlong source base vertices).role c).parent = some p) := by
  let raised : AlternatingForestState α :=
    { forest with
      depth := fun v => forest.depth v + (if forest.depth base ≤ forest.depth v then vertices.length else 0) }
  let grown := raised.growPairs source vertices
  let expanded := forest.expandAlong source base vertices
  have roleAt (v : α) : expanded.role v = Function.update grown.1.role base (.inner grown.2) v := rfl
  obtain ⟨links, final⟩ := growPairs_parent_chain (forest := raised) (source := source) vertices distinct even
  have carried : (source :: vertices).IsChain (fun p c => (expanded.role c).parent = some p) := by
    apply links.imp_of_mem_tail_imp
    intro p c _ inside linked
    have different : c ≠ base := fun eq => avoidsBase (eq ▸ inside)
    rw [roleAt, Function.update_of_ne different]
    exact linked
  rw [← List.cons_append]
  apply carried.append (List.isChain_singleton base)
  intro p pIsLast v vIsBase
  have finalAt : (source :: vertices).getLast? = some grown.2 := final
  have atEnd : grown.2 = p := by simpa only [finalAt, Option.mem_some_iff] using pIsLast
  have atBase : base = v := by simpa only [List.head?_cons, Option.mem_some_iff] using vIsBase
  subst p
  subst v
  simp [roleAt, AlternatingForestRole.parent]

theorem AlternatingForestState.expandAlong_keeps_role {α : Type*} [DecidableEq α]
    (forest : AlternatingForestState α) (source base v : α) (vertices : List α)
    (outside : v ∉ vertices) (different : v ≠ base) :
    (forest.expandAlong source base vertices).role v = forest.role v := by
  let raised : AlternatingForestState α :=
    { forest with
      depth := fun w => forest.depth w + (if forest.depth base ≤ forest.depth w then vertices.length else 0) }
  let grown := raised.growPairs source vertices
  change Function.update grown.1.role base (.inner grown.2) v = forest.role v
  rw [Function.update_of_ne different]
  exact (AlternatingForestState.growPairs_preserves (state := raised) (source := source) vertices outside).1

/-- The recorded original endpoints are oriented from each parent to its
new child. They remain tight using the post-step original dual values. -/
def ExpansionParentEdges {k : ℕ} (rep : Fin k → Fin k) (tight : Sym2 (Fin k) → Prop) (parent : Fin k) :
    List (ExpansionPathRecord k) → Prop
  | [] => True
  | record :: rest => (rep record.edge.1, rep record.edge.2) = (parent, record.vertex) ∧
    tight s(record.edge.1, record.edge.2) ∧ ExpansionParentEdges rep tight record.vertex rest

theorem ExpansionParentEdges.sound {k : ℕ} {rep : Fin k → Fin k} {tight : Sym2 (Fin k) → Prop}
    {forest : AlternatingForestState (Fin k)} {parent : Fin k} {records : List (ExpansionPathRecord k)}
    (edges : ExpansionParentEdges rep tight parent records)
    (chain : (parent :: records.map ExpansionPathRecord.vertex).IsChain
      (fun p c => (forest.role c).parent = some p)) {record : ExpansionPathRecord k} (inPath : record ∈ records)
    {recordParent : Fin k} (attached : (forest.role record.vertex).parent = some recordParent) :
    (rep record.edge.1, rep record.edge.2) = (recordParent, record.vertex) ∧ tight s(record.edge.1, record.edge.2) := by
  induction records generalizing parent with
  | nil => simp at inPath
  | cons first rest ih =>
    have links := List.isChain_cons_cons.mp chain
    rcases List.mem_cons.mp inPath with rfl | later
    · have same : recordParent = parent := Option.some.inj (attached.symm.trans links.1)
      subst recordParent
      exact ⟨edges.1, edges.2.1⟩
    · exact ih edges.2.2 links.2 later

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionParentModel

/-! matching/ExpansionPathEncoding.lean -/
section RppSource_ExpansionPathEncoding
namespace VehicleRoutingSurvey.Routing

def ExpansionPathRecord.words {k : ℕ} (record : ExpansionPathRecord k) : ℕ × ℕ × ℕ :=
  (record.vertex.val, record.edge.1.val, record.edge.2.val)

/-- Indexed triples and the sequential path decoder describe the same memory. -/
theorem ExpansionPathMemory.ofIndexed {k : ℕ} {memory : ℕ → ℕ} {base : ℕ}
    (records : List (ExpansionPathRecord k))
    (words : ∀ (i : ℕ) (within : i < records.length),
      expansionTripleAt memory (base + 3 * i) = records[i].words) :
    ExpansionPathMemory memory base records := by
  induction records generalizing base with
  | nil => exact True.intro
  | cons first rest ih =>
    have head := words 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero, expansionTripleAt,
      ExpansionPathRecord.words, Prod.mk.injEq] at head
    refine ⟨head.1, head.2.1, head.2.2, ih ?_⟩
    intro i within
    have next := words (i + 1) (by simp only [List.length_cons]; omega)
    simpa only [show base + 3 + 3 * i = base + 3 * (i + 1) by omega,
      List.getElem_cons_succ] using next

/-- An entering edge and a valid edge between each successive pair of path
records suffice for the recursive oriented-parent invariant. -/
theorem ExpansionParentEdges.ofIndexed {k : ℕ} {rep : Fin k → Fin k}
    {tight : Sym2 (Fin k) → Prop} {source : Fin k} (records : List (ExpansionPathRecord k))
    (first : ∀ r, records.head? = some r →
      (rep r.edge.1, rep r.edge.2) = (source, r.vertex) ∧ tight s(r.edge.1, r.edge.2))
    (next : ∀ (i : ℕ) (within : i + 1 < records.length),
      let before := records[i]'(by omega)
      let current := records[i + 1]
      (rep current.edge.1, rep current.edge.2) = (before.vertex, current.vertex) ∧
        tight s(current.edge.1, current.edge.2)) :
    ExpansionParentEdges rep tight source records := by
  induction records generalizing source with
  | nil => exact True.intro
  | cons head rest ih =>
    obtain ⟨orientation, tightHead⟩ := first head rfl
    refine ⟨orientation, tightHead, ih ?_ ?_⟩
    · intro r found
      cases rest with
      | nil => simp at found
      | cons nextRecord tail =>
        have eq : nextRecord = r := Option.some.inj found
        subst r
        exact next 0 (by simp)
    · intro i within
      exact next (i + 1) (by simp only [List.length_cons]; omega)

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionPathEncoding

/-! matching/ExpansionArcRecords.lean -/
section RppSource_ExpansionArcRecords
namespace VehicleRoutingSurvey.Routing

private def expansionArcRecordEdge {k : ℕ} {m : ℕ} (edge : Fin m → Fin k × Fin k)
    (entry base : Fin m) (incoming : Fin k × Fin k) (i : ℕ) : Fin k × Fin k :=
  let index := fun j => ⟨expansionArcIndex m entry.val base.val j,
    Nat.mod_lt _ (Nat.zero_lt_of_lt entry.isLt)⟩
  if i = 0 then incoming
  else if expansionForwardArcDistance m entry.val base.val % 2 = 0 then edge (index (i - 1))
  else (edge (index i)).swap

/-- The records describe the physical traversal and use the original endpoints
on its crossing edges. Registry index zero need not be the current base. -/
def expansionArcRecords {k : ℕ} (cycle : List (Fin k))
    (edge : Fin cycle.length → Fin k × Fin k) (entry base : Fin cycle.length)
    (incoming : Fin k × Fin k) : List (ExpansionPathRecord k) :=
  List.ofFn (fun i : Fin (expansionArcLength cycle.length entry.val base.val + 1) =>
    ⟨cycle[expansionArcIndex cycle.length entry.val base.val i.val]'(Nat.mod_lt _ (Nat.zero_lt_of_lt entry.isLt)),
      expansionArcRecordEdge edge entry base incoming i.val⟩)

@[simp] theorem expansionArcRecords_length {k : ℕ} (cycle : List (Fin k))
    (edge : Fin cycle.length → Fin k × Fin k) (entry base : Fin cycle.length) (incoming : Fin k × Fin k) :
    (expansionArcRecords cycle edge entry base incoming).length =
      expansionArcLength cycle.length entry.val base.val + 1 := by
  simp [expansionArcRecords]

theorem expansionArcRecords_vertices {k : ℕ} (cycle : List (Fin k))
    (edge : Fin cycle.length → Fin k × Fin k) (entry base : Fin cycle.length) (incoming : Fin k × Fin k) :
    (expansionArcRecords cycle edge entry base incoming).map ExpansionPathRecord.vertex =
      matchingExpansionPhysicalPath cycle entry base := by
  simp only [expansionArcRecords, matchingExpansionPhysicalPath, List.map_ofFn]
  rfl

/-- The persistent cycle rows couple each child with the oriented original edge
from that child to the next, modulo the physical cycle length. -/
structure ExpansionCycleWitnessRows {k : ℕ} (s : ArithmeticState) (cycle : List (Fin k))
    (edges : Fin cycle.length → Fin k × Fin k) : Prop where
  length : expansionRegisteredCycleLength s = cycle.length
  records : ∀ i : Fin cycle.length,
    let row := matchingCycleChildAt s.nm (expansionRegisteredCycleBase s + 4 * i.val)
    row.representative = cycle[i.val].val ∧
      (row.endpointA, row.endpointB) = ((edges i).1.val, (edges i).2.val)

theorem ExpansionArcReady.encodedRecords {k : ℕ} {s t : ArithmeticState}
    {cycle : List (Fin k)} {edges : Fin cycle.length → Fin k × Fin k}
    {entry base : Fin cycle.length} {incoming : Fin k × Fin k}
    (arc : ExpansionArcReady s t entry.val base.val) (cycleRows : ExpansionCycleWitnessRows s cycle edges)
    (witness : expansionOldParentWitness s = (incoming.1.val, incoming.2.val)) :
    ExpansionPathMemory t.nm (t.nr 94) (expansionArcRecords cycle edges entry base incoming) := by
  apply ExpansionPathMemory.ofIndexed
  intro i inside
  have allowed : i ≤ expansionArcLength (expansionRegisteredCycleLength s) entry.val base.val := by
    rw [cycleRows.length]
    have h : i < expansionArcLength cycle.length entry.val base.val + 1 := by
      simpa only [expansionArcRecords_length] using inside
    omega
  rw [arc.words i allowed]
  let idx : ℕ → Fin cycle.length := fun j => ⟨expansionArcIndex cycle.length entry.val base.val j,
    Nat.mod_lt _ (Nat.zero_lt_of_lt entry.isLt)⟩
  have row (j : ℕ) := cycleRows.records (idx j)
  have owner (j : ℕ) : (matchingCycleChildAt s.nm
      (expansionRegisteredCycleBase s + 4 * expansionArcIndex cycle.length entry.val base.val j)).representative =
      cycle[(idx j).val].val := (row j).1
  have endpointA (j : ℕ) := congrArg Prod.fst (row j).2
  have endpointB (j : ℕ) := congrArg Prod.snd (row j).2
  change _ = (expansionArcRecords cycle edges entry base incoming)[i].words
  simp only [expansionArcWords, cycleRows.length, expansionArcRecords, List.getElem_ofFn,
    ExpansionPathRecord.words, expansionArcRecordEdge, owner, witness]
  by_cases first : i = 0
  · simp [first, idx]
  · by_cases forward : expansionForwardArcDistance cycle.length entry.val base.val % 2 = 0
    · simp only [first, forward, if_false, if_true]
      rw [show (matchingCycleChildAt s.nm (expansionRegisteredCycleBase s +
        4 * expansionArcIndex cycle.length entry.val base.val (i - 1))).endpointA = _ from endpointA (i - 1),
        show (matchingCycleChildAt s.nm (expansionRegisteredCycleBase s +
        4 * expansionArcIndex cycle.length entry.val base.val (i - 1))).endpointB = _ from endpointB (i - 1)] <;> rfl
    · simp only [first, forward, if_false, Prod.swap]
      rw [show (matchingCycleChildAt s.nm (expansionRegisteredCycleBase s +
        4 * expansionArcIndex cycle.length entry.val base.val i)).endpointA = _ from endpointA i,
        show (matchingCycleChildAt s.nm (expansionRegisteredCycleBase s +
        4 * expansionArcIndex cycle.length entry.val base.val i)).endpointB = _ from endpointB i] <;> rfl

/-- The chosen arc's consecutive edges point from each new parent to its child. -/
theorem expansionArcRecords_parentEdges {k : ℕ} {cycle : List (Fin k)}
    (edges : Fin cycle.length → Fin k × Fin k) (entry base : Fin cycle.length)
    (incoming : Fin k × Fin k) (source : Fin k) (rep : Fin k → Fin k)
    (tight : Sym2 (Fin k) → Prop)
    (incomingEdge : (rep incoming.1, rep incoming.2) = (source, cycle[entry.val]) ∧
      tight s(incoming.1, incoming.2))
    (cycleEdges : ∀ j : Fin cycle.length,
      (rep (edges j).1, rep (edges j).2) =
        (cycle[j.val], cycle[(j.val + 1) % cycle.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt j.isLt))) ∧
      tight s((edges j).1, (edges j).2)) :
    ExpansionParentEdges rep tight source (expansionArcRecords cycle edges entry base incoming) := by
  let m := cycle.length
  let index : ℕ → Fin m := fun j => ⟨expansionArcIndex m entry.val base.val j,
    Nat.mod_lt _ (Nat.zero_lt_of_lt entry.isLt)⟩
  let records := expansionArcRecords cycle edges entry base incoming
  have nonempty : 0 < records.length := by simp [records]
  have entryWithin : entry.val < m := entry.isLt
  have starts : (index 0).val = entry.val := by
    by_cases forward : expansionForwardArcDistance m entry.val base.val % 2 = 0 <;>
      simp [index, expansionArcIndex, forward, Nat.mod_eq_of_lt entryWithin]
  have words (i : ℕ) (within : i < records.length) : records[i] =
      ⟨cycle[(index i).val], expansionArcRecordEdge edges entry base incoming i⟩ := by
    simp only [records, expansionArcRecords, List.getElem_ofFn, index] <;> rfl
  apply ExpansionParentEdges.ofIndexed records
  · intro r found
    have same : records[0] = r := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem nonempty, Option.some.injEq] at found
      exact found
    have startNode : cycle[(index 0).val] = cycle[entry.val] := getElem_congr_idx starts
    have firstEdge : expansionArcRecordEdge edges entry base incoming 0 = incoming := by
      simp [expansionArcRecordEdge]
    rw [← same, words 0 nonempty, firstEdge, startNode]
    exact incomingEdge
  · intro i within
    have step : i + 1 < m := by
      have bound : expansionArcLength m entry.val base.val < m := expansionArcLength_lt entry.isLt base.isLt
      have len : records.length = expansionArcLength m entry.val base.val + 1 := by simp [records, m]
      omega
    dsimp only
    rw [words i (by omega), words (i + 1) within]
    change (rep (expansionArcRecordEdge edges entry base incoming (i + 1)).1,
        rep (expansionArcRecordEdge edges entry base incoming (i + 1)).2) =
      (cycle[(index i).val], cycle[(index (i + 1)).val]) ∧
      tight s((expansionArcRecordEdge edges entry base incoming (i + 1)).1,
        (expansionArcRecordEdge edges entry base incoming (i + 1)).2)
    by_cases forward : expansionForwardArcDistance m entry.val base.val % 2 = 0
    · have advance : ((index i).val + 1) % m = (index (i + 1)).val := by
        change (((if expansionForwardArcDistance m entry.val base.val % 2 = 0 then entry.val + i
          else entry.val + m - i) % m) + 1) % m = _
        simp only [forward, if_true, index, expansionArcIndex, Nat.mod_add_mod, Nat.add_assoc]
      have valid := cycleEdges (index i)
      have node : cycle[((index i).val + 1) % cycle.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt entry.isLt)) =
          cycle[(index (i + 1)).val] := getElem_congr_idx advance
      have oriented := valid.1.trans (congrArg (fun w => (cycle[(index i).val], w)) node)
      have even : expansionForwardArcDistance cycle.length entry.val base.val % 2 = 0 := forward
      have edgeEq : expansionArcRecordEdge edges entry base incoming (i + 1) = edges (index i) := by
        simp [expansionArcRecordEdge, even, index] <;> rfl
      rw [edgeEq]
      exact ⟨oriented, valid.2⟩
    · have retreat : ((index (i + 1)).val + 1) % m = (index i).val := by
        change (((if expansionForwardArcDistance m entry.val base.val % 2 = 0 then entry.val + (i + 1)
          else entry.val + m - (i + 1)) % m) + 1) % m = _
        simp only [forward, if_false, index, expansionArcIndex]
        rw [Nat.mod_add_mod, show entry.val + m - (i + 1) + 1 = entry.val + m - i by omega]
      have valid := cycleEdges (index (i + 1))
      have node : cycle[((index (i + 1)).val + 1) % cycle.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt entry.isLt)) =
          cycle[(index i).val] := getElem_congr_idx retreat
      have oriented := congrArg Prod.swap
        (valid.1.trans (congrArg (fun w => (cycle[(index (i + 1)).val], w)) node))
      have tightReverse : tight s((edges (index (i + 1))).2, (edges (index (i + 1))).1) := by
        simpa only [Sym2.eq_swap] using valid.2
      have odd : ¬expansionForwardArcDistance cycle.length entry.val base.val % 2 = 0 := forward
      have edgeEq : expansionArcRecordEdge edges entry base incoming (i + 1) = (edges (index (i + 1))).swap := by
        simp [expansionArcRecordEdge, odd, index] <;> rfl
      rw [edgeEq]
      exact ⟨oriented, tightReverse⟩

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionArcRecords

/-! matching/AlternatingBlossomExpansion.lean -/
section RppSource_AlternatingBlossomExpansion
namespace VehicleRoutingSurvey.Routing

private theorem blossomExpansionPath_subset {α : Type*} (base : α) (tail : List α) (entry : ℕ) :
    ∀ v ∈ blossomExpansionPath base (base :: tail) entry, v ∈ base :: tail := by
  intro v hv
  by_cases even : entry % 2 = 0
  · rw [blossomExpansionPath, if_pos even] at hv
    exact (List.take_sublist _ _).subset (List.mem_reverse.mp hv)
  · rw [blossomExpansionPath, if_neg even] at hv
    rcases List.mem_append.mp hv with kept | atBase
    · exact (List.drop_sublist _ _).subset kept
    · have equal : v = base := by simpa only [List.mem_singleton] using atBase
      exact List.mem_cons.mpr (Or.inl equal)



theorem AlternatingForestState.expandBlossom_valid {n : ℕ} {state : AlternatingForestState (Fin n)}
    {mate : Fin n → Option (Fin n)} {tight : Sym2 (Fin n) → Prop}
    (valid : state.valid mate (fun u v => tight s(u, v))) {source base : Fin n}
    (baseInner : state.role base = .inner source) (children : List (Fin n)) {entry : ℕ}
    (within : entry < (base :: children).length) (distinct : (base :: children).Nodup)
    (evenChildren : children.length % 2 = 0)
    (dormant : ∀ v ∈ children, state.role v = .unlabelled)
    (tightCycle : CycleEdgesTight (base :: children) tight)
    (tightEntry : tight s(source, (base :: children)[entry]))
    (childMates : ∀ a b, s(a, b) ∈ alternatingEdges children → mate a = some b ∧ mate b = some a) :
    (state.expandBlossom source base children entry).valid mate (fun a b => tight s(a, b)) := by
  have oddCycle : Odd (base :: children).length := by
    rw [Nat.odd_iff, List.length_cons]
    omega
  let path := blossomExpansionPath base (base :: children) entry
  obtain ⟨firstAt, endsAt, noRepeat, odd, chain⟩ :=
    blossomExpansionPath_spec rfl within distinct oddCycle tight tightCycle
  change path.head? = some (base :: children)[entry] at firstAt
  change path.getLast? = some base at endsAt
  obtain ⟨before, shape⟩ := List.getLast?_eq_some_iff.mp endsAt
  have beforeEq : path.dropLast = before := by simp [shape]
  have noRepeatBefore : (before ++ [base]).Nodup := shape ▸ noRepeat
  have evenBefore : before.length % 2 = 0 := by
    have oddSize : path.length % 2 = 1 := Nat.odd_iff.mp odd
    rw [shape, List.length_append] at oddSize
    simp at oddSize
    omega
  have newDormant : ∀ v ∈ before, state.role v = .unlabelled := by
    intro v hv
    have inPath : v ∈ path := shape.symm ▸ List.mem_append_left _ hv
    have notBase : v ≠ base := (List.nodup_append.mp noRepeatBefore).2.2 v hv base (by simp)
    exact dormant v ((List.mem_cons.mp (blossomExpansionPath_subset base children entry v inPath)).resolve_left notBase)
  have fullPath : (source :: (before ++ [base])).IsChain (fun u v => tight s(u, v)) := by
    rw [← shape]
    apply List.isChain_cons.mpr
    refine ⟨?_, chain⟩
    intro v hv
    have selected : (base :: children)[entry] = v := by simpa only [firstAt, Option.mem_some_iff] using hv
    exact selected ▸ tightEntry
  have internalPairs : ∀ a b, s(a, b) ∈ alternatingEdges before → mate a = some b ∧ mate b = some a := by
    intro a b pair
    apply childMates a b
    apply blossomExpansionPath_uses_old_pairs base children entry within evenChildren
    change s(a, b) ∈ alternatingEdges path
    rw [shape, alternatingEdges_append_even _ _ evenBefore]
    exact List.mem_append_left _ pair
  change (state.expandAlong source base path.dropLast).valid mate (fun u v => tight s(u, v))
  rw [beforeEq]
  exact expandAlong_valid valid baseInner before (List.nodup_append.mp noRepeatBefore).1 evenBefore
    newDormant fullPath internalPairs

end VehicleRoutingSurvey.Routing
end RppSource_AlternatingBlossomExpansion

/-! matching/MatchingExpansionRefinement.lean -/
section RppSource_MatchingExpansionRefinement
namespace VehicleRoutingSurvey.Routing

/-- The path producer has selected the correct arc and emitted its ordered
child and witness records, including the final record for the old base. -/
structure MatchingExpansionPathReady {k : ℕ} (s : ArithmeticState) (source base : Fin k)
    (children : List (Fin k)) (entry : ℕ) (records : List (ExpansionPathRecord k))
    (lastEdge : Fin k × Fin k) : Prop where
  layout : ExpansionForestFrame k (s.nr 51) (s.nr 90) (s.nr 94) s
  sourceAt : s.nr 96 = source.val
  baseAt : s.nr 97 = base.val
  pairs : records.length = s.nr 95 + s.nr 95
  encoded : ExpansionPathMemory s.nm (s.nr 94) (records ++ [⟨base, lastEdge⟩])
  followsCycle : records.map ExpansionPathRecord.vertex ++ [base] =
    blossomExpansionPath base (base :: children) entry



/-- An encoded cycle path refines the abstract blossom expansion and installs
oriented parent witnesses for later augmentation. Unaffected parents keep
their original witnesses. -/
theorem expandAlternatingForest_fromCycle {k : ℕ} {s : ArithmeticState}
    {forest : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)}
    {source base : Fin k} {children : List (Fin k)} {entryIndex : ℕ}
    {records : List (ExpansionPathRecord k)} {lastEdge : Fin k × Fin k}
    {tightRep tightOriginal : Sym2 (Fin k) → Prop} {rep : Fin k → Fin k}
    (path : MatchingExpansionPathReady s source base children entryIndex records lastEdge)
    (entry : s.pc = 0) (running : s.halted = false)
    (valid : forest.valid mate (fun a b => tightRep s(a, b)))
    (baseInner : forest.role base = .inner source)
    (within : entryIndex < (base :: children).length) (distinct : (base :: children).Nodup)
    (evenChildren : children.length % 2 = 0) (dormant : ∀ v ∈ children, forest.role v = .unlabelled)
    (tightCycle : CycleEdgesTight (base :: children) tightRep)
    (tightEntry : tightRep s(source, (base :: children)[entryIndex]))
    (childMates : ∀ a b, s(a, b) ∈ alternatingEdges children → mate a = some b ∧ mate b = some a)
    (encoding : AlternatingForestMemory forest (s.nr 51) s.nm)
    (newEdges : ExpansionParentEdges rep tightOriginal source (records ++ [⟨base, lastEdge⟩]))
    (retained : ∀ child parent : Fin k, child ∉ records.map ExpansionPathRecord.vertex ++ [base] →
      (forest.role child).parent = some parent → ∃ edge : Fin k × Fin k,
        matchingForestWitnessAt s.nm (s.nr 90) child.val = (edge.1.val, edge.2.val) ∧
        (rep edge.1, rep edge.2) = (parent, child) ∧ tightOriginal s(edge.1, edge.2)) :
    ∃ t steps, BlockRuns expandAlternatingForestBlock steps s t ∧ t.halted = false ∧
      steps ≤ 31 * k + 23 ∧ MatchingExpandedForest
        (forest.expandBlossom source base children entryIndex) mate tightRep tightOriginal rep s t := by
  let vertices := records.map ExpansionPathRecord.vertex
  let expanded := forest.expandBlossom source base children entryIndex
  let allRecords := records ++ [⟨base, lastEdge⟩]
  have allVertices : allRecords.map ExpansionPathRecord.vertex = vertices ++ [base] := by simp [allRecords, vertices]
  have oddCycle : Odd (base :: children).length := by
    rw [Nat.odd_iff, List.length_cons]
    omega
  have cycleShape : vertices ++ [base] = blossomExpansionPath base (base :: children) entryIndex := path.followsCycle
  obtain ⟨_, _, pathUnique, _, _⟩ := blossomExpansionPath_spec rfl within distinct oddCycle tightRep tightCycle
  have unique : (vertices ++ [base]).Nodup := cycleShape.symm ▸ pathUnique
  have avoids : base ∉ vertices := by
    intro found
    exact (List.nodup_append.mp unique).2.2 base found base (by simp) rfl
  have uniquePrefix : vertices.Nodup := (List.nodup_append.mp unique).1
  have prefixLength : vertices.length = s.nr 95 + s.nr 95 := by simpa [vertices] using path.pairs
  have evenPrefix : vertices.length % 2 = 0 := by rw [prefixLength]; omega
  have exactModel : forest.expandAlong source base vertices = expanded := by
    have routePrefix : vertices = (blossomExpansionPath base (base :: children) entryIndex).dropLast := by
      simpa using congrArg List.dropLast cycleShape
    rw [routePrefix]
    rfl
  obtain ⟨t, executes, ready, finished, recorded, keptWitness, keptNatural, keptReal, keptRr, keptRegisters⟩ :=
    expandAlternatingForestBlock_spec path.layout entry running path.sourceAt path.baseAt path.pairs uniquePrefix
      avoids baseInner encoding path.encoded
  have newForest : AlternatingForestMemory expanded (s.nr 51) t.nm := exactModel ▸ finished
  have newValid : expanded.valid mate (fun a b => tightRep s(a, b)) :=
    AlternatingForestState.expandBlossom_valid valid baseInner children within distinct evenChildren dormant
      tightCycle tightEntry childMates
  have parentChain : (source :: allRecords.map ExpansionPathRecord.vertex).IsChain
      (fun p c => (expanded.role c).parent = some p) := by
    rw [allVertices, ← exactModel]
    exact forest.expandAlong_parent_chain source base vertices uniquePrefix avoids evenPrefix
  have witness (child parent : Fin k) (link : (expanded.role child).parent = some parent) :
      ∃ edge : Fin k × Fin k,
        matchingForestWitnessAt t.nm (s.nr 90) child.val = (edge.1.val, edge.2.val) ∧
        (rep edge.1, rep edge.2) = (parent, child) ∧ tightOriginal s(edge.1, edge.2) := by
    by_cases active : child ∈ allRecords.map ExpansionPathRecord.vertex
    · obtain ⟨record, used, rfl⟩ := List.mem_map.mp active
      exact ⟨record.edge, recorded record used, newEdges.sound parentChain used link⟩
    · have outside : child ∉ vertices ++ [base] := by simpa only [allVertices] using active
      obtain ⟨awayPath, awayBase⟩ : child ∉ vertices ∧ child ≠ base := by
        simpa only [List.mem_append, List.mem_singleton, not_or] using outside
      have role : expanded.role child = forest.role child := exactModel ▸
        forest.expandAlong_keeps_role source base child vertices awayPath awayBase
      have previous := link
      rw [role] at previous
      obtain ⟨edge, remembered, oriented, tight⟩ := retained child parent outside previous
      exact ⟨edge, (keptWitness child awayBase awayPath).trans remembered, oriented, tight⟩
  have bounded : (vertices ++ [base]).length ≤ k := by simpa using unique.length_le_card
  have stepsBound : 9 * k + 44 * s.nr 95 + 23 ≤ 31 * k + 23 := by
    simp only [List.length_append, List.length_singleton] at bounded
    omega
  exact ⟨t, _, executes, ready, stepsBound,
    newForest, newValid, witness, keptNatural, keptReal, keptRr, keptRegisters⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionRefinement

/-! matching/MatchingExpansionHandoff.lean -/
section RppSource_MatchingExpansionHandoff
namespace VehicleRoutingSurvey.Routing

/-- Convert the parser's physical cycle positions and emitted node sequence
to the base-first expansion model consumed by the forest block. -/
theorem MatchingExpansionPathReady.ofPhysicalPath {k : ℕ} {s : ArithmeticState}
    {cycle : List (Fin k)} (entrySlot baseSlot : Fin cycle.length)
    {source base : Fin k} {children : List (Fin k)}
    {records : List (ExpansionPathRecord k)} {lastEdge : Fin k × Fin k}
    (odd : Odd cycle.length) (rotates : cycle.rotate baseSlot.val = base :: children)
    (layout : ExpansionForestFrame k (s.nr 51) (s.nr 90) (s.nr 94) s)
    (sourceAt : s.nr 96 = source.val) (baseAt : s.nr 97 = base.val)
    (pairCount : expansionArcLength cycle.length entrySlot.val baseSlot.val = 2 * s.nr 95)
    (encoded : ExpansionPathMemory s.nm (s.nr 94) (records ++ [⟨base, lastEdge⟩]))
    (physicalNodes : records.map ExpansionPathRecord.vertex ++ [base] =
      matchingExpansionPhysicalPath cycle entrySlot baseSlot) :
    MatchingExpansionPathReady s source base children
      (expansionEntryFromBase cycle.length entrySlot.val baseSlot.val) records lastEdge := by
  have count := congrArg List.length physicalNodes
  simp only [List.length_append, List.length_map, List.length_singleton, matchingExpansionPhysicalPath_length,
    pairCount] at count
  have head := List.head?_rotate baseSlot.isLt
  have baseNode : cycle[baseSlot.val] = base := by
    rw [rotates, List.head?_cons, List.getElem?_eq_getElem baseSlot.isLt, Option.some.injEq] at head
    exact head.symm
  refine ⟨layout, sourceAt, baseAt, by omega, encoded, ?_⟩
  rw [physicalNodes, matchingExpansionPhysicalPath_eq_rotated cycle entrySlot baseSlot odd, rotates, baseNode]



end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionHandoff

/-! matching/ExpansionArcHandoff.lean -/
section RppSource_ExpansionArcHandoff
namespace VehicleRoutingSurvey.Routing

/-- The typed handoff packages the emitted path and proves the orientation of
every original witness, ready for the arithmetic-RAM expansion. -/
theorem ExpansionArcReady.toForestPath {k : ℕ} {s t : ArithmeticState}
    {cycle : List (Fin k)} {edges : Fin cycle.length → Fin k × Fin k}
    (entrySlot baseSlot : Fin cycle.length) {incoming : Fin k × Fin k}
    {source base : Fin k} {children : List (Fin k)}
    {rep : Fin k → Fin k} {tightOriginal : Sym2 (Fin k) → Prop}
    (arc : ExpansionArcReady s t entrySlot.val baseSlot.val) (cycleRows : ExpansionCycleWitnessRows s cycle edges)
    (witness : expansionOldParentWitness s = (incoming.1.val, incoming.2.val))
    (incomingEdge : (rep incoming.1, rep incoming.2) = (source, cycle[entrySlot.val]) ∧
      tightOriginal s(incoming.1, incoming.2))
    (cycleEdges : ∀ j : Fin cycle.length,
      (rep (edges j).1, rep (edges j).2) =
        (cycle[j.val], cycle[(j.val + 1) % cycle.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt j.isLt))) ∧
      tightOriginal s((edges j).1, (edges j).2))
    (finishes : (matchingExpansionPhysicalPath cycle entrySlot baseSlot).getLast? = some base)
    (odd : Odd cycle.length) (rotates : cycle.rotate baseSlot.val = base :: children)
    (layout : ExpansionForestFrame k (t.nr 51) (t.nr 90) (t.nr 94) t)
    (sourceAt : t.nr 96 = source.val) (baseAt : s.nr 97 = base.val) :
    ∃ records lastEdge, MatchingExpansionPathReady t source base children
      (expansionEntryFromBase cycle.length entrySlot.val baseSlot.val) records lastEdge ∧
      ExpansionParentEdges rep tightOriginal source (records ++ [⟨base, lastEdge⟩]) := by
  let all := expansionArcRecords cycle edges entrySlot baseSlot incoming
  have nonempty : all ≠ [] := by
    have n : 0 < all.length := by simp [all]
    intro empty
    simp [empty] at n
  let last := all.getLast nonempty
  have tail : all.dropLast ++ [last] = all := List.dropLast_concat_getLast nonempty
  have finalVertex : last.vertex = base := by
    have output := congrArg List.getLast? (expansionArcRecords_vertices cycle edges entrySlot baseSlot incoming)
    rw [finishes, List.getLast?_map, List.getLast?_eq_some_getLast nonempty] at output
    exact Option.some.inj output
  have finalRecord : last = ⟨base, last.edge⟩ := by
    calc
      last = ⟨last.vertex, last.edge⟩ := by cases last; rfl
      _ = ⟨base, last.edge⟩ := congrArg (fun v => (⟨v, last.edge⟩ : ExpansionPathRecord k)) finalVertex
  have decomposed : all.dropLast ++ [⟨base, last.edge⟩] = all := by simpa only [← finalRecord] using tail
  have emitted : ExpansionPathMemory t.nm (t.nr 94) all := arc.encodedRecords cycleRows witness
  have oriented : ExpansionParentEdges rep tightOriginal source all :=
    expansionArcRecords_parentEdges edges entrySlot baseSlot incoming source rep tightOriginal incomingEdge cycleEdges
  refine ⟨all.dropLast, last.edge, ?_, decomposed.symm ▸ oriented⟩
  apply MatchingExpansionPathReady.ofPhysicalPath entrySlot baseSlot odd rotates layout sourceAt
    ((arc.fixed 97 (by decide)).trans baseAt)
  · simpa only [cycleRows.length] using arc.arcLength.symm
  · exact decomposed.symm ▸ emitted
  · have vertices := congrArg (List.map ExpansionPathRecord.vertex) decomposed
    have route := vertices.trans (expansionArcRecords_vertices cycle edges entrySlot baseSlot incoming)
    simpa only [List.map_append, List.map_cons, List.map_nil] using route

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionArcHandoff

/-! matching/ExpansionCommitRAM.lean -/
section RppSource_ExpansionCommitRAM
namespace VehicleRoutingSurvey.Routing



structure ExpansionPublicationLayout (s : ArithmeticState) : Prop where
  forestBelowRepresentatives : s.nr 51 + 3 * s.nr 55 ≤ s.nr 57
  representativesBelowScratch : s.nr 57 + s.nr 55 ≤ s.nr 79
  representativesBelowNodes : s.nr 57 + s.nr 55 ≤ s.nr 74
  nodesBelowWitnesses : s.nr 74 + s.nr 55 ≤ s.nr 90
  nodesBelowCycle : s.nr 74 + s.nr 55 ≤ s.nr 18

theorem MatchingExpandedForest.relocate {k : ℕ} {s t : ArithmeticState}
    {forest : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)}
    {tightRep tightOriginal : Sym2 (Fin k) → Prop} {rep : Fin k → Fin k}
    (expanded : MatchingExpandedForest forest mate tightRep tightOriginal rep s t) (offset : ℕ) :
    MatchingExpandedForest forest mate tightRep tightOriginal rep s (relocateState offset t) :=
  ⟨expanded.encoding, expanded.valid, expanded.edgeWitness, expanded.natural, expanded.real,
    expanded.realRegisters, expanded.fixed⟩

theorem commitMatchingExpansionBlock_spec {k : ℕ} {s : ArithmeticState}
    {forest : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)}
    {source base : Fin k} {children : List (Fin k)} {entryIndex : ℕ}
    {records : List (ExpansionPathRecord k)} {lastEdge : Fin k × Fin k}
    {tightRep tightOriginal : Sym2 (Fin k) → Prop} {rep : Fin k → Fin k}
    (path : MatchingExpansionPathReady s source base children entryIndex records lastEdge)
    (layout : ExpansionPublicationLayout s) (entry : s.pc = 0) (running : s.halted = false)
    (inRange : ∀ i < s.nr 19, (expansionCycleRow s i).representative < s.nr 55)
    (rowsDistinct : ∀ i < s.nr 19, ∀ j < s.nr 19,
      (expansionCycleRow s i).representative = (expansionCycleRow s j).representative → i = j)
    (small : s.nr 19 ≤ k)
    (valid : forest.valid mate (fun a b => tightRep s(a, b)))
    (baseInner : forest.role base = .inner source)
    (within : entryIndex < (base :: children).length) (distinct : (base :: children).Nodup)
    (evenChildren : children.length % 2 = 0) (dormant : ∀ v ∈ children, forest.role v = .unlabelled)
    (tightCycle : CycleEdgesTight (base :: children) tightRep)
    (tightEntry : tightRep s(source, (base :: children)[entryIndex]))
    (childMates : ∀ a b, s(a, b) ∈ alternatingEdges children → mate a = some b ∧ mate b = some a)
    (encoding : AlternatingForestMemory forest (s.nr 51) s.nm)
    (newEdges : ExpansionParentEdges rep tightOriginal source (records ++ [⟨base, lastEdge⟩]))
    (retained : ∀ child parent : Fin k, child ∉ records.map ExpansionPathRecord.vertex ++ [base] →
      (forest.role child).parent = some parent → ∃ edge : Fin k × Fin k,
        matchingForestWitnessAt s.nm (s.nr 90) child.val = (edge.1.val, edge.2.val) ∧
        (rep edge.1, rep edge.2) = (parent, child) ∧ tightOriginal s(edge.1, edge.2)) :
    ∃ t published steps, BlockRuns commitMatchingExpansionBlock steps s t ∧ t.halted = false ∧
      steps ≤ 55 * k + 27 ∧ ExpansionPublication s published ∧ MatchingExpandedForest
        (forest.expandBlossom source base children entryIndex) mate tightRep tightOriginal rep published t := by
  obtain ⟨p, publishes, pLive, representatives, nodes, natural, real, rr, fixed⟩ :=
    publishExpansionSplit_spec entry running path.layout.one layout.representativesBelowScratch
      layout.representativesBelowNodes layout.nodesBelowCycle inRange rowsDistinct
  let a := {p with pc := 0}
  have outer : ExpansionPublication s a := ⟨representatives, nodes, natural, real, rr, fixed⟩
  have above (address : ℕ) (safe : s.nr 90 ≤ address) : a.nm address = s.nm address := by
    have nodesBelow := layout.nodesBelowWitnesses
    have representativesBelow := layout.representativesBelowNodes
    exact natural address (Or.inr (by omega)) (fun j hj => by have := inRange j hj; omega)
  have below (address : ℕ) (safe : address < s.nr 57) : a.nm address = s.nm address := by
    have representativesBelow := layout.representativesBelowNodes
    exact natural address (Or.inl safe) (fun j _ => by omega)
  have roles : a.nr 51 = s.nr 51 := fixed 51 (by decide)
  have witnesses : a.nr 90 = s.nr 90 := fixed 90 (by decide)
  have aLayout : ExpansionForestFrame k (a.nr 51) (a.nr 90) (a.nr 94) a := by
    refine ⟨(fixed 55 (by decide)).trans path.layout.dimension, (fixed 9 (by decide)).trans path.layout.one,
      (fixed 14 (by decide)).trans path.layout.zero, rfl, ?_, ?_, rfl, rfl, ?_, ?_⟩
    · rw [roles, show a.nr 52 = _ from fixed 52 (by decide)]
      exact path.layout.parents
    · rw [roles, show a.nr 53 = _ from fixed 53 (by decide)]
      exact path.layout.depths
    · rw [roles, witnesses]
      exact path.layout.forestGap
    · rw [witnesses, show a.nr 94 = _ from fixed 94 (by decide)]
      exact path.layout.pathGap
  have aPath : MatchingExpansionPathReady a source base children entryIndex records lastEdge := by
    refine ⟨aLayout, (fixed 96 (by decide)).trans path.sourceAt,
      (fixed 97 (by decide)).trans path.baseAt, ?_, ?_, path.followsCycle⟩
    · rw [show a.nr 95 = _ from fixed 95 (by decide)]
      exact path.pairs
    · rw [show a.nr 94 = _ from fixed 94 (by decide)]
      apply path.encoded.preserved
      intro address after
      have gap := path.layout.pathGap
      exact above address (by omega)
  have aEncoding : AlternatingForestMemory forest (a.nr 51) a.nm := by
    intro v
    have range := v.isLt
    have belowRep := layout.forestBelowRepresentatives
    have dim := path.layout.dimension
    have here := encoding v
    rw [roles]
    exact ⟨(below _ (by omega)).trans here.1, (below _ (by omega)).trans here.2.1,
      (below _ (by omega)).trans here.2.2⟩
  have aRetained (child parent : Fin k) (outside : child ∉ records.map ExpansionPathRecord.vertex ++ [base])
      (linked : (forest.role child).parent = some parent) : ∃ edge : Fin k × Fin k,
      matchingForestWitnessAt a.nm (a.nr 90) child.val = (edge.1.val, edge.2.val) ∧
        (rep edge.1, rep edge.2) = (parent, child) ∧ tightOriginal s(edge.1, edge.2) := by
    obtain ⟨edge, remembered, oriented, tight⟩ := retained child parent outside linked
    refine ⟨edge, ?_, oriented, tight⟩
    have first := above (forestWitnessAddress (s.nr 90) child.val) (by simp [forestWitnessAddress])
    have second := above (forestWitnessAddress (s.nr 90) child.val + 1) (by unfold forestWitnessAddress; omega)
    rw [witnesses, matchingForestWitnessAt, first, second]
    exact remembered
  obtain ⟨t, forestSteps, grows, live, bound, expanded⟩ := expandAlternatingForest_fromCycle aPath rfl pLive
    valid baseInner within distinct evenChildren dormant tightCycle tightEntry childMates aEncoding newEdges aRetained
  have dim := path.layout.dimension
  exact ⟨_, a, _, publishes.append grows, live, by omega, outer, expanded.relocate _⟩

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionCommitRAM

/-! matching/MatchingExpansionAfterMembers.lean -/
section RppSource_MatchingExpansionAfterMembers
namespace VehicleRoutingSurvey.Routing



structure ExpansionCycleInput {k : ℕ} (s : ArithmeticState) (cycle : List (Fin k))
    (edges : Fin cycle.length → Fin k × Fin k) (entrySlot baseSlot : Fin cycle.length)
    (source base : Fin k) (children : List (Fin k)) (incoming : Fin k × Fin k) : Prop where
  rows : ExpansionCycleWitnessRows s cycle edges
  nodup : cycle.Nodup
  odd : Odd cycle.length
  rotates : cycle.rotate baseSlot.val = base :: children
  baseWord : s.nr 97 = base.val
  baseChild : cycle[baseSlot.val] = base
  entryChild : expansionEntryChild s = cycle[entrySlot.val].val
  parentWord : s.nm (s.nr 52 + s.nr 97) = source.val
  witness : expansionOldParentWitness s = (incoming.1.val, incoming.2.val)

structure ExpansionModelInput {k : ℕ} (s : ArithmeticState) (forest : AlternatingForestState (Fin k))
    (mate : Fin k → Option (Fin k)) (tightRep tightOriginal : Sym2 (Fin k) → Prop) (rep : Fin k → Fin k)
    (cycle : List (Fin k)) (edges : Fin cycle.length → Fin k × Fin k)
    (entrySlot baseSlot : Fin cycle.length) (source base : Fin k) (children : List (Fin k))
    (incoming : Fin k × Fin k) : Prop where
  encoding : AlternatingForestMemory forest (s.nr 51) s.nm
  valid : forest.valid mate (fun a b => tightRep s(a, b))
  baseInner : forest.role base = .inner source
  dormant : ∀ v ∈ children, forest.role v = .unlabelled
  tightCycle : CycleEdgesTight (base :: children) tightRep
  tightEntry : tightRep s(source, cycle[entrySlot.val])
  childMates : ∀ a b, s(a, b) ∈ alternatingEdges children → mate a = some b ∧ mate b = some a
  incomingEdge : (rep incoming.1, rep incoming.2) = (source, cycle[entrySlot.val]) ∧ tightOriginal s(incoming.1, incoming.2)
  cycleEdges : ∀ j : Fin cycle.length,
    (rep (edges j).1, rep (edges j).2) =
      (cycle[j.val], cycle[(j.val + 1) % cycle.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt j.isLt))) ∧
    tightOriginal s((edges j).1, (edges j).2)
  retained : ∀ child parent : Fin k, child ∉ matchingExpansionPhysicalPath cycle entrySlot baseSlot →
    (forest.role child).parent = some parent → ∃ edge : Fin k × Fin k,
      matchingForestWitnessAt s.nm (s.nr 90) child.val = (edge.1.val, edge.2.val) ∧
      (rep edge.1, rep edge.2) = (parent, child) ∧ tightOriginal s(edge.1, edge.2)

/-- Once the member map is available, the bytecode reads the registry, emits
the even arc, publishes the split, and installs the typed alternating forest. -/
theorem expandMatchingAfterMembersBlock_spec {k : ℕ} {s : ArithmeticState}
    {forest : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)}
    {tightRep tightOriginal : Sym2 (Fin k) → Prop} {rep : Fin k → Fin k}
    {cycle : List (Fin k)} {edges : Fin cycle.length → Fin k × Fin k}
    {entrySlot baseSlot : Fin cycle.length} {source base : Fin k} {children : List (Fin k)}
    {incoming : Fin k × Fin k} (entry : s.pc = 0) (running : s.halted = false)
    (layout : ExpansionInputLayout k s)
    (input : ExpansionCycleInput s cycle edges entrySlot baseSlot source base children incoming)
    (model : ExpansionModelInput s forest mate tightRep tightOriginal rep cycle edges entrySlot baseSlot
      source base children incoming) :
    ∃ t arc published steps, BlockRuns expandMatchingAfterMembersBlock steps s t ∧ t.halted = false ∧
      steps ≤ 114 * k + 88 ∧ ExpansionArcReady s arc entrySlot.val baseSlot.val ∧
      ExpansionPublication arc published ∧ MatchingExpandedForest
        (forest.expandBlossom source base children (expansionEntryFromBase cycle.length entrySlot.val baseSlot.val))
        mate tightRep tightOriginal rep published t := by
  have dimension := layout.dimension
  have cycleLength := input.rows.length
  have count : cycle.length ≤ k := by simpa using input.nodup.length_le_card
  have rows (i : ℕ) (inside : i < cycle.length) :
      (matchingCycleChildAt s.nm (expansionRegisteredCycleBase s + 4 * i)).representative = cycle[i].val :=
    (input.rows.records ⟨i, inside⟩).1
  have unique (slot : Fin cycle.length) (i : ℕ) (inside : i < cycle.length) :
      (matchingCycleChildAt s.nm (expansionRegisteredCycleBase s + 4 * i)).representative = cycle[slot.val].val ↔ i = slot.val := by
    rw [rows i inside]
    constructor
    · intro eq
      exact (List.Nodup.getElem_inj_iff input.nodup).mp (Fin.ext eq)
    · intro eq
      subst i
      rfl
  have eWithin : entrySlot.val < expansionRegisteredCycleLength s := by simpa only [cycleLength] using entrySlot.isLt
  have bWithin : baseSlot.val < expansionRegisteredCycleLength s := by simpa only [cycleLength] using baseSlot.isLt
  obtain ⟨p, parserSteps, parses, live, parserCost, arc⟩ := prepareMatchingExpansionArc_spec entry running layout.one
    eWithin bWithin
    (fun i within => by rw [input.entryChild]; exact unique entrySlot i (cycleLength ▸ within))
    (fun i within => by rw [input.baseWord, ← input.baseChild]; exact unique baseSlot i (cycleLength ▸ within))
    (by simpa only [cycleLength] using input.odd) (by rw [cycleLength, dimension]; exact count) layout.pathBelowCycle
  let a := {p with pc := 0}
  have parsed : ExpansionArcReady s a entrySlot.val baseSlot.val := by
    exact ⟨arc.cycleStart, arc.cycleLength, arc.pathBase, arc.arcLength, arc.parent, arc.mate, arc.words,
      arc.natural, arc.real, arc.realRegisters, arc.fixed⟩
  have frame (r : ℕ) (safe : r ∉ expansionArcScratch := by decide) : a.nr r = s.nr r := parsed.fixed r safe
  have nodeRoom := layout.nodesBelowWitnesses
  have forestRoom := layout.forestBelowRepresentatives
  have repRoom := layout.representativesBelowNodes
  have pathRoom := layout.witnessesBelowPath
  have cycleRoom := layout.pathBelowCycle
  have aLayout : ExpansionForestFrame k (a.nr 51) (a.nr 90) (a.nr 94) a :=
    ⟨(frame 55).trans dimension, (frame 9).trans layout.one, (frame 14).trans layout.zero, rfl,
      by rw [frame 52, frame 51, layout.parents], by rw [frame 53, frame 51, layout.depths], rfl, rfl,
      by rw [frame 51, frame 90]; omega, by rw [frame 90, parsed.pathBase]; exact pathRoom⟩
  have commitLayout : ExpansionPublicationLayout a :=
    ⟨by rw [frame 51, frame 55, frame 57, dimension]; exact forestRoom,
      by rw [frame 57, frame 55, frame 79, dimension]; exact layout.representativesBelowScratch,
      by rw [frame 57, frame 55, frame 74, dimension]; exact repRoom,
      by rw [frame 74, frame 55, frame 90, dimension]; exact nodeRoom,
      by rw [frame 74, frame 55, dimension, parsed.cycleStart]; omega⟩
  have rotatedLength : (base :: children).length = cycle.length := by rw [← input.rotates, List.length_rotate]
  have baseDistinct : (base :: children).Nodup := by rw [← input.rotates, List.nodup_rotate]; exact input.nodup
  have rotatedOdd : Odd (base :: children).length := by rw [rotatedLength]; exact input.odd
  have evenChildren : children.length % 2 = 0 := by have h := Nat.odd_iff.mp rotatedOdd; simp at h; omega
  let index := expansionEntryFromBase cycle.length entrySlot.val baseSlot.val
  have indexWithin : index < (base :: children).length := by
    rw [rotatedLength]
    exact Nat.mod_lt _ (Nat.zero_lt_of_lt entrySlot.isLt)
  have rotatedEntry : (base :: children)[index] = cycle[entrySlot.val] := by
    have rotatedWithin : index < (cycle.rotate baseSlot.val).length := by
      simpa only [input.rotates] using indexWithin
    have relative := List.getElem_rotate cycle baseSlot.val index rotatedWithin
    have offset : (index + baseSlot.val) % cycle.length = entrySlot.val := by
      have rearranged : entrySlot.val + cycle.length - baseSlot.val + baseSlot.val = entrySlot.val + cycle.length := by
        have := baseSlot.isLt
        omega
      simp only [index, expansionEntryFromBase, Nat.mod_add_mod, rearranged, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt entrySlot.isLt
    have rotated : (cycle.rotate baseSlot.val)[index] = cycle[entrySlot.val] :=
      relative.trans (getElem_congr_idx offset)
    simpa only [input.rotates] using rotated
  have ends : (matchingExpansionPhysicalPath cycle entrySlot baseSlot).getLast? = some base := by
    rw [matchingExpansionPhysicalPath_eq_rotated cycle entrySlot baseSlot input.odd, input.rotates, input.baseChild]
    exact (blossomExpansionPath_spec rfl indexWithin baseDistinct rotatedOdd tightRep model.tightCycle).2.1
  obtain ⟨records, lastEdge, path, edgeWitnesses⟩ := parsed.toForestPath entrySlot baseSlot input.rows input.witness
    model.incomingEdge model.cycleEdges ends input.odd input.rotates aLayout (parsed.parent.trans input.parentWord)
    input.baseWord
  have aSize : a.nr 19 = cycle.length := parsed.cycleLength.trans cycleLength
  have aRow (i : ℕ) (hi : i < cycle.length) : (expansionCycleRow a i).representative = cycle[i].val := by
    have untouched : a.nm (a.nr 18 + 4 * i) = s.nm (a.nr 18 + 4 * i) :=
      parsed.natural _ (.inr (by
        have short := expansionArcLength_lt eWithin bWithin
        have start := parsed.cycleStart
        omega))
    change a.nm (a.nr 18 + 4 * i) = _
    rw [untouched, parsed.cycleStart]
    exact rows i hi
  have low (address : ℕ) (safe : address < s.nr 86) : a.nm address = s.nm address :=
    parsed.natural address (.inl safe)
  have aEncoding : AlternatingForestMemory forest (a.nr 51) a.nm := by
    intro v
    have range := v.isLt
    have here := model.encoding v
    rw [frame 51]
    exact ⟨(low _ (by omega)).trans here.1, (low _ (by omega)).trans here.2.1,
      (low _ (by omega)).trans here.2.2⟩
  have pathNodes : records.map ExpansionPathRecord.vertex ++ [base] = matchingExpansionPhysicalPath cycle entrySlot baseSlot := by
    rw [path.followsCycle, matchingExpansionPhysicalPath_eq_rotated cycle entrySlot baseSlot input.odd,
      input.rotates, input.baseChild]
  have aRetained (child parent : Fin k) (outside : child ∉ records.map ExpansionPathRecord.vertex ++ [base])
      (linked : (forest.role child).parent = some parent) : ∃ edge : Fin k × Fin k,
      matchingForestWitnessAt a.nm (a.nr 90) child.val = (edge.1.val, edge.2.val) ∧
      (rep edge.1, rep edge.2) = (parent, child) ∧ tightOriginal s(edge.1, edge.2) := by
    obtain ⟨edge, old, orientation, tight⟩ := model.retained child parent (pathNodes ▸ outside) linked
    have range := child.isLt
    have first := low (forestWitnessAddress (s.nr 90) child.val) (by unfold forestWitnessAddress; omega)
    have second := low (forestWitnessAddress (s.nr 90) child.val + 1) (by unfold forestWitnessAddress; omega)
    refine ⟨edge, ?_, orientation, tight⟩
    rwa [frame 90, matchingForestWitnessAt, first, second]
  obtain ⟨t, published, finishSteps, commits, tLive, finishCost, publication, expanded⟩ :=
    commitMatchingExpansionBlock_spec path commitLayout rfl live
      (fun i hi => by rw [aRow i (aSize ▸ hi), frame 55, dimension]; exact (cycle[i]'(aSize ▸ hi)).isLt)
      (fun i hi j hj same => by
        rw [aRow i (aSize ▸ hi), aRow j (aSize ▸ hj)] at same
        exact (List.Nodup.getElem_inj_iff input.nodup).mp (Fin.ext same))
      (aSize.symm ▸ count) model.valid model.baseInner indexWithin baseDistinct evenChildren model.dormant
      model.tightCycle (rotatedEntry.symm ▸ model.tightEntry) model.childMates aEncoding edgeWitnesses aRetained
  rw [dimension] at parserCost
  exact ⟨_, a, published, _, parses.append commits, tLive, by omega, parsed, publication, expanded.relocate _⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionAfterMembers

/-! matching/MatchingExpansionHandler.lean -/
section RppSource_MatchingExpansionHandler
namespace VehicleRoutingSurvey.Routing

def selectedExpansionBaseState (s : ArithmeticState) : ArithmeticState :=
  {s with pc := 0, nr := Function.update s.nr 97 (s.nr 92)}



theorem prepareExpansionChildrenBlock_spec {s : ArithmeticState} {children : MatchingMemberTree}
    (root : MatchingMemberRoot (topMatchingMemberNodeInput (selectedExpansionBaseState s)) children)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0) :
    ∃ t steps, BlockRuns prepareExpansionChildrenBlock steps s t ∧ t.halted = false ∧
      steps ≤ 93 * s.nr 55 + 16 ∧ ExpansionMemberMapResult s t children := by
  let a := selectedExpansionBaseState s
  have select : BlockRuns selectMatchingExpansionBase 1 s {a with pc := 1} := by
    apply BlockRuns.of_running_exit
    · simp [a, selectMatchingExpansionBase, selectedExpansionBaseState, arithmeticStep, entry, running, zero]
    · exact running
    · rfl
  have preserves (r : ℕ) (away : r ≠ 97 := by decide) : a.nr r = s.nr r := by
    simp [a, selectedExpansionBaseState, Function.update_of_ne away]
  obtain ⟨t, ticks, cost, maps, live, _, _, values, sentinel, kept, real, rr, fixed⟩ :=
    mapMatchingCycleMembers_spec a children root rfl running ((preserves 9).trans one)
  rw [preserves 55] at cost
  refine ⟨_, _, select.append maps, live, by omega, ?_, ?_, ?_, ?_, real, rr, ?_⟩
  · exact (fixed 97 (by decide)).trans (by simp [a, selectedExpansionBaseState])
  · intro p assigned
    change t.nm (s.nr 79 + p.1) = p.2
    simpa only [preserves 79] using values p assigned
  · intro v within absent
    change t.nm (s.nr 79 + v) = s.nr 55
    simpa only [preserves 55, preserves 79] using sentinel v (by rwa [preserves 55]) absent
  · intro address safe
    exact kept address (by simpa only [outsideMatchingMemberScratch, preserves 55, preserves 79, preserves 80] using safe)
  · intro r safe
    exact (fixed r (by simp at safe ⊢; omega)).trans (preserves r (by simp at safe; omega))





end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionHandler

/-! matching/ExpansionMemberSemantics.lean -/
section RppSource_ExpansionMemberSemantics
namespace VehicleRoutingSurvey.Routing

/-- With oriented parent witnesses, the endpoint inside the old base is the
second original. The DFS map supplies its exact direct child. -/
theorem expansionEntryChild_ofOriented {k : ℕ} {s : ArithmeticState}
    {witness : Fin k × Fin k} {child : Fin k}
    (words : expansionOldParentWitness s = (witness.1.val, witness.2.val))
    (outside : s.nm (s.nr 57 + witness.1.val) ≠ s.nr 97)
    (owner : s.nm (s.nr 79 + witness.2.val) = child.val) : expansionEntryChild s = child.val := by
  unfold expansionEntryChild expansionEntryOriginal
  rw [words]
  change s.nm (s.nr 79 + (if s.nm (s.nr 57 + witness.1.val) = s.nr 97 then witness.1.val else witness.2.val)) = child.val
  rw [if_neg outside]
  exact owner

theorem ExpansionMemberMapResult.assignment {k : ℕ} {a b : ArithmeticState} {tree : MatchingMemberTree}
    (map : ExpansionMemberMapResult a b tree) {v child : Fin k}
    (member : (v.val, child.val) ∈ matchingMemberAssignments tree) :
    b.nm (b.nr 79 + v.val) = child.val := by
  rw [map.fixed 79 (by decide)]
  exact map.values (v.val, child.val) member

theorem ExpansionMemberMapResult.nonmember {k : ℕ} {a b : ArithmeticState} {tree : MatchingMemberTree}
    (map : ExpansionMemberMapResult a b tree) (size : a.nr 55 = k) {v : Fin k}
    (outside : v.val ∉ tree.leaves) : b.nm (b.nr 79 + v.val) = k := by
  have within : v.val < a.nr 55 := size.symm ▸ v.isLt
  rw [map.fixed 79 (by decide)]
  exact (map.sentinel v.val within outside).trans size

theorem ExpansionArcReady.keepsMembers {s t : ArithmeticState} {e b : ℕ}
    (arc : ExpansionArcReady s t e b)
    (entry : e < expansionRegisteredCycleLength s) (base : b < expansionRegisteredCycleLength s)
    (room : s.nr 86 + 3 * expansionRegisteredCycleLength s ≤ s.nr 79) (v : ℕ) :
    t.nm (t.nr 79 + v) = s.nm (s.nr 79 + v) := by
  have pathLength := expansionArcLength_lt entry base
  rw [arc.fixed 79 (by decide)]
  exact arc.natural _ (.inr (by omega))





theorem ExpansionPublication.childRepresentative {k : ℕ} {s t : ArithmeticState}
    (publication : ExpansionPublication s t) (size : s.nr 55 = k) {v child : Fin k}
    (assigned : s.nm (s.nr 79 + v.val) = child.val) : t.nm (t.nr 57 + v.val) = child.val := by
  have within : v.val < s.nr 55 := size.symm ▸ v.isLt
  have validChild : child.val < s.nr 55 := size.symm ▸ child.isLt
  rw [publication.fixed 57 (by decide), publication.representatives v.val within, assigned, if_pos validChild]

theorem ExpansionPublication.keptRepresentative {k : ℕ} {s t : ArithmeticState}
    (publication : ExpansionPublication s t) (size : s.nr 55 = k) {v : Fin k}
    (outside : s.nm (s.nr 79 + v.val) = k) : t.nm (t.nr 57 + v.val) = s.nm (s.nr 57 + v.val) := by
  have within : v.val < s.nr 55 := size.symm ▸ v.isLt
  rw [publication.fixed 57 (by decide), publication.representatives v.val within, outside, size, if_neg (Nat.lt_irrefl _)]

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionMemberSemantics

/-! matching/AlternatingContractionParity.lean -/
section RppSource_AlternatingContractionParity
namespace VehicleRoutingSurvey.Routing



theorem parent_step_roles {α : Type*} {state : AlternatingForestState α}
    {mate : α → Option α} {tight : α → α → Prop} (valid : state.valid mate tight)
    {child parent : α} (link : (state.role child).parent = some parent) :
    (∃ previous, state.role child = .outer (some parent) ∧
        state.role parent = .inner previous ∧ mate parent = some child) ∨
    (∃ previous, state.role child = .inner parent ∧ state.role parent = .outer previous) := by
  have before := valid child
  cases kind : state.role child with
  | unlabelled => simp [kind, AlternatingForestRole.parent] at link
  | outer opt =>
    cases opt with
    | none => simp [kind, AlternatingForestRole.parent] at link
    | some p =>
      have same : p = parent := Option.some.inj (by simpa only [kind, AlternatingForestRole.parent] using link)
      subst p
      try rw [kind] at before
      obtain ⟨⟨previous, inner⟩, _, partner, _, _⟩ := before
      exact Or.inl ⟨previous, rfl, inner, partner⟩
  | inner p =>
    have same : p = parent := Option.some.inj (by simpa only [kind, AlternatingForestRole.parent] using link)
    subst p
    try rw [kind] at before
    obtain ⟨⟨previous, outer⟩, _, _, _, _⟩ := before
    exact Or.inr ⟨previous, rfl, outer⟩

























end VehicleRoutingSurvey.Routing
end RppSource_AlternatingContractionParity

/-! matching/MatchingExpansionOwnerMap.lean -/
section RppSource_MatchingExpansionOwnerMap
namespace VehicleRoutingSurvey.Routing



theorem ExpansionMemberMapResult.encodesChildPorts {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {B : Finset (Fin k)} {a b : ArithmeticState}
    {tree : MatchingMemberTree} {registry : MatchingExpansionChildPorts state B}
    (map : ExpansionMemberMapResult a b tree) (geometry : MatchingChildMemberTree registry tree)
    (dimension : a.nr 55 = k) :
    ∀ v : Fin k, b.nm (b.nr 79 + v.val) = if v ∈ B then (registry.owner v).val else k := by
  intro v
  by_cases inside : v ∈ B
  · rw [if_pos inside]
    exact map.assignment (geometry.assignment v inside)
  · rw [if_neg inside]
    exact map.nonmember dimension (geometry.absent v inside)





end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionOwnerMap

/-! matching/MatchingSearchWitnesses.lean -/
section RppSource_MatchingSearchWitnesses
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory





theorem AlternatingForestState.valid_of_parent_tight {α : Type*} {forest : AlternatingForestState α}
    {mate : α → Option α} {old next : α → α → Prop} (valid : forest.valid mate old)
    (tight : ∀ {child parent}, (forest.role child).parent = some parent → next parent child) :
    forest.valid mate next := by
  intro child
  have row := valid child
  cases kind : forest.role child with
  | unlabelled => trivial
  | outer prior =>
    rw [kind] at row
    cases prior with
    | none => exact row
    | some p =>
      exact ⟨row.1, row.2.1, row.2.2.1, tight (child := child) (by simp [kind, AlternatingForestRole.parent]),
        row.2.2.2.2⟩
  | inner p =>
    rw [kind] at row
    exact ⟨row.1, row.2.1, row.2.2.1, tight (child := child) (by simp [kind, AlternatingForestRole.parent]),
      row.2.2.2.2⟩






end VehicleRoutingSurvey.Routing
end RppSource_MatchingSearchWitnesses

/-! matching/MatchingExpansionRetained.lean -/
section RppSource_MatchingExpansionRetained
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The representative of every old block except the selected top block
survives. The selected base also survives as the port of its own child. -/
theorem MatchingExpansionChildPorts.openRep {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {B : Finset (Fin k)} (registry : MatchingExpansionChildPorts state B)
    (top : B ∈ Finset.univ.image part.blocks.block) (present : B ∈ state.cuts) (zero : state.cutDual B = 0)
    (internal : state.InternalCuts)
    (external : ∀ p ∈ registry.ports, ∀ w, state.partialMate p = some w → w ∉ registry.block p)
    {base : Fin k} (baseBlock : part.blocks.block base = B) (baseFixed : part.representative base = base)
    (basePort : base ∈ registry.ports) :
    let opened := part.openZeroCut top present zero (registry.toExpansionChildren internal external)
    opened.representative base = base ∧
      ∀ v, part.representative v ≠ base → opened.representative v = part.representative v := by
  intro opened
  have member : base ∈ B := registry.subset _ basePort (registry.containsPort _ basePort)
  constructor
  · change (if base ∈ B then registry.owner base else part.representative base) = base
    rw [if_pos member, registry.unique _ basePort _ (registry.containsPort _ basePort)]
  · intro v different
    have outside : v ∉ B := fun inside => different ((part.same_block.mpr
      (((part.block_eq_iff_member top v).mpr inside).trans baseBlock.symm)).trans baseFixed)
    change (if v ∈ B then registry.owner v else part.representative v) = part.representative v
    rw [if_neg outside]

theorem MatchingExpansionChildPorts.dormant {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {B : Finset (Fin k)} (registry : MatchingExpansionChildPorts state B)
    (top : B ∈ Finset.univ.image part.blocks.block) {base : Fin k} (children : List (Fin k))
    (ports : registry.ports = (base :: children).toFinset) (distinct : (base :: children).Nodup)
    (baseBlock : part.blocks.block base = B) (baseFixed : part.representative base = base)
    {forest : AlternatingForestState (Fin k)}
    (inactive : ∀ v, part.representative v ≠ v → forest.role v = .unlabelled) :
    ∀ v ∈ children, forest.role v = .unlabelled := by
  intro v member
  have port : v ∈ registry.ports := ports.symm ▸ List.mem_toFinset.mpr (List.mem_cons_of_mem _ member)
  have inside := registry.subset _ port (registry.containsPort _ port)
  have rep := (part.same_block.mpr (((part.block_eq_iff_member top v).mpr inside).trans baseBlock.symm)).trans baseFixed
  exact inactive v (fun fixed => (List.nodup_cons.mp distinct).1 ((rep.symm.trans fixed).symm ▸ member))

/-- A retained unmatched parent link stays outside the split. A retained
link from the selected inner base is matched and stores its actual original
endpoints, so its physical witness still reads as a link from the base. -/
theorem MatchingExpansionChildPorts.retainedWitness {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {B : Finset (Fin k)} (registry : MatchingExpansionChildPorts state B)
    (top : B ∈ Finset.univ.image part.blocks.block) (present : B ∈ state.cuts) (zero : state.cutDual B = 0)
    (internal : state.InternalCuts)
    (external : ∀ p ∈ registry.ports, ∀ w, state.partialMate p = some w → w ∉ registry.block p)
    {base source : Fin k} (baseBlock : part.blocks.block base = B) (baseFixed : part.representative base = base)
    (basePort : base ∈ registry.ports) {s : ArithmeticState} {forest : AlternatingForestState (Fin k)}
    (witnesses : MatchingForestOriginalWitnesses part forest s)
    {tight : Fin k → Fin k → Prop} (valid : forest.valid state.partialMate tight)
    (inner : forest.role base = .inner source)
    (matched : ∀ child, forest.role child = .outer (some base) →
      matchingForestWitnessAt s.nm (s.nr 90) child.val = (base.val, child.val)) :
    let opened := part.openZeroCut top present zero (registry.toExpansionChildren internal external)
    let next := state.eraseZeroCut present zero
    ∀ (child parent : Fin k), child ≠ base → (forest.role child).parent = some parent →
      ∃ e : Fin k × Fin k, matchingForestWitnessAt s.nm (s.nr 90) child.val = (e.1.val, e.2.val) ∧
        (opened.representative e.1, opened.representative e.2) = (parent, child) ∧
        oddCutDualEdgeValue next.cuts next.potential next.cutDual s(e.1, e.2) = edgeCost cost s(e.1, e.2) := by
  intro opened next child parent childAway link
  obtain ⟨a, b, words, first, second, value⟩ := witnesses link
  obtain ⟨atBase, away⟩ := registry.openRep top present zero internal external baseBlock baseFixed basePort
  have childNow : opened.representative b = child := (away b (fun eq => childAway (second.symm.trans eq))).trans second
  have parentNow : opened.representative a = parent := by
    by_cases atCut : parent = base
    · rw [atCut] at link ⊢
      have childRole : forest.role child = .outer (some base) := by
        cases r : forest.role child with
        | unlabelled => simp [r, AlternatingForestRole.parent] at link
        | outer p =>
          rw [r] at link
          exact congrArg AlternatingForestRole.outer link
        | inner p =>
          have isBase : p = base := Option.some.inj (by simpa only [r, AlternatingForestRole.parent] using link)
          have row := valid child
          rw [r] at row
          obtain ⟨q, isOuter⟩ := row.1
          rw [isBase, inner] at isOuter
          contradiction
      have original : a = base := Fin.ext (congrArg Prod.fst (words.symm.trans (matched child childRole)))
      rw [original]
      exact atBase
    · exact (away a (fun eq => atCut (first.symm.trans eq))).trans first
  refine ⟨(a, b), words, Prod.ext parentNow childNow, ?_⟩
  exact (oddCutDualEdgeValue_erase_zero state.cuts present state.potential state.cutDual zero s(a, b)).trans value

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionRetained

/-! matching/MatchingExpansionMapRefinement.lean -/
section RppSource_MatchingExpansionMapRefinement
namespace VehicleRoutingSurvey.Routing

/-- The member traversal's scratch writes are disjoint from the chosen
registry node and all its cycle words. -/
structure MatchingExpansionCycleRead {s : ArithmeticState} (selected : ArithmeticState) : Prop where
  node : outsideMatchingMemberScratch s (selected.nr 74 + selected.nr 97)
  start : outsideMatchingMemberScratch s (selected.nr 77 + expansionOldNode selected)
  length : outsideMatchingMemberScratch s (selected.nr 78 + expansionOldNode selected)
  records : ∀ i < expansionRegisteredCycleLength selected, ∀ w < 4,
    outsideMatchingMemberScratch s (expansionRegisteredCycleBase selected + 4 * i + w)

theorem ExpansionMemberMapResult.cycleRows {k : ℕ} {a b : ArithmeticState} {tree : MatchingMemberTree}
    {cycle : List (Fin k)} {edges : Fin cycle.length → Fin k × Fin k}
    (mapped : ExpansionMemberMapResult a b tree)
    (rows : ExpansionCycleWitnessRows (selectedExpansionBaseState a) cycle edges)
    (safe : MatchingExpansionCycleRead (s := a) (selectedExpansionBaseState a)) :
    ExpansionCycleWitnessRows b cycle edges := by
  let s := selectedExpansionBaseState a
  have stateWord (r : ℕ) (keep : r ≠ 97 := by decide) : s.nr r = a.nr r := by
    simp [s, selectedExpansionBaseState, Function.update_of_ne keep]
  have nodeWord : b.nr 97 = s.nr 97 := by
    simpa [s, selectedExpansionBaseState] using mapped.selectedBase
  have sameRegister (r : ℕ) (keep : r ∉ [0, 6, 7, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 28, 87, 97] := by decide)
      (away : r ≠ 97 := by decide) : b.nr r = s.nr r := (mapped.fixed r keep).trans (stateWord r away).symm
  have node : expansionOldNode b = expansionOldNode s := by
    unfold expansionOldNode
    rw [sameRegister 74, nodeWord]
    exact mapped.natural _ safe.node
  have start : expansionRegisteredCycleBase b = expansionRegisteredCycleBase s := by
    unfold expansionRegisteredCycleBase
    rw [sameRegister 77, node]
    exact mapped.natural _ safe.start
  have length : expansionRegisteredCycleLength b = expansionRegisteredCycleLength s := by
    unfold expansionRegisteredCycleLength
    rw [sameRegister 78, node]
    exact mapped.natural _ safe.length
  refine ⟨length.trans rows.length, ?_⟩
  intro i
  have within : i.val < expansionRegisteredCycleLength s := rows.length.symm ▸ i.isLt
  have keep (w : ℕ) (hw : w < 4 := by decide) :
      b.nm (expansionRegisteredCycleBase s + 4 * i.val + w) = s.nm (expansionRegisteredCycleBase s + 4 * i.val + w) :=
    mapped.natural _ (safe.records i.val within w hw)
  have cell : matchingCycleChildAt b.nm (expansionRegisteredCycleBase b + 4 * i.val) =
      matchingCycleChildAt s.nm (expansionRegisteredCycleBase s + 4 * i.val) := by
    rw [start]
    have first : b.nm (expansionRegisteredCycleBase s + 4 * i.val) = s.nm (expansionRegisteredCycleBase s + 4 * i.val) := keep 0
    simp only [matchingCycleChildAt, first, keep 1, keep 2, keep 3]
  change let row := matchingCycleChildAt b.nm (expansionRegisteredCycleBase b + 4 * i.val)
    row.representative = cycle[i.val].val ∧
      (row.endpointA, row.endpointB) = ((edges i).1.val, (edges i).2.val)
  rw [cell]
  exact rows.records i

theorem ExpansionMemberMapResult.cycleInput {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost}
    {B : Finset (Fin k)} {a b : ArithmeticState} {tree : MatchingMemberTree}
    {registry : MatchingExpansionChildPorts state B} {forest : AlternatingForestState (Fin k)}
    {cycle : List (Fin k)} {edges : Fin cycle.length → Fin k × Fin k}
    {entrySlot baseSlot : Fin cycle.length} {source base : Fin k} {children : List (Fin k)}
    {incoming : Fin k × Fin k}
    (mapped : ExpansionMemberMapResult a b tree) (geometry : MatchingChildMemberTree registry tree)
    (size : a.nr 55 = k) (selected : a.nr 92 = base.val)
    (rows : ExpansionCycleWitnessRows (selectedExpansionBaseState a) cycle edges)
    (safe : MatchingExpansionCycleRead (s := a) (selectedExpansionBaseState a))
    (scratch : a.nr 79 ≤ a.nr 80)
    (prefixParents : a.nr 52 + k ≤ a.nr 79)
    (prefixRepresentatives : a.nr 57 + k ≤ a.nr 79)
    (prefixWitness : a.nr 90 + 2 * k ≤ a.nr 79)
    (encoding : AlternatingForestMemory forest (a.nr 51) a.nm) (parentBase : a.nr 52 = a.nr 51 + k)
    (inner : forest.role base = .inner source)
    (distinct : cycle.Nodup) (odd : Odd cycle.length)
    (rotates : cycle.rotate baseSlot.val = base :: children) (atBase : cycle[baseSlot.val] = base)
    (witness : matchingForestWitnessAt a.nm (a.nr 90) base.val = (incoming.1.val, incoming.2.val))
    (preRep : a.nm (a.nr 57 + incoming.1.val) = source.val) (apart : source ≠ base)
    (owned : incoming.2 ∈ B) (atEntry : registry.owner incoming.2 = cycle[entrySlot.val]) :
    ExpansionCycleInput b cycle edges entrySlot baseSlot source base children incoming := by
  have overwritten (address : ℕ) (h : address < a.nr 79) : b.nm address = a.nm address :=
    mapped.natural _ ⟨.inl h, .inl (h.trans_le scratch)⟩
  have baseWord := mapped.selectedBase.trans selected
  have bv := base.isLt
  have iv := incoming.1.isLt
  have witnessed : expansionOldParentWitness b = (incoming.1.val, incoming.2.val) := by
    unfold expansionOldParentWitness
    rw [mapped.fixed 90 (by decide), baseWord]
    let addr := a.nr 90 + (base.val + base.val)
    change (b.nm addr, b.nm (addr + 1)) = _
    rw [overwritten addr (by dsimp [addr]; omega), overwritten (addr + 1) (by dsimp [addr]; omega)]
    exact witness
  have sourceWord : b.nm (b.nr 57 + incoming.1.val) ≠ b.nr 97 := by
    rw [mapped.fixed 57 (by decide), overwritten _ (by omega), preRep, baseWord]
    exact fun same => apart (Fin.ext same)
  have owner := mapped.encodesChildPorts geometry size incoming.2
  rw [if_pos owned, atEntry] at owner
  have parentWord : b.nm (b.nr 52 + b.nr 97) = source.val := by
    rw [mapped.fixed 52 (by decide), baseWord, overwritten _ (by omega), parentBase, (encoding base).2.1, inner] <;> rfl
  exact ⟨mapped.cycleRows rows safe, distinct, odd, rotates, baseWord, atBase,
    expansionEntryChild_ofOriented witnessed sourceWord owner, parentWord, witnessed⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionMapRefinement

/-! matching/MatchingExpansionGeometry.lean -/
section RppSource_MatchingExpansionGeometry
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory







/-- The incoming forest witness determines the child hit by its second
original endpoint, hence an actual table index used by the expansion scan. -/
theorem MatchingExpansionGeometry.incoming {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {B : Finset (Fin k)} {registry : MatchingExpansionChildPorts state B} {tree : MatchingMemberTree}
    {base source : Fin k} (g : MatchingExpansionGeometry registry tree base)
    (top : B ∈ Finset.univ.image part.blocks.block)
    (baseFixed : part.representative base = base) (baseBlock : part.blocks.block base = B)
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState} (inner : forest.role base = .inner source)
    (witnesses : MatchingForestOriginalWitnesses part forest s) :
    ∃ (entrySlot : Fin g.cycle.length) (edge : Fin k × Fin k),
      matchingForestWitnessAt s.nm (s.nr 90) base.val = (edge.1.val, edge.2.val) ∧
      part.representative edge.1 = source ∧ edge.2 ∈ B ∧ registry.owner edge.2 = g.cycle[entrySlot.val] ∧
      oddCutDualEdgeValue state.cuts state.potential state.cutDual s(edge.1, edge.2) = edgeCost cost s(edge.1, edge.2) := by
  have linked : (forest.role base).parent = some source := by rw [inner]; rfl
  obtain ⟨a, b, words, head, tail, tight⟩ := witnesses linked
  have inside := (part.block_eq_iff_member top b).mp ((part.same_block.mp (tail.trans baseFixed.symm)).trans baseBlock)
  have port := (registry.covered b inside).1
  rw [g.ports, List.mem_toFinset] at port
  obtain ⟨i, within, atSlot⟩ := List.mem_iff_getElem.mp port
  exact ⟨⟨i, within⟩, (a,b), words, head, inside, atSlot.symm, tight⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionGeometry

/-! matching/MatchingExpansionSelection.lean -/
section RppSource_MatchingExpansionSelection
namespace VehicleRoutingSurvey.Routing











theorem MatchingSelectedExpansion.registry_node {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {s t : ArithmeticState} {B : Finset (Fin k)}
    (event : MatchingSelectedExpansion part forest positive s B)
    (dual : MatchingSearchDualMemory part forest t) (present : B ∈ state.cuts) :
    t.nm (t.nr 74 + event.base.val) = dual.node B ∧ dual.node B ≠ 0 := by
  have top := dual.top event.base
  change t.nm (t.nr 74 + event.base.val) = _ at top
  have nontrivialAt : (part.blocks.block event.base).card ≠ 1 := by rw [event.block]; exact event.nontrivial
  rw [if_pos ⟨event.active, nontrivialAt⟩, event.block] at top
  exact ⟨top, dual.nodeNonzero B present⟩





end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionSelection

/-! matching/MatchingLiveCycleGeometry.lean -/
section RppSource_MatchingLiveCycleGeometry
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



theorem MatchingNodeCycleRows.selected {k n : ℕ} {s : ArithmeticState} {cycle : List (Fin k)}
    {edge : Fin cycle.length → Fin k × Fin k} (rows : MatchingNodeCycleRows s n cycle edge)
    (atNode : s.nm (s.nr 74 + s.nr 92) = n) :
    ExpansionCycleWitnessRows (selectedExpansionBaseState s) cycle edge := by
  constructor
  · simpa [expansionRegisteredCycleLength,expansionOldNode,selectedExpansionBaseState,atNode] using rows.length
  · intro i
    simpa [expansionRegisteredCycleBase,expansionOldNode,selectedExpansionBaseState,matchingCycleRecordStart,atNode]
      using rows.records i







theorem MatchingLiveCycleMemory.expansionRoot {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    {e : MatchingLiveCycle state node B} {s : ArithmeticState} (memory : MatchingLiveCycleMemory e s)
    (nodeAt : s.nm (s.nr 74 + s.nr 92) = node B) :
    MatchingMemberRoot (topMatchingMemberNodeInput (selectedExpansionBaseState s)) e.tree := by
  let a := topMatchingMemberNodeInput (selectedExpansionBaseState s)
  let b := matchingRebaseNodeState s (node B)
  have id : a.nr 22 = b.nr 22 := by simp [a,b,topMatchingMemberNodeInput,selectedExpansionBaseState,matchingRebaseNodeState,nodeAt]
  have keep (r : ℕ) (six : r ≠ 6 := by decide) (n : r ≠ 22 := by decide) (base : r ≠ 97 := by decide) :
      a.nr r = b.nr r := by
    simp [a,b,topMatchingMemberNodeInput,selectedExpansionBaseState,matchingRebaseNodeState,
      Function.update_of_ne six, Function.update_of_ne n, Function.update_of_ne base]
  have outside : outsideMatchingMemberScratch a = outsideMatchingMemberScratch b := by
    funext x
    simp only [outsideMatchingMemberScratch,keep 79,keep 80,keep 55]
  have old : MatchingMemberRoot b e.tree := memory.members
  change MatchingMemberRoot a e.tree
  have nm : a.nm = b.nm := rfl
  exact ⟨by rw [id]; exact old.proper, by rw [id,nm,keep 77,keep 78]; exact old.encoded,
    by rw [id,nm,keep 77,keep 78,outside]; exact old.readable,
    by rw [id,nm,keep 77,keep 80,keep 55]; exact old.above, old.unique,
    by rw [keep 55]; exact old.valid, by rw [keep 79,keep 55,keep 80]; exact old.separated⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingLiveCycleGeometry

/-! matching/MatchingForestLinkMemory.lean -/
section RppSource_MatchingForestLinkMemory
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory





theorem MatchingForestLinkMemory.advance {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state next : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {nextPart : CompactMatchingPartition next} {forest : AlternatingForestState (Fin k)} {s t : ArithmeticState}
    (links : MatchingForestLinkMemory part forest s) (reps : nextPart.representative = part.representative)
    (words : ∀ v : Fin k, matchingForestWitnessAt t.nm (t.nr 90) v.val =
      matchingForestWitnessAt s.nm (s.nr 90) v.val) : MatchingForestLinkMemory nextPart forest t := by
  exact ⟨fun v away => links.inactive v (reps ▸ away), fun {child _} role => (words child).trans (links.matched role)⟩




end VehicleRoutingSurvey.Routing
end RppSource_MatchingForestLinkMemory

/-! matching/MatchingExpansionPhysicalLayout.lean -/
section RppSource_MatchingExpansionPhysicalLayout
namespace VehicleRoutingSurvey.Routing

/-- The selected root already certifies that every word of its cycle is
outside the DFS scratch areas. Only the top-node table requires a separate bound. -/
theorem MatchingMemberRoot.expansionCycleRead {s : ArithmeticState} {tree : MatchingMemberTree}
    (root : MatchingMemberRoot (topMatchingMemberNodeInput (selectedExpansionBaseState s)) tree)
    (nodeSafe : outsideMatchingMemberScratch s (s.nr 74 + s.nr 92)) :
    MatchingExpansionCycleRead (s := s) (selectedExpansionBaseState s) := by
  let selected := selectedExpansionBaseState s
  let input := topMatchingMemberNodeInput selected
  have atNode : input.nr 22 = expansionOldNode selected := by simp [input, topMatchingMemberNodeInput, expansionOldNode]
  have shared (r : ℕ) (h6 : r ≠ 6 := by decide) (h22 : r ≠ 22 := by decide)
      (h97 : r ≠ 97 := by decide) : input.nr r = s.nr r := by
    simp [input, selected, topMatchingMemberNodeInput, selectedExpansionBaseState,
      Function.update_of_ne h6, Function.update_of_ne h22, Function.update_of_ne h97]
  have selectedAt (r : ℕ) (h97 : r ≠ 97 := by decide) : selected.nr r = s.nr r :=
    Function.update_of_ne h97 _ _
  have scratch : outsideMatchingMemberScratch input = outsideMatchingMemberScratch s := by
    funext a
    simp only [outsideMatchingMemberScratch, shared 55, shared 79, shared 80]
  have readable := root.readable
  change (MatchingMemberTree.blossom 0 (input.nr 22) tree .nil).readable input.nm
    (input.nr 77) (input.nr 78) (outsideMatchingMemberScratch input) at readable
  rw [scratch, atNode, shared 77, shared 78] at readable
  have sameMemory : input.nm = selected.nm := rfl
  have n : expansionRegisteredCycleLength selected = tree.arity := by
    simpa only [expansionRegisteredCycleLength, selectedAt 78, atNode, shared 78, sameMemory] using
      (show input.nm (input.nr 78 + input.nr 22) = tree.arity from root.encoded.1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [selectedExpansionBaseState] using nodeSafe
  · change outsideMatchingMemberScratch s (selected.nr 77 + expansionOldNode selected)
    rw [selectedAt 77]
    exact readable.1
  · change outsideMatchingMemberScratch s (selected.nr 78 + expansionOldNode selected)
    rw [selectedAt 78]
    exact readable.2.1
  · intro i hi w hw
    change outsideMatchingMemberScratch s (selected.nm (selected.nr 77 + expansionOldNode selected) + 4*i+w)
    rw [selectedAt 77]
    exact readable.2.2.1 i (n ▸ hi) w hw

/-- Stable allocations for the physical expansion path. The reserved temporary
records end before the leaf map. Every live cycle starts beyond the DFS stack. -/
structure MatchingExpansionStorage (k : ℕ) (s : ArithmeticState) : Prop where
  repsNodes : s.nr 57 + k ≤ s.nr 74
  nodesWitness : s.nr 74 + k ≤ s.nr 90
  witnessPath : s.nr 90 + 2*k ≤ s.nr 86
  pathMap : s.nr 86 + 3*k ≤ s.nr 79
  mapStack : s.nr 79 + k ≤ s.nr 80

theorem ExpansionMemberMapResult.layout {k : ℕ} {s t : ArithmeticState} {tree : MatchingMemberTree}
    (mapped : ExpansionMemberMapResult s t tree) (warm : MatchingWarmLayout s k)
    (storage : MatchingExpansionStorage k s) (unit : s.nr 9 = 1) (zero : s.nr 14 = 0)
    {cycle : List (Fin k)} {edges : Fin cycle.length → Fin k × Fin k}
    (rows : ExpansionCycleWitnessRows (selectedExpansionBaseState s) cycle edges) (unique : cycle.Nodup)
    (root : MatchingMemberRoot (topMatchingMemberNodeInput (selectedExpansionBaseState s)) tree)
    (selectedBound : s.nr 92 < k) : ExpansionInputLayout k t := by
  let selected := selectedExpansionBaseState s
  let input := topMatchingMemberNodeInput selected
  have keep (r : ℕ) (safe : r ∉ [0,6,7,15,16,17,18,19,22,23,24,25,26,28,87,97] := by decide) := mapped.fixed r safe
  obtain ⟨repNode, nodeWitness, witnessPath, pathMap, mapStack⟩ := storage
  have nodeSafe : outsideMatchingMemberScratch s (s.nr 74 + s.nr 92) := ⟨.inl (by omega), .inl (by omega)⟩
  have safe := root.expansionCycleRead nodeSafe
  have n : expansionRegisteredCycleLength t = cycle.length := (mapped.cycleRows rows safe).length
  have bound : cycle.length ≤ k := by
    simpa using unique.length_le_card
  have atNode : expansionOldNode t = expansionOldNode selected := by
    unfold expansionOldNode
    change t.nm (t.nr 74 + t.nr 97) = s.nm (s.nr 74 + s.nr 92)
    rw [keep 74, mapped.selectedBase]
    exact mapped.natural _ nodeSafe
  have starts : expansionRegisteredCycleBase t = expansionRegisteredCycleBase selected := by
    unfold expansionRegisteredCycleBase
    rw [atNode, keep 77]
    exact mapped.natural _ safe.start
  have above : s.nr 80 + 3*s.nr 55 ≤ expansionRegisteredCycleBase selected := by
    simpa [input, selected, expansionRegisteredCycleBase, expansionOldNode,
      topMatchingMemberNodeInput, selectedExpansionBaseState] using root.above.1
  refine ⟨(keep 55).trans warm.size, (keep 9).trans unit, (keep 14).trans zero, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [keep 52, keep 51, warm.parents]
  · rw [keep 53, keep 51, warm.depths]
  · rw [keep 51, keep 57]
    exact warm.representativesAfter
  · rw [keep 57, keep 79]
    omega
  · rw [keep 57, keep 74]
    exact repNode
  · rw [keep 74, keep 90]
    exact nodeWitness
  · rw [keep 90, keep 86]
    omega
  · rw [keep 86, n, starts]
    omega

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionPhysicalLayout

/-! matching/MatchingExpansionPublishedNodes.lean -/
section RppSource_MatchingExpansionPublishedNodes
namespace VehicleRoutingSurvey.Routing

/-- The node word paired with the stored child port is its live child ID, or
zero for a singleton. This is the second physical word of the cycle row. -/
theorem MatchingLiveCycleMemory.childRow {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    {e : MatchingLiveCycle state node B} {s : ArithmeticState} (memory : MatchingLiveCycleMemory e s)
    (i : Fin e.geometry.cycle.length) :
    let cell := matchingCycleChildAt s.nm (matchingCycleRecordStart s (node B) + 4*i.val)
    let p := e.geometry.cycle.get i
    cell.representative = p.val ∧ cell.node = if (e.ports.block p).card = 1 then 0 else node (e.ports.block p) := by
  intro cell p
  let jobs := e.tree.jobs none
  have size : jobs.length = e.geometry.cycle.length := (e.tree.jobs_length none).trans e.arity
  have inside : i.val < jobs.length := size.symm ▸ i.isLt
  have key := (matchingMemberJobRows (owner := none) memory.members.encoded.2.1 i.val inside).1
  have head : cell.representative = jobs[i.val].representative := congrArg Prod.fst key
  have id : cell.node = jobs[i.val].node := congrArg Prod.snd key
  have typed : cell.representative = p.val := (memory.rows.records i).1
  exact ⟨typed,id.trans (e.childNode _ (List.getElem_mem inside) p (head.symm.trans typed))⟩

/-- The child ID and its representative at the instruction which publishes
them, after both the DFS scratch writes and the even-arc path writes. -/
theorem MatchingLiveCycleMemory.arcRows {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    {e : MatchingLiveCycle state node B} {s m a : ArithmeticState} (memory : MatchingLiveCycleMemory e s)
    (atNode : s.nm (s.nr 74+s.nr 92) = node B) (topSafe : outsideMatchingMemberScratch s (s.nr 74+s.nr 92))
    (map : ExpansionMemberMapResult s m e.tree) (layout : ExpansionInputLayout k m)
    {entry base : Fin e.geometry.cycle.length} (arc : ExpansionArcReady m a entry.val base.val) :
    a.nr 19 = e.geometry.cycle.length ∧ ∀ i : Fin e.geometry.cycle.length,
      let cell := expansionCycleRow a i.val
      let p := e.geometry.cycle.get i
      cell.representative = p.val ∧ cell.node = if (e.ports.block p).card = 1 then 0 else node (e.ports.block p) := by
  let selected := selectedExpansionBaseState s
  have safe := (memory.expansionRoot atNode).expansionCycleRead topSafe
  have initial := memory.rows.selected atNode
  have mapped := (map.cycleRows initial safe).length
  have n : expansionOldNode m = node B := by
    unfold expansionOldNode
    rw [map.fixed 74 (by decide),map.selectedBase,map.natural _ topSafe,atNode]
  have header : outsideMatchingMemberScratch s (s.nr 77+node B) := by
    simpa [expansionOldNode,selectedExpansionBaseState,atNode] using safe.start
  have start : expansionRegisteredCycleBase m = matchingCycleRecordStart s (node B) := by
    unfold expansionRegisteredCycleBase matchingCycleRecordStart
    rw [map.fixed 77 (by decide),n,map.natural _ header]
  have entryInside : entry.val < expansionRegisteredCycleLength m := by rw [mapped]; exact entry.isLt
  have baseInside : base.val < expansionRegisteredCycleLength m := by rw [mapped]; exact base.isLt
  have short := expansionArcLength_lt entryInside baseInside
  have high := layout.pathBelowCycle
  refine ⟨arc.cycleLength.trans mapped,?_⟩
  intro i cell p
  have within : i.val < expansionRegisteredCycleLength (selectedExpansionBaseState s) := initial.length.symm ▸ i.isLt
  have keep (w : ℕ) (hw : w < 4) : a.nm (a.nr 18+4*i.val+w) = s.nm (matchingCycleRecordStart s (node B)+4*i.val+w) := by
    rw [arc.cycleStart,arc.natural _ (.inr (by omega)),start]
    apply map.natural
    simpa [expansionRegisteredCycleBase,expansionOldNode,selectedExpansionBaseState,matchingCycleRecordStart,atNode] using
      safe.records i.val within w hw
  obtain ⟨rep,id⟩ := memory.childRow i
  exact ⟨(keep 0 (by decide)).trans rep,(keep 1 (by decide)).trans id⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionPublishedNodes

/-! matching/MatchingExpansionTopTable.lean -/
section RppSource_MatchingExpansionTopTable
namespace VehicleRoutingSurvey.Routing

/-- Relating the new child rows to the previous top-node table accounts for
every compact vertex, including previously hidden vertices that stay hidden. -/
theorem MatchingExpansionChildPorts.topAfter {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {B : Finset (Fin k)} (ports : MatchingExpansionChildPorts state B)
    (chosen : B ∈ Finset.univ.image part.blocks.block) (present : B ∈ state.cuts) (zero : state.cutDual B = 0)
    (internal : state.InternalCuts)
    (external : ∀ p ∈ ports.ports, ∀ w, state.partialMate p = some w → w ∉ ports.block p)
    {base : Fin k} (baseBlock : part.blocks.block base = B) (baseFixed : part.representative base = base)
    (basePort : base ∈ ports.ports) (node : Finset (Fin k) → ℕ) (v : Fin k) :
    let opened := part.openZeroCut chosen present zero (ports.toExpansionChildren internal external)
    (if v ∈ ports.ports then (if (ports.block v).card = 1 then 0 else node (ports.block v))
      else if part.representative v = v ∧ (part.blocks.block v).card ≠ 1 then node (part.blocks.block v) else 0) =
      if opened.representative v = v ∧ (opened.blocks.block v).card ≠ 1 then node (opened.blocks.block v) else 0 := by
  intro opened
  have split := part.openZeroCut_block chosen present zero (ports.toExpansionChildren internal external) v
  have newRep : opened.representative v = if v ∈ B then ports.owner v else part.representative v := rfl
  by_cases port : v ∈ ports.ports
  · have child := ports.containsPort v port
    have inside := ports.subset v port child
    have self := ports.unique v port v child
    have newBlock : opened.blocks.block v = ports.block v := by
      rw [split,if_pos inside]
      change ports.block (ports.owner v) = _
      rw [self]
    by_cases one : (ports.block v).card = 1 <;> simp [port,newRep,inside,self,newBlock,one]
  · rw [if_neg port]
    by_cases inside : v ∈ B
    · have oldRep : part.representative v = base :=
        (part.same_block.mpr (((part.block_eq_iff_member chosen v).mpr inside).trans baseBlock.symm)).trans baseFixed
      have different : base ≠ v := fun h => port (h ▸ basePort)
      have hidden : ports.owner v ≠ v := fun h => port (h ▸ (ports.covered v inside).1)
      simp [oldRep,different,newRep,inside,hidden]
    · have newBlock : opened.blocks.block v = part.blocks.block v := by simpa only [if_neg inside] using split
      simp [inside,newRep,newBlock]

/-- The publication loop overwrites exactly the node words of the cycle
children. All other vertex-indexed words in the old node table survive. -/
theorem ExpansionPublication.topTable {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    {e : MatchingLiveCycle state node B} {s t : ArithmeticState} (pub : ExpansionPublication s t)
    (size : s.nr 55 = k) (space : s.nr 57+k ≤ s.nr 74)
    (rows : s.nr 19 = e.geometry.cycle.length ∧ ∀ i : Fin e.geometry.cycle.length,
      let cell := expansionCycleRow s i.val
      let p := e.geometry.cycle.get i
      cell.representative = p.val ∧ cell.node = if (e.ports.block p).card = 1 then 0 else node (e.ports.block p)) :
    ∀ v : Fin k, blossomNodeAt t v.val = if v ∈ e.ports.ports then
      (if (e.ports.block v).card = 1 then 0 else node (e.ports.block v)) else blossomNodeAt s v.val := by
  intro v
  simp only [blossomNodeAt,pub.fixed 74 (by decide)]
  by_cases port : v ∈ e.ports.ports
  · rw [if_pos port]
    obtain ⟨i,hi,equal⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp (e.geometry.ports ▸ port))
    let ix : Fin e.geometry.cycle.length := ⟨i,hi⟩
    have key : e.geometry.cycle.get ix = v := equal
    obtain ⟨rep,id⟩ := rows.2 ix
    have actual := pub.nodes i (rows.1.symm ▸ hi)
    have word : (expansionCycleRow s i).representative = v.val := rep.trans (congrArg Fin.val key)
    rw [word] at actual
    exact actual.trans (by simpa only [key] using! id)
  · rw [if_neg port]
    apply pub.natural _ (.inr (by omega))
    intro j hj equal
    let ix : Fin e.geometry.cycle.length := ⟨j,rows.1 ▸ hj⟩
    have rep := (rows.2 ix).1
    have same : v = e.geometry.cycle.get ix := Fin.ext ((Nat.add_left_cancel equal).trans rep)
    apply port
    rw [same,e.geometry.ports,List.mem_toFinset]
    exact List.getElem_mem ix.isLt

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionTopTable

/-! matching/MatchingExpansionCoreFrame.lean -/
section RppSource_MatchingExpansionCoreFrame
namespace VehicleRoutingSurvey.Routing

theorem MatchingStageStorage.expansion {k : ℕ} {original s : ArithmeticState}
    (storage : MatchingStageStorage k original s) : MatchingExpansionStorage k s := by
  obtain ⟨warm,_,nodes,_,starts,lengths,left,right,marks,witnesses,records,promotion,mask,map,stack,_⟩ := storage
  have rep := warm.candidatesAfter
  have cache := warm.pairsAfter
  constructor <;> omega





theorem matchingExpansionCoreFrame {k : ℕ} {original s m a p t : ArithmeticState} {tree : MatchingMemberTree}
    {forest : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)}
    {tightRep tightOriginal : Sym2 (Fin k) → Prop} {rep : Fin k → Fin k}
    {entry base : ℕ} (storage : MatchingStageStorage k original s)
    (map : ExpansionMemberMapResult s m tree) (arc : ExpansionArcReady m a entry base)
    (pub : ExpansionPublication a p) (forestExit : MatchingExpandedForest forest mate tightRep tightOriginal rep p t)
    (entryIn : entry < expansionRegisteredCycleLength m) (baseIn : base < expansionRegisteredCycleLength m)
    (count : expansionRegisteredCycleLength m ≤ k)
    (row : ∀ j < a.nr 19, (expansionCycleRow a j).representative < k) :
    MatchingExpansionCoreFrame k s t := by
  have mReg (r : ℕ) (h : r ∉ [0,6,7,15,16,17,18,19,22,23,24,25,26,28,87,97] := by decide) := map.fixed r h
  have aReg (r : ℕ) (h : r ∉ expansionArcScratch := by decide) := arc.fixed r h
  have pReg (r : ℕ) (h : r ∉ [0,6,7,10,15,16,17,25] := by decide) := pub.fixed r h
  have dimension := storage.warm.size
  have rep := storage.warm.representativesAfter
  have ids := storage.warm.candidatesAfter
  have pairs := storage.warm.pairsAfter
  have starts := storage.starts
  obtain ⟨repNodes,nodesWitness,witnessPath,pathMap,mapStack⟩ := storage.expansion
  have short := expansionArcLength_lt entryIn baseIn
  refine ⟨?_,forestExit.real.trans (pub.real.trans (arc.real.trans map.real)),
    forestExit.realRegisters.trans (pub.realRegisters.trans (arc.realRegisters.trans map.realRegisters)),?_⟩
  · intro addr span
    have before : addr < s.nr 79 ∨ s.nr 80+3*k ≤ addr := by
      rcases span with h | ⟨lo,hi⟩ | ⟨lo,hi⟩ | h <;> omega
    have outside : outsideMatchingMemberScratch s addr := by
      unfold outsideMatchingMemberScratch
      rcases before with h | h
      · exact ⟨.inl h,.inl (by omega)⟩
      · exact ⟨.inr (by omega),.inr (by omega)⟩
    have path : addr < m.nr 86 ∨ m.nr 86+3*(expansionArcLength (expansionRegisteredCycleLength m) entry base+1) ≤ addr := by
      rw [mReg 86]
      rcases span with h | ⟨lo,hi⟩ | ⟨lo,hi⟩ | h
      · exact .inl (by omega)
      · exact .inl (by omega)
      · exact .inl (by omega)
      · exact .inr (by omega)
    have repSafe : addr < a.nr 57 ∨ a.nr 57 + a.nr 55 ≤ addr := by
      rw [aReg 57,mReg 57,aReg 55,mReg 55,dimension]
      rcases span with h | ⟨lo,hi⟩ | ⟨lo,hi⟩ | h
      · exact .inl (by omega)
      all_goals exact .inr (by omega)
    have nodeSafe (j : ℕ) (hj : j < a.nr 19) : addr ≠ a.nr 74+(expansionCycleRow a j).representative := by
      rw [aReg 74,mReg 74]
      have bounded := row j hj
      rcases span with h | ⟨lo,hi⟩ | ⟨lo,hi⟩ | h <;> omega
    have roles : addr < p.nr 51 ∨ p.nr 51+k+k+k ≤ addr := by
      rw [pReg 51,aReg 51,mReg 51]
      rcases span with h | ⟨lo,hi⟩ | ⟨lo,hi⟩ | h
      · exact .inl h
      all_goals exact .inr (by omega)
    have links : addr < p.nr 90 ∨ p.nr 90+k+k ≤ addr := by
      rw [pReg 90,aReg 90,mReg 90]
      rcases span with h | ⟨lo,hi⟩ | ⟨lo,hi⟩ | h
      · exact .inl (by omega)
      · exact .inl (by omega)
      · exact .inl hi
      · exact .inr (by omega)
    exact (forestExit.natural _ roles links).trans ((pub.natural _ repSafe nodeSafe).trans
      ((arc.natural _ path).trans (map.natural _ outside)))
  · intro r high away
    apply (forestExit.fixed r high).trans
    apply (pub.fixed r (by simp at *; omega)).trans
    apply (arc.fixed r (by simp [expansionArcScratch] at *; omega)).trans
    exact map.fixed r (by simp at *; omega)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionCoreFrame

/-! matching/MatchingExpansionModel.lean -/
section RppSource_MatchingExpansionModel
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Instantiate the relabeling model at the new partition. All original tight
edges retain their values upon erasing the zero cut. The concrete output
witnesses supply the new quotient tightness in `ExpansionPersistentState.toSearch`. -/
theorem MatchingExpansionGeometry.model {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state} {B : Finset (Fin k)}
    {registry : MatchingExpansionChildPorts state B} {tree : MatchingMemberTree} {source base : Fin k}
    (g : MatchingExpansionGeometry registry tree base) (top : CompactTopMatching part)
    (chosen : B ∈ Finset.univ.image part.blocks.block) (present : B ∈ state.cuts) (zero : state.cutDual B = 0)
    (baseFixed : part.representative base = base) (baseBlock : part.blocks.block base = B)
    (internal : state.InternalCuts) {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    (search : CompactMatchingSearchForest part forest state.partialMate part.tightBetween)
    (inner : forest.role base = .inner source)
    (encoding : AlternatingForestMemory forest (s.nr 51) s.nm)
    (witnesses : MatchingForestOriginalWitnesses part forest s) (links : MatchingForestLinkMemory part forest s)
    (entrySlot : Fin g.cycle.length) (incoming : Fin k × Fin k)
    (first : part.representative incoming.1 = source) (inside : incoming.2 ∈ B)
    (target : registry.owner incoming.2 = g.cycle[entrySlot.val])
    (tight : oddCutDualEdgeValue state.cuts state.potential state.cutDual s(incoming.1,incoming.2) =
      edgeCost cost s(incoming.1,incoming.2)) :
    let external := g.exposesPorts top baseFixed baseBlock
    let opened := part.openZeroCut chosen present zero (registry.toExpansionChildren internal external)
    let next := state.eraseZeroCut present zero
    ExpansionModelInput s forest next.partialMate (fun _ => True)
      (fun e => oddCutDualEdgeValue next.cuts next.potential next.cutDual e = edgeCost cost e)
      opened.representative g.cycle g.edges entrySlot g.baseSlot source base g.children incoming := by
  intro external opened next
  have basePort : base ∈ registry.ports := g.rotatedPorts.symm ▸ List.mem_toFinset.mpr List.mem_cons_self
  have sourceAway : source ≠ base := by
    have row := search.valid base
    rw [inner] at row
    obtain ⟨p, isOuter⟩ := row.1
    intro eq
    rw [eq, inner] at isOuter
    contradiction
  have other := (registry.openRep chosen present zero internal external baseBlock baseFixed basePort).2
  have distinct : (base :: g.children).Nodup := by rw [← g.rotate, List.nodup_rotate]; exact g.distinct
  have newTight (e : Sym2 (Fin k)) (old : oddCutDualEdgeValue state.cuts state.potential state.cutDual e = edgeCost cost e) :
      oddCutDualEdgeValue next.cuts next.potential next.cutDual e = edgeCost cost e :=
    (oddCutDualEdgeValue_erase_zero _ present _ _ zero e).trans old
  have openPort (v p : Fin k) (port : p ∈ registry.ports) (has : v ∈ registry.block p) :
      opened.representative v = p := by
    change (if v ∈ B then registry.owner v else part.representative v) = p
    rw [if_pos (registry.subset _ port has), registry.unique _ port _ has]
  have indexed (i : Fin g.cycle.length) : g.cycle[i.val] ∈ registry.ports :=
    g.ports.symm ▸ List.mem_toFinset.mpr (List.getElem_mem i.isLt)
  have exactBase : base ∈ matchingExpansionPhysicalPath g.cycle entrySlot g.baseSlot := by
    rw [matchingExpansionPhysicalPath_eq_rotated _ _ _ g.odd, g.atBase, g.rotate]
    unfold blossomExpansionPath
    split <;> simp
  refine ⟨encoding, AlternatingForestState.valid_of_parent_tight search.valid (fun _ => True.intro), inner,
    registry.dormant chosen g.children g.rotatedPorts distinct baseBlock baseFixed links.inactive,
    fun _ _ => True.intro, True.intro, g.matched, ?_, ?_, ?_⟩
  · have inOwner : opened.representative incoming.2 = registry.owner incoming.2 := by
      change (if incoming.2 ∈ B then registry.owner incoming.2 else part.representative incoming.2) = _
      rw [if_pos inside]
    exact ⟨Prod.ext ((other _ (fun eq => sourceAway (first.symm.trans eq))).trans first) (inOwner.trans target),
      newTight _ tight⟩
  · intro i
    let j : Fin g.cycle.length := ⟨(i.val+1) % g.cycle.length, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    exact ⟨Prod.ext (openPort _ _ (indexed i) (g.source i)) (openPort _ _ (indexed j) (g.target i)),
      newTight _ (g.tight i)⟩
  · intro child parent offPath linked
    exact registry.retainedWitness chosen present zero internal external baseBlock baseFixed basePort witnesses search.valid
      inner (fun _ h => links.matched h) child parent (fun eq => offPath (eq.symm ▸ exactBase)) linked

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionModel

/-! matching/MatchingExpansionExactLinks.lean -/
section RppSource_MatchingExpansionExactLinks
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



theorem MatchingLiveCycle.exactModel {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    {part : CompactMatchingPartition state} {B : Finset (Fin k)} {node : Finset (Fin k) → ℕ}
    (e : MatchingLiveCycle state node B) {forest : AlternatingForestState (Fin k)} {source : Fin k}
    {s : ArithmeticState} (top : CompactTopMatching part)
    (chosen : B ∈ Finset.univ.image part.blocks.block) (present : B ∈ state.cuts) (zero : state.cutDual B = 0)
    (baseFixed : part.representative e.base = e.base) (baseBlock : part.blocks.block e.base = B)
    (internal : state.InternalCuts) (inner : forest.role e.base = .inner source)
    (links : MatchingForestLinkMemory part forest s)
    (entry : Fin e.geometry.cycle.length) (incoming : Fin k × Fin k) (incomingRep : part.representative incoming.1 = source) :
    let g := e.geometry
    let opened := part.openZeroCut chosen present zero
      (e.ports.toExpansionChildren internal (g.exposesPorts top baseFixed baseBlock))
    let next := state.eraseZeroCut present zero
    ∀ model : ExpansionModelInput s forest next.partialMate (fun _ => True)
        (fun f => oddCutDualEdgeValue next.cuts next.potential next.cutDual f = edgeCost cost f)
        opened.representative g.cycle g.edges entry g.baseSlot source e.base g.children incoming,
      ExpansionModelInput s forest next.partialMate (fun _ => True) (matchingExactExpansionEdge next opened.representative)
        opened.representative g.cycle g.edges entry g.baseSlot source e.base g.children incoming := by
  intro g opened next model
  have mateEq : next.partialMate = state.partialMate := state.partialMate_eraseZeroCut present zero
  have valid : forest.valid state.partialMate (fun _ _ => True) := mateEq ▸ model.valid
  have inCycle (i : Fin g.cycle.length) : g.cycle.get i ∈ e.ports.ports := by
    rw [g.ports,List.mem_toFinset]
    exact List.getElem_mem i.isLt
  refine ⟨model.encoding,model.valid,model.baseInner,model.dormant,model.tightCycle,model.tightEntry,
    model.childMates,⟨model.incomingEdge.1,model.incomingEdge.2,?_⟩,?_,?_⟩
  · intro projected
    have ends := model.incomingEdge.1
    have matched : s(source,g.cycle.get entry) ∈ state.edges := by
      have head : opened.representative incoming.1 = source := congrArg Prod.fst ends
      have tail : opened.representative incoming.2 = g.cycle.get entry := congrArg Prod.snd ends
      change s(opened.representative incoming.1,opened.representative incoming.2) ∈ state.edges at projected
      rwa [head,tail] at projected
    have srcFixed : part.representative source = source := by simpa only [incomingRep] using part.representative_idem incoming.1
    have incomingPort := inCycle entry
    have member := e.ports.subset _ incomingPort (e.ports.containsPort _ incomingPort)
    have oldBase : part.representative (g.cycle.get entry) = e.base :=
      (part.same_block.mpr (((part.block_eq_iff_member chosen _).mpr member).trans baseBlock.symm)).trans baseFixed
    have oldRow := valid e.base
    rw [inner] at oldRow
    have distinct : source ≠ e.base := by
      obtain ⟨p,h⟩ := oldRow.1
      intro same
      rw [same,inner] at h
      contradiction
    have crossing := top.crossing_endpoints matched (fun same =>
      distinct (srcFixed.symm.trans ((part.same_block.mpr same).trans oldBase)))
    have same := crossing.2.symm.trans oldBase
    rw [same] at matched
    exact (oldRow.2.1 (state.partialMate_some_iff.mpr (Sym2.eq_swap ▸ matched))).elim
  · intro i
    have ends := (model.cycleEdges i).1
    refine ⟨ends,(model.cycleEdges i).2,?_⟩
    intro projected
    let j : Fin g.cycle.length := ⟨(i.val+1)%g.cycle.length,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    have matched : s(g.cycle.get i,g.cycle.get j) ∈ state.edges := by
      have head : opened.representative (g.edges i).1 = g.cycle.get i := congrArg Prod.fst ends
      have tail : opened.representative (g.edges i).2 = g.cycle.get j := congrArg Prod.snd ends
      change s(opened.representative (g.edges i).1,opened.representative (g.edges i).2) ∈ state.edges at projected
      rwa [head,tail] at projected
    have atRow := e.matchedRow i (state.partialMate_some_iff.mpr matched)
    change s((g.edges i).1,(g.edges i).2) ∈ state.edges
    rw [atRow]
    exact matched
  · intro child parent outside attached
    obtain ⟨edge,words,ends,tight⟩ := model.retained child parent outside attached
    refine ⟨edge,words,ends,tight,?_⟩
    intro projected
    have matched : s(parent,child) ∈ state.edges := by
      have head : opened.representative edge.1 = parent := congrArg Prod.fst ends
      have tail : opened.representative edge.2 = child := congrArg Prod.snd ends
      change s(opened.representative edge.1,opened.representative edge.2) ∈ state.edges at projected
      rwa [head,tail] at projected
    rcases parent_step_roles valid attached with ⟨_,outer,_,_⟩ | ⟨_,inside,_⟩
    · have equal := words.symm.trans (links.matched outer)
      have a : edge.1 = parent := Fin.ext (congrArg Prod.fst equal)
      have b : edge.2 = child := Fin.ext (congrArg Prod.snd equal)
      change s(edge.1,edge.2) ∈ state.edges
      simpa only [a,b] using matched
    · have row := valid child
      rw [inside] at row
      exact (row.2.1 (state.partialMate_some_iff.mpr (Sym2.eq_swap ▸ matched))).elim



end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionExactLinks

/-! matching/MatchingExpansionCoreDual.lean -/
section RppSource_MatchingExpansionCoreDual
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Interpret the representative, top-node, role and both dual tables at the
actual relabelling exit. The exhausted cut disappears from the domain while
each surviving cut keeps its allocated ID. -/
noncomputable def MatchingLiveCycleMemory.openedDual {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {B : Finset (Fin k)} {forest after : AlternatingForestState (Fin k)}
    {original s m a p t : ArithmeticState} (prior : MatchingSearchDualMemory part forest s)
    {e : MatchingLiveCycle state prior.node B} (memory : MatchingLiveCycleMemory e s)
    (storage : MatchingStageStorage k original s) (chosen : B ∈ Finset.univ.image part.blocks.block)
    (present : B ∈ state.cuts) (zero : state.cutDual B = 0) (internal : state.InternalCuts)
    (top : CompactTopMatching part) (baseFixed : part.representative e.base = e.base) (baseBlock : part.blocks.block e.base = B)
    (atNode : s.nm (s.nr 74+s.nr 92) = prior.node B) (baseWord : s.nr 92 = e.base.val)
    (mapped : ExpansionMemberMapResult s m e.tree) (layout : ExpansionInputLayout k m)
    {entry : Fin e.geometry.cycle.length} (arc : ExpansionArcReady m a entry.val e.geometry.baseSlot.val)
    (pub : ExpansionPublication a p) {mate : Fin k → Option (Fin k)}
    {tightRep tightOriginal : Sym2 (Fin k) → Prop} {rep : Fin k → Fin k}
    (exit : MatchingExpandedForest after mate tightRep tightOriginal rep p t) :
    let external := e.geometry.exposesPorts top baseFixed baseBlock
    let opened := part.openZeroCut chosen present zero (e.ports.toExpansionChildren internal external)
    { dual : MatchingSearchDualMemory opened after t // dual.node = prior.node } := by
  intro external opened
  have dim := storage.warm.size
  have forestReps := storage.warm.representativesAfter
  obtain ⟨repsNodes,nodesWitness,witnessPath,pathMap,mapStack⟩ := storage.expansion
  have mReg (r : ℕ) (h : r ∉ [0,6,7,15,16,17,18,19,22,23,24,25,26,28,87,97] := by decide) := mapped.fixed r h
  have aReg (r : ℕ) (h : r ∉ expansionArcScratch := by decide) := arc.fixed r h
  have pReg (r : ℕ) (h : r ∉ [0,6,7,10,15,16,17,25] := by decide) := pub.fixed r h
  have reg (r : ℕ) (high : 30 ≤ r := by decide)
      (hm : r ∉ [0,6,7,15,16,17,18,19,22,23,24,25,26,28,87,97] := by decide)
      (ha : r ∉ expansionArcScratch := by decide) (hp : r ∉ [0,6,7,10,15,16,17,25] := by decide) :
      t.nr r = s.nr r := (exit.fixed r high).trans ((pReg r hp).trans ((aReg r ha).trans (mReg r hm)))
  have bound := e.base.isLt
  have topSafe : outsideMatchingMemberScratch s (s.nr 74+s.nr 92) := by
    rw [baseWord]
    exact ⟨.inl (by omega),.inl (by omega)⟩
  have childRows := memory.arcRows atNode topSafe mapped layout arc
  have length := arc.cycleLength.symm.trans childRows.1
  have count : e.geometry.cycle.length ≤ k := by simpa using e.geometry.distinct.length_le_card
  have arcRoom : m.nr 86+3*expansionRegisteredCycleLength m ≤ m.nr 79 := by
    rw [mReg 86,mReg 79,length]; omega
  have mapRead (v : Fin k) : a.nm (a.nr 79+v.val) = if v ∈ B then (e.ports.owner v).val else k :=
    (arc.keepsMembers (length.symm ▸ entry.isLt) (length.symm ▸ e.geometry.baseSlot.isLt) arcRoom v.val).trans
      (mapped.encodesChildPorts e.geometry.members dim v)
  have early (addr : ℕ) (lo : addr < s.nr 86) : a.nm addr = s.nm addr :=
    (arc.natural _ (.inl ((mReg 86).symm ▸ lo))).trans (mapped.natural _ ⟨.inl (by omega),.inl (by omega)⟩)
  have pSize : a.nr 55 = k := (aReg 55).trans ((mReg 55).trans dim)
  have forestFrame (addr : ℕ) (lo : s.nr 57 ≤ addr) (hi : addr < s.nr 90) : t.nm addr = p.nm addr := by
    apply exit.natural _ (.inr ?_) (.inl ?_)
    · rw [pReg 51,aReg 51,mReg 51]; omega
    · rwa [pReg 90,aReg 90,mReg 90]
  have pubReps (v : Fin k) : p.nm (p.nr 57+v.val) = (opened.representative v).val := by
    have read := mapRead v
    have range := v.isLt
    by_cases member : v ∈ B
    · rw [if_pos member] at read
      simpa only [opened,CompactMatchingPartition.openZeroCut,MatchingExpansionChildPorts.toExpansionChildren,
        if_pos member] using pub.childRepresentative pSize read
    · rw [if_neg member] at read
      have old := pub.keptRepresentative pSize read
      rw [aReg 57,mReg 57,early _ (by omega),prior.reps] at old
      simpa only [opened,CompactMatchingPartition.openZeroCut,if_neg member] using old
  have basePort : e.base ∈ e.ports.ports := by
    rw [e.geometry.rotatedPorts,List.mem_toFinset]
    exact List.mem_cons_self
  have real := exit.real.trans (pub.real.trans (arc.real.trans mapped.real))
  refine ⟨⟨(reg 55).trans dim,?_,?_,?_,?_,prior.node,?_,?_,?_,?_⟩,rfl⟩
  · rw [reg 62,reg 75]
    exact prior.separated
  · intro v
    have boundV := v.isLt
    have stored := pubReps v
    rw [pReg 57,aReg 57,mReg 57] at stored
    rw [reg 57,forestFrame _ (by omega) (by omega)]
    exact stored
  · rw [exit.fixed 51 (by decide)]
    exact exit.encoding
  · intro v
    rw [reg 62,real,prior.effective]
    exact (effectiveVertexPotential_erase_zero _ present _ _ zero v).symm
  · intro C belongs
    exact prior.nodeNonzero C (Finset.mem_of_mem_erase belongs)
  · intro C member D belongs eq
    exact prior.nodeInjective (Finset.mem_of_mem_erase member) (Finset.mem_of_mem_erase belongs) eq
  · intro C belongs
    rw [reg 75,real]
    exact prior.cutValues C (Finset.mem_of_mem_erase belongs)
  · intro v
    have range := v.isLt
    have staged := pub.topTable pSize (by rw [aReg 57,mReg 57,aReg 74,mReg 74]; exact repsNodes) childRows v
    have before : blossomNodeAt a v.val = blossomNodeAt s v.val := by
      unfold blossomNodeAt
      rw [aReg 74,mReg 74,early _ (by omega)]
    rw [before,prior.top] at staged
    have tail := e.ports.topAfter chosen present zero internal external baseBlock baseFixed basePort prior.node v
    change t.nm (t.nr 74+v.val) = _
    rw [reg 74,forestFrame _ (by omega) (by omega)]
    change p.nm (p.nr 74+v.val) = _ at staged
    rw [pReg 74,aReg 74,mReg 74] at staged
    exact staged.trans tail

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionCoreDual

/-! matching/MatchingExpansionMappedModel.lean -/
section RppSource_MatchingExpansionMappedModel
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

theorem ExpansionMemberMapResult.forestTables {k : ℕ} {s t : ArithmeticState} {tree : MatchingMemberTree}
    (mapped : ExpansionMemberMapResult s t tree) (warm : MatchingWarmLayout s k)
    (storage : MatchingExpansionStorage k s) {forest : AlternatingForestState (Fin k)}
    (roles : AlternatingForestMemory forest (s.nr 51) s.nm) :
    AlternatingForestMemory forest (t.nr 51) t.nm ∧
    ∀ v : Fin k, matchingForestWitnessAt t.nm (t.nr 90) v.val = matchingForestWitnessAt s.nm (s.nr 90) v.val := by
  obtain ⟨repNode, nodeWitness, witnessPath, pathMap, mapStack⟩ := storage
  have roleBound := warm.representativesAfter
  have keep (a : ℕ) (early : a < s.nr 79) : t.nm a = s.nm a :=
    mapped.natural a ⟨.inl early, .inl (by omega)⟩
  constructor
  · intro v
    have within := v.isLt
    rw [mapped.fixed 51 (by decide), keep _ (by omega), keep _ (by omega), keep _ (by omega)]
    exact roles v
  · intro v
    have within := v.isLt
    simp only [matchingForestWitnessAt, forestWitnessAddress, mapped.fixed 90 (by decide)]
    exact Prod.ext (keep _ (by omega)) (keep _ (by omega))

/-- At the exhausted dual point the mapped rows determine the entry child and
the path model used by the executable. The three handler premises are jointly
derived from the incoming forest and the persistent selected cycle. -/
theorem MatchingExpansionGeometry.mappedInputs {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {B : Finset (Fin k)}
    {chosen s t : ArithmeticState} {tree : MatchingMemberTree} {registry : MatchingExpansionChildPorts state B}
    (event : MatchingSelectedExpansion part forest positive chosen B)
    (g : MatchingExpansionGeometry registry tree event.base) (top : CompactTopMatching part)
    (zero : state.cutDual B = 0) (internal : state.InternalCuts)
    (dual : MatchingSearchDualMemory part forest s)
    (search : CompactMatchingSearchForest part forest state.partialMate part.tightBetween)
    (witnesses : MatchingForestOriginalWitnesses part forest s) (links : MatchingForestLinkMemory part forest s)
    (root : MatchingMemberRoot (topMatchingMemberNodeInput (selectedExpansionBaseState s)) tree)
    (rows : ExpansionCycleWitnessRows (selectedExpansionBaseState s) g.cycle g.edges)
    (selected : s.nr 92 = event.base.val) (warm : MatchingWarmLayout s k)
    (storage : MatchingExpansionStorage k s) (unit : s.nr 9 = 1) (zeroWord : s.nr 14 = 0)
    (mapped : ExpansionMemberMapResult s t tree) :
    let external := g.exposesPorts top event.active event.block
    let opened := part.openZeroCut event.top event.present zero (registry.toExpansionChildren internal external)
    let next := state.eraseZeroCut event.present zero
    ∃ (entrySlot : Fin g.cycle.length) (incoming : Fin k × Fin k),
      part.representative incoming.1 = event.parent ∧ ExpansionInputLayout k t ∧
      ExpansionCycleInput t g.cycle g.edges entrySlot g.baseSlot event.parent event.base g.children incoming ∧
      ExpansionModelInput t forest next.partialMate (fun _ => True)
        (fun e => oddCutDualEdgeValue next.cuts next.potential next.cutDual e = edgeCost cost e)
        opened.representative g.cycle g.edges entrySlot g.baseSlot event.parent event.base g.children incoming := by
  intro external opened next
  obtain ⟨entrySlot, incoming, words, source, inside, target, tight⟩ :=
    g.incoming event.top event.active event.block event.inner witnesses
  have encoded := dual.roles
  obtain ⟨forestNow, wordFrame⟩ := mapped.forestTables warm storage encoded
  have current : MatchingForestOriginalWitnesses part forest t := by
    intro child parent h
    obtain ⟨a,b,witness,first,second,value⟩ := witnesses h
    exact ⟨a,b,(wordFrame child).trans witness,first,second,value⟩
  have parentAway : event.parent ≠ event.base := by
    have valid := search.valid event.base
    rw [event.inner] at valid
    obtain ⟨prior, outer⟩ := valid.1
    intro same
    rw [same, event.inner] at outer
    contradiction
  have bv := event.base.isLt
  have nodeSafe : outsideMatchingMemberScratch s (s.nr 74+s.nr 92) := by
    obtain ⟨_, nodes, witness, path, stack⟩ := storage
    rw [selected]
    exact ⟨.inl (by omega), .inl (by omega)⟩
  have safe := root.expansionCycleRead nodeSafe
  have space := storage
  obtain ⟨repNode, nodeWitness, witnessPath, pathMap, mapStack⟩ := space
  have parents := warm.parents
  have forestReps := warm.representativesAfter
  have cycle := mapped.cycleInput g.members warm.size selected rows safe (by omega) (by omega) (by omega) (by omega)
    encoded parents event.inner g.distinct g.odd g.rotate g.atBase words
    ((dual.reps incoming.1).trans (congrArg Fin.val source)) parentAway inside target
  exact ⟨entrySlot, incoming, source, mapped.layout warm storage unit zeroWord rows g.distinct root (selected.symm ▸ bv), cycle,
    g.model top event.top event.present zero event.active event.block internal search event.inner forestNow current
      (links.advance rfl wordFrame) entrySlot incoming source inside target tight⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionMappedModel

/-! matching/MatchingExpansionOpenedCore.lean -/
section RppSource_MatchingExpansionOpenedCore
namespace VehicleRoutingSurvey.Routing





/-- Execute the member-map and even-arc blocks on an exhausted selected
blossom. The resulting forest carries the original matched parent endpoints,
and its opened dual memory reflects the published child top-node array. -/
theorem MatchingSelectedExpansion.openedCore {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {chosen original s : ArithmeticState}
    {B : Finset (Fin k)} (event : MatchingSelectedExpansion part forest positive chosen B)
    (stage : MatchingAdvancedStage part forest positive (matchingTopCutAt part) original s)
    (live : MatchingLiveCycles stage.registry) (storage : MatchingStageStorage k original s)
    (top : CompactTopMatching part) (internal : state.InternalCuts) (zero : state.cutDual B = 0)
    (selected : s.nr 92 = event.base.val) (pc : s.pc = 0) (running : s.halted = false)
    (one : s.nr 9 = 1) (zeroWord : s.nr 14 = 0) :
    let e := live.entry B event.present
    let g := e.geometry
    let same := (live.selectedBase event).1
    let external := g.exposesPorts top
      (by rw [show e.base = event.base from same]; exact event.active)
      (by rw [show e.base = event.base from same]; exact event.block)
    let opened := part.openZeroCut event.top event.present zero (e.ports.toExpansionChildren internal external)
    let next := state.eraseZeroCut event.present zero
    ∃ (entry : Fin g.cycle.length) (t m a p : ArithmeticState) (ticks : ℕ),
      BlockRuns (appendBlock prepareExpansionChildrenBlock expandMatchingAfterMembersBlock) ticks s t ∧
      t.halted = false ∧ ticks ≤ 207*k+104 ∧ ExpansionMemberMapResult s m e.tree ∧ ExpansionInputLayout k m ∧
      ExpansionArcReady m a entry.val g.baseSlot.val ∧ ExpansionPublication a p ∧
      let after := forest.expandBlossom event.parent e.base g.children (expansionEntryFromBase g.cycle.length entry.val g.baseSlot.val)
      MatchingExpandedForest after next.partialMate (fun _ => True) (matchingExactExpansionEdge next opened.representative)
        opened.representative p t ∧ MatchingExpansionCoreFrame k s t ∧
        ∃ dual : MatchingSearchDualMemory opened after t, dual.node = stage.dual.node := by
  intro e g same external opened next
  have baseAt : e.base = event.base := same
  have fixed : part.representative e.base = e.base := by rw [baseAt]; exact event.active
  have block : part.blocks.block e.base = B := by rw [baseAt]; exact event.block
  let atBase : MatchingSelectedExpansion part forest positive chosen B :=
    ⟨e.base,event.parent,by rw [baseAt]; exact event.ports,event.classTag,block,fixed,
      by rw [baseAt]; exact event.representative,event.top,event.nontrivial,by rw [baseAt]; exact event.inner⟩
  have word : s.nr 92 = e.base.val := selected.trans (congrArg Fin.val same.symm)
  have node : s.nm (s.nr 74+s.nr 92) = stage.dual.node B := by
    rw [selected]; exact (event.registry_node stage.dual event.present).1
  have memory := live.memory B event.present
  have root := memory.expansionRoot node
  have rows := memory.rows.selected node
  obtain ⟨m0,mTicks,mapRun,mLive,mBound,mapped⟩ := prepareExpansionChildrenBlock_spec root pc running one zeroWord
  let m := {m0 with pc := 0}
  have map : ExpansionMemberMapResult s m e.tree := ⟨mapped.selectedBase,mapped.values,mapped.sentinel,mapped.natural,
    mapped.real,mapped.realRegisters,mapped.fixed⟩
  obtain ⟨entry,incoming,incomingRep,layout,cycle,model⟩ :=
    g.mappedInputs atBase top zero internal stage.dual stage.search stage.witnesses stage.links root rows word
      storage.warm storage.expansion one zeroWord map
  have table := map.forestTables storage.warm storage.expansion stage.dual.roles
  have links := stage.links.advance rfl table.2
  have refined := e.exactModel top event.top event.present zero fixed block internal atBase.inner links entry incoming incomingRep model
  obtain ⟨out,a,p,cTicks,commit,done,costLimit,arc,pub,finish⟩ :=
    expandMatchingAfterMembersBlock_spec (s := m) rfl mLive layout cycle refined
  have entire := mapRun.append commit
  let t := relocateState prepareExpansionChildrenBlock.length out
  have exit := finish.relocate prepareExpansionChildrenBlock.length
  have span := cycle.rows.length
  have size : g.cycle.length ≤ k := by simpa using g.distinct.length_le_card
  have safe : outsideMatchingMemberScratch s (s.nr 74+s.nr 92) := by
    obtain ⟨_,nw,wp,pm,ms⟩ := storage.expansion
    have limit := e.base.isLt
    rw [word]
    exact ⟨.inl (by omega),.inl (by omega)⟩
  have childRows := memory.arcRows node safe map layout arc
  have frame := matchingExpansionCoreFrame storage map arc pub exit (span.symm ▸ entry.isLt)
    (span.symm ▸ g.baseSlot.isLt) (span.trans_le size) (fun j hj => by
      let i : Fin g.cycle.length := ⟨j,childRows.1 ▸ hj⟩
      exact (childRows.2 i).1.symm ▸ (g.cycle.get i).isLt)
  have dual := memory.openedDual stage.dual storage event.top event.present zero internal top fixed block node word map layout arc pub exit
  rw [storage.warm.size] at mBound
  exact ⟨entry,t,m,a,p,_,entire,done,by omega,map,layout,arc,pub,exit,frame,dual.val,dual.property⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionOpenedCore

open VehicleRoutingSurvey.Routing SupplyChainTheory in
theorem solution : (fun {P : Prop} (_ : P) => P) (@VehicleRoutingSurvey.Routing.MatchingSelectedExpansion.openedCore) :=
  @VehicleRoutingSurvey.Routing.MatchingSelectedExpansion.openedCore
