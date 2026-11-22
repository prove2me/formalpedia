-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.matchingAugmentationHandlerBlock_primal
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T16:03:24.47145+00:00
-- url     : https://prove2.me/submissions/6c79af8f-e50c-4a9e-8e4f-2fec6faaf7c0

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

theorem arity_le_nodes (tree : MatchingMemberTree) : tree.arity ≤ tree.nodes := by
  induction tree with
  | nil => rfl
  | leaf v siblings ih => simp only [arity, nodes]; omega
  | blossom representative node children siblings _ ih => simp only [arity, nodes]; omega





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

/-! matching/MatchingExpansionDirectionRAM.lean -/
section RppSource_MatchingExpansionDirectionRAM
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













end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionDirectionRAM

/-! matching/MatchingRebasePair.lean -/
section RppSource_MatchingRebasePair
open private orientRebasePairPorts VehicleRoutingSurvey.Routing.orientRebasePairPorts from Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
open private saveRebasePairLeft VehicleRoutingSurvey.Routing.saveRebasePairLeft from Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
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



private def rebasePairLeftSaved (s : ArithmeticState) : ArithmeticState :=
  {s with
    pc := 4
    nr := Function.update (Function.update (Function.update (Function.update s.nr 10 (s.nr 15))
      11 (s.nr 25)) 12 (s.nr 16)) 13 (s.nr 17)}

private theorem saveRebasePairLeft_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (zero : s.nr 14 = 0) :
    BlockRuns saveRebasePairLeft 4 s (rebasePairLeftSaved s) := by
  refine BlockRuns.of_running_exit ?_ (show (rebasePairLeftSaved s).halted = false from running) rfl
  simp [saveRebasePairLeft, rebasePairLeftSaved, arithmeticStep, entry, running, zero,
    Function.iterate_succ_apply']



def matchingRebasePorts (memory : ℕ → ℕ) (mapBase : ℕ) (left : MatchingCycleChild) : ℕ × ℕ :=
  if memory (mapBase + left.endpointA) = left.representative then (left.endpointA, left.endpointB)
  else (left.endpointB, left.endpointA)

private theorem orientRebasePairPorts_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (zero : s.nr 14 = 0) :
    ∃ t steps, steps ≤ 7 ∧ BlockRuns orientRebasePairPorts steps s t ∧ t.halted = false ∧
      (t.nr 12, t.nr 13) = matchingRebasePorts s.nm (s.nr 79) ⟨s.nr 10, s.nr 11, s.nr 12, s.nr 13⟩ ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 12, 13] → t.nr r = s.nr r := by
  have build (steps : ℕ) (budget : steps ≤ 7)
      (effect : let t := (arithmeticStep orientRebasePairPorts)^[steps] s
       t.pc = orientRebasePairPorts.length ∧ t.halted = false ∧
         (t.nr 12, t.nr 13) = matchingRebasePorts s.nm (s.nr 79) ⟨s.nr 10, s.nr 11, s.nr 12, s.nr 13⟩ ∧
         t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr) :
      ∃ t steps, steps ≤ 7 ∧ BlockRuns orientRebasePairPorts steps s t ∧ t.halted = false ∧
        (t.nr 12, t.nr 13) = matchingRebasePorts s.nm (s.nr 79) ⟨s.nr 10, s.nr 11, s.nr 12, s.nr 13⟩ ∧
        t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 12, 13] → t.nr r = s.nr r := by
    obtain ⟨exit, live, ports, natural, real, rr⟩ := effect
    exact ⟨_, steps, budget, BlockRuns.of_running_exit rfl live exit, live, ports, natural, real, rr,
      fun _ safe => arithmeticRun_keeps_from_destination_list _ (by decide) safe s steps⟩
  rcases lt_trichotomy (s.nm (s.nr 79 + s.nr 12)) (s.nr 10) with below | equal | above
  · apply build 7 le_rfl
    simp [orientRebasePairPorts, matchingRebasePorts, arithmeticStep, entry, running, zero,
      below.le, not_le.mpr below, below.ne, Function.iterate_succ_apply']
  · apply build 4 (by decide)
    simp [orientRebasePairPorts, matchingRebasePorts, arithmeticStep, entry, running, equal,
      Function.iterate_succ_apply']
  · apply build 6 (by decide)
    simp [orientRebasePairPorts, matchingRebasePorts, arithmeticStep, entry, running, zero,
      not_le.mpr above, above.ne', Function.iterate_succ_apply']



set_option maxRecDepth 4096 in
theorem readRebasedCyclePairBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (inside : s.nr 7 < s.nr 19) :
    let next := (s.nr 7 + 1) % s.nr 19
    let left := matchingCycleChildAt s.nm (s.nr 18 + 4 * s.nr 7)
    let right := matchingCycleChildAt s.nm (s.nr 18 + 4 * next)
    ∃ t steps, steps ≤ 34 ∧ BlockRuns readRebasedCyclePairBlock steps s t ∧ t.halted = false ∧
      t.nr 7 = next ∧ (t.nr 10, t.nr 11) = (left.representative, left.node) ∧
      (t.nr 15, t.nr 25) = (right.representative, right.node) ∧
      (t.nr 12, t.nr 13) = matchingRebasePorts s.nm (s.nr 79) left ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 7, 10, 11, 12, 13, 15, 16, 17, 25] → t.nr r = s.nr r := by
  intro next left right
  obtain ⟨a, readLeft, aReady, leftRead, aNat, aReal, aRR, aGet⟩ := readMatchingCycleChild_spec s entry running one
  let aInput := {a with pc := 0}
  have aZero : aInput.nr 14 = 0 := (aGet 14 (by decide)).trans zero
  have saved := saveRebasePairLeft_correct (s := aInput) rfl aReady aZero
  let beforeAdvance := {relocateState readMatchingCycleChild.length (rebasePairLeftSaved aInput) with pc := 0}
  have carry (r : ℕ) (safe : r ∉ [10, 11, 12, 13] := by decide) : beforeAdvance.nr r = a.nr r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at safe
    obtain ⟨h10, h11, h12, h13⟩ := safe
    simp [beforeAdvance, rebasePairLeftSaved, aInput, relocateState, h10, h11, h12, h13]
  have oneAt : beforeAdvance.nr 9 = 1 := (carry 9).trans ((aGet 9 (by decide)).trans one)
  have indexAt : beforeAdvance.nr 7 = s.nr 7 := (carry 7).trans (aGet 7 (by decide))
  have countAt : beforeAdvance.nr 19 = s.nr 19 := (carry 19).trans (aGet 19 (by decide))
  obtain ⟨advanceSteps, advanceBound, advance⟩ := advanceMatchingCycleIndexBlock_correct
    (s := beforeAdvance) rfl aReady oneAt (by rwa [indexAt, countAt])
  let advanced := {beforeAdvance with pc := 3, nr := Function.update beforeAdvance.nr 7 next}
  have advancedRun : BlockRuns advanceMatchingCycleIndexBlock advanceSteps beforeAdvance advanced := by
    simpa only [advanced, indexAt, countAt, next] using advance
  let prefixCode := appendBlock (appendBlock readMatchingCycleChild saveRebasePairLeft) advanceMatchingCycleIndexBlock
  let readInput := {relocateState (appendBlock readMatchingCycleChild saveRebasePairLeft).length advanced with pc := 0}
  have keep (r : ℕ) (safe : r ≠ 7 := by decide) : readInput.nr r = beforeAdvance.nr r := by
    simp [readInput, advanced, relocateState, safe]
  have readOne : readInput.nr 9 = 1 := (keep 9).trans oneAt
  obtain ⟨d, readRight, dReady, rightRead, dNat, dReal, dRR, dGet⟩ := readMatchingCycleChild_spec readInput rfl aReady readOne
  have rightRead' : readMatchingCycleChildValue d = right := by
    have fixed := (keep 18).trans ((carry 18).trans (aGet 18 (by decide)))
    have idx : readInput.nr 7 = next := by simp [readInput, advanced, relocateState]
    simpa only [fixed, idx, show readInput.nm = s.nm from aNat, right] using rightRead
  let orientInput := {relocateState prefixCode.length d with pc := 0}
  have orientFixed (r : ℕ) (safe : r ∉ [0, 6, 15, 16, 17, 25] := by decide) :
      orientInput.nr r = readInput.nr r := dGet r safe
  have orientZero : orientInput.nr 14 = 0 :=
    (orientFixed 14).trans ((keep 14).trans ((carry 14).trans aZero))
  obtain ⟨e, orientSteps, orientBound, oriented, live, ports, eNat, eReal, eRR, eGet⟩ :=
    orientRebasePairPorts_correct (s := orientInput) rfl dReady orientZero
  let t := relocateState (appendBlock prefixCode readMatchingCycleChild).length e
  have joined : BlockRuns readRebasedCyclePairBlock (10 + 4 + advanceSteps + 10 + orientSteps) s t :=
    (((readLeft.append saved).append advancedRun).append readRight).append oriented
  have leftBytes : (⟨orientInput.nr 10, orientInput.nr 11, orientInput.nr 12, orientInput.nr 13⟩ : MatchingCycleChild) = left := by
    simpa [orientFixed 10, orientFixed 11, orientFixed 12, orientFixed 13, keep 10, keep 11, keep 12, keep 13,
      beforeAdvance, rebasePairLeftSaved, aInput, relocateState, readMatchingCycleChildValue] using leftRead
  refine ⟨t, _, by omega, joined, live, ?_, ?_, ?_, ?_, eNat.trans (dNat.trans aNat),
    eReal.trans (dReal.trans aReal), eRR.trans (dRR.trans aRR), ?_⟩
  · change e.nr 7 = next
    rw [eGet 7 (by decide), orientFixed 7]
    simp [readInput, advanced, relocateState]
  · change (e.nr 10, e.nr 11) = _
    rw [eGet 10 (by decide), eGet 11 (by decide)]
    exact Prod.ext (congrArg MatchingCycleChild.representative leftBytes) (congrArg MatchingCycleChild.node leftBytes)
  · change (e.nr 15, e.nr 25) = _
    rw [eGet 15 (by decide), eGet 25 (by decide)]
    exact Prod.ext (congrArg MatchingCycleChild.representative rightRead') (congrArg MatchingCycleChild.node rightRead')
  · change (e.nr 12, e.nr 13) = _
    have mapBase : orientInput.nr 79 = s.nr 79 :=
      (orientFixed 79).trans ((keep 79).trans ((carry 79).trans (aGet 79 (by decide))))
    simpa only [leftBytes, mapBase, show orientInput.nm = s.nm from dNat.trans aNat] using ports
  · intro r safe
    rw [← joined.run]
    exact arithmeticRun_keeps_from_destination_list _ (by decide) safe s _


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebasePair

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

/-! matching/MatchingPairBucketMemory.lean -/
section RppSource_MatchingPairBucketMemory
namespace VehicleRoutingSurvey.Routing







/-- Two executions that stay inside the same block up to its exit have the same result. -/
theorem BlockRuns.same_exit {code : List ArithmeticInstruction} {s t u : ArithmeticState} {m n : ℕ}
    (left : BlockRuns code m s t) (right : BlockRuns code n s u) : m = n ∧ t = u := by
  have lower : m ≤ n := by
    by_contra! earlier
    have contradict := left.inside n earlier
    rw [right.run, right.exit] at contradict
    exact (lt_irrefl _ contradict).elim
  have upper : n ≤ m := by
    by_contra! earlier
    have contradict := right.inside m earlier
    rw [left.run, left.exit] at contradict
    exact (lt_irrefl _ contradict).elim
  have same := Nat.le_antisymm lower upper
  exact ⟨same, left.run.symm.trans (same.symm ▸ right.run)⟩






end VehicleRoutingSurvey.Routing
end RppSource_MatchingPairBucketMemory

/-! matching/MatchingRegistryUnique.lean -/
section RppSource_MatchingRegistryUnique
namespace VehicleRoutingSurvey.Routing

namespace MatchingMemberTree

private theorem children_rootKeys_eq {memory : ℕ → ℕ} {startBase countBase node : ℕ}
    {a b : MatchingMemberTree} {r q : ℕ} {tail rest : MatchingMemberTree}
    (left : (blossom r node a tail).encoded memory startBase countBase)
    (right : (blossom q node b rest).encoded memory startBase countBase) : a.rootKeys = b.rootKeys := by
  have count : a.rootKeys.length = b.rootKeys.length := by
    rw [rootKeys_length, rootKeys_length, ← left.1, ← right.1]
  apply List.ext_getElem count
  intro i ha hb
  exact (left.2.1 i ha).symm.trans (right.2.1 i hb)

/-- An encoded list of root keys determines the live registry tree. Nonzero
IDs identify blossoms and the physical headers fix the full child list. -/
theorem eq_of_encoded_rootKeys {memory : ℕ → ℕ} {startBase countBase : ℕ}
    {a b : MatchingMemberTree} (leftProper : a.proper) (rightProper : b.proper)
    (left : a.encoded memory startBase countBase) (right : b.encoded memory startBase countBase)
    (keys : a.rootKeys = b.rootKeys) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b <;> simp_all [rootKeys]
  | leaf v tail ih =>
    cases b with
    | nil => simp [rootKeys] at keys
    | leaf w rest =>
      obtain ⟨same, remaining⟩ := List.cons.inj keys
      have sameVertex := congrArg Prod.fst same
      change v = w at sameVertex
      subst w
      rw [ih (b := rest) leftProper rightProper left right remaining]
    | blossom w node children rest =>
      have same := congrArg Prod.snd (List.cons.inj keys).1
      exact (Nat.ne_of_gt rightProper.1 same.symm).elim
  | blossom v node children tail ihChildren ihTail =>
    cases b with
    | nil => simp [rootKeys] at keys
    | leaf w rest =>
      have same := congrArg Prod.snd (List.cons.inj keys).1
      exact (Nat.ne_of_gt leftProper.1 same).elim
    | blossom w id other rest =>
      obtain ⟨same, remaining⟩ := List.cons.inj keys
      have sameVertex := congrArg Prod.fst same
      have sameNode := congrArg Prod.snd same
      change v = w at sameVertex
      change node = id at sameNode
      subst w
      subst id
      have childKeys := children_rootKeys_eq left right
      have childTree := ihChildren (b := other) leftProper.2.2.1 rightProper.2.2.1 left.2.2.1 right.2.2.1 childKeys
      have siblingTree := ihTail (b := rest) leftProper.2.2.2 rightProper.2.2.2 left.2.2.2 right.2.2.2 remaining
      rw [childTree, siblingTree]



end MatchingMemberTree






end VehicleRoutingSurvey.Routing
end RppSource_MatchingRegistryUnique

/-! matching/MatchingRebaseStack.lean -/
section RppSource_MatchingRebaseStack
namespace VehicleRoutingSurvey.Routing









theorem resetMatchingRebaseJobsBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns resetMatchingRebaseJobsBlock 4 s t ∧ t.halted = false ∧
      t.nr 81 = s.nr 80 + 3 * s.nr 55 ∧ t.nr 82 = 0 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 81, 82] → t.nr r = s.nr r := by
  let t := (arithmeticStep resetMatchingRebaseJobsBlock)^[4] s
  have triple : s.nr 55 + s.nr 55 + s.nr 55 = 3 * s.nr 55 := by omega
  have effect : t.pc = resetMatchingRebaseJobsBlock.length ∧ t.halted = false ∧
      t.nr 81 = s.nr 80 + 3 * s.nr 55 ∧ t.nr 82 = 0 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, resetMatchingRebaseJobsBlock, arithmeticStep, entry, running, Function.iterate_succ_apply', triple]
  obtain ⟨exit, live, base, count, natural, real, realRegisters⟩ := effect
  exact ⟨t, BlockRuns.of_running_exit rfl live exit, live, base, count, natural, real, realRegisters,
    fun _ safe => arithmeticRun_keeps_from_destination_list _ (by decide) safe s 4⟩



theorem popMatchingRebaseJobBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) :
    let i := s.nr 82 - 1
    ∃ t, BlockRuns popMatchingRebaseJobBlock 6 s t ∧ t.halted = false ∧
      t.nr 82 = i ∧ t.nr 22 = s.nm (matchingRebaseJobAddress s i) ∧
      t.nr 29 = s.nm (matchingRebaseJobAddress s i + 1) ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 22, 29, 82] → t.nr r = s.nr r := by
  intro i
  let t := (arithmeticStep popMatchingRebaseJobBlock)^[6] s
  have effect : t.pc = popMatchingRebaseJobBlock.length ∧ t.halted = false ∧
      t.nr 82 = i ∧ t.nr 22 = s.nm (matchingRebaseJobAddress s i) ∧
      t.nr 29 = s.nm (matchingRebaseJobAddress s i + 1) ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, popMatchingRebaseJobBlock, arithmeticStep, entry, running, one,
      Function.iterate_succ_apply', matchingRebaseJobAddress, i, Nat.two_mul]
  obtain ⟨exit, live, count, node, desired, natural, real, realRegisters⟩ := effect
  exact ⟨t, BlockRuns.of_running_exit rfl live exit, live, count, node, desired, natural, real, realRegisters,
    fun _ safe => arithmeticRun_keeps_from_destination_list _ (by decide) safe s 6⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseStack

/-! matching/MatchingRebaseWrite.lean -/
section RppSource_MatchingRebaseWrite
open private pushMatchingRebaseJob VehicleRoutingSurvey.Routing.pushMatchingRebaseJob from Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing



def installedRebasedCyclePairMemory (s : ArithmeticState) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update
    s.nm (s.nr 50 + s.nr 12) (s.nr 13)) (s.nr 50 + s.nr 13) (s.nr 12))
    (s.nr 18 + 4 * s.nr 28) (s.nr 12)) (s.nr 18 + 4 * s.nr 7) (s.nr 13)

theorem installRebasedCyclePairBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns installRebasedCyclePairBlock 12 s t ∧ t.halted = false ∧
      t.nm = installedRebasedCyclePairMemory s ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6] → t.nr r = s.nr r := by
  let t := (arithmeticStep installRebasedCyclePairBlock)^[12] s
  have effect : t.pc = installRebasedCyclePairBlock.length ∧ t.halted = false ∧
      t.nm = installedRebasedCyclePairMemory s ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    have quad (n : ℕ) : n + n + (n + n) = 4 * n := by omega
    simp [t, installRebasedCyclePairBlock, arithmeticStep, entry, running, Function.iterate_succ_apply',
      installedRebasedCyclePairMemory, quad]
  obtain ⟨exit, live, natural, real, rr⟩ := effect
  exact ⟨t, BlockRuns.of_running_exit rfl live exit, live, natural, real, rr,
    fun _ safe => arithmeticRun_keeps_from_destination_list _ (by decide) safe s 12⟩





private theorem pushMatchingRebaseJob_correct (node port : ℕ) {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (nodeReg : node ≠ 6) (portReg : port ≠ 6) :
    ∃ t, BlockRuns (pushMatchingRebaseJob node port) 6 s t ∧ t.halted = false ∧
      t.nr 82 = s.nr 82 + 1 ∧ t.nm = pushedMatchingRebaseJob s (s.nr node) (s.nr port) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 82] → t.nr r = s.nr r := by
  let t := (arithmeticStep (pushMatchingRebaseJob node port))^[6] s
  have effect : t.pc = (pushMatchingRebaseJob node port).length ∧ t.halted = false ∧
      t.nr 82 = s.nr 82 + 1 ∧ t.nm = pushedMatchingRebaseJob s (s.nr node) (s.nr port) ∧
      t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, pushMatchingRebaseJob, arithmeticStep, entry, running, one, Function.iterate_succ_apply',
      pushedMatchingRebaseJob, matchingRebaseJobAddress, nodeReg, portReg, Nat.two_mul]
  obtain ⟨exit, live, size, natural, real, rr⟩ := effect
  refine ⟨t, BlockRuns.of_running_exit rfl live exit, live, size, natural, real, rr, ?_⟩
  intro r safe
  have destinations : (pushMatchingRebaseJob node port).all (fun ins => decide (naturalDestination ins ∈ [0, 6, 82])) = true := by
    simp [pushMatchingRebaseJob, naturalDestination]
  exact arithmeticRun_keeps_from_destination_list _ destinations safe s 6



theorem queueMatchingRebaseChildBlock_correct (node port : ℕ) {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (nodeReg : node ≠ 6) (portReg : port ≠ 6) :
    ∃ t steps, steps ≤ 7 ∧ BlockRuns (queueMatchingRebaseChildBlock node port) steps s t ∧
      t.halted = false ∧ t.nr 82 = s.nr 82 + (if s.nr node = 0 then 0 else 1) ∧
      t.nm = (if s.nr node = 0 then s.nm else pushedMatchingRebaseJob s (s.nr node) (s.nr port)) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 82] → t.nr r = s.nr r := by
  by_cases singleton : s.nr node = 0
  · have empty : BlockRuns [] 0 s s := ⟨fun i h => (Nat.not_lt_zero i h).elim, by simp, entry⟩
    have skips := branchOnAtMost_left node 14 [] (pushMatchingRebaseJob node port) entry running
      (by rw [singleton, zero]) empty running
    exact ⟨_, 2, by decide, skips, running, by simp [singleton], by simp [singleton], rfl, rfl, fun _ _ => rfl⟩
  · obtain ⟨t, push, live, size, natural, real, rr, regs⟩ :=
      pushMatchingRebaseJob_correct node port entry running one nodeReg portReg
    have takes := branchOnAtMost_right node 14 [] (pushMatchingRebaseJob node port) entry running
      (by rw [zero]; exact Nat.pos_of_ne_zero singleton) push live
    exact ⟨_, 7, le_rfl, takes, live, by simpa [singleton] using size,
      by simpa [singleton] using natural, real, rr, regs⟩





def rebasedCyclePairState (s : ArithmeticState) : ArithmeticState :=
  let rightIndex := (s.nr 7 + 1) % s.nr 19
  let left := matchingCycleChildAt s.nm (s.nr 18 + 4 * s.nr 7)
  let right := matchingCycleChildAt s.nm (s.nr 18 + 4 * rightIndex)
  let (a, b) := matchingRebasePorts s.nm (s.nr 79) left
  let positions := Function.update (Function.update s.nr 28 (s.nr 7)) 7 rightIndex
  let edge := {s with nr := Function.update (Function.update positions 12 a) 13 b}
  let installed := {edge with nm := installedRebasedCyclePairMemory edge}
  queuedMatchingRebaseJob (queuedMatchingRebaseJob installed left.node a) right.node b

set_option maxRecDepth 4096 in
theorem rebaseMatchingCyclePairBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (inside : s.nr 7 < s.nr 19) :
    ∃ t steps, steps ≤ 61 ∧ BlockRuns rebaseMatchingCyclePairBlock steps s t ∧ t.halted = false ∧
      t.nr 7 = (s.nr 7 + 1) % s.nr 19 ∧ t.nr 82 = (rebasedCyclePairState s).nr 82 ∧
      t.nm = (rebasedCyclePairState s).nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 7, 10, 11, 12, 13, 15, 16, 17, 25, 28, 82] → t.nr r = s.nr r := by
  let next := (s.nr 7 + 1) % s.nr 19
  let left := matchingCycleChildAt s.nm (s.nr 18 + 4 * s.nr 7)
  let right := matchingCycleChildAt s.nm (s.nr 18 + 4 * next)
  let ports := matchingRebasePorts s.nm (s.nr 79) left
  let saved := {s with pc := 1, nr := Function.update s.nr 28 (s.nr 7)}
  have save : BlockRuns [.natAdd 28 7 14] 1 s saved := by
    apply BlockRuns.of_running_exit
    · simp [saved, arithmeticStep, entry, running, zero]
    · exact running
    · rfl
  let a := {saved with pc := 0}
  have aAt (r : ℕ) (h : r ≠ 28 := by decide) : a.nr r = s.nr r := by simp [a, saved, h]
  obtain ⟨b, readSteps, readCost, read, bLive, bNext, bLeft, bRight, bPorts, bNat, bReal, bRR, bRegs⟩ :=
    readRebasedCyclePairBlock_correct (s := a) rfl running ((aAt 9).trans one) ((aAt 14).trans zero)
      (by rwa [aAt 7, aAt 19])
  have bAt (r : ℕ) (h : r ∉ [0, 6, 7, 10, 11, 12, 13, 15, 16, 17, 25] := by decide)
      (j : r ≠ 28 := by decide) : b.nr r = s.nr r := (bRegs r h).trans (aAt r j)
  have bNext' : b.nr 7 = next := by simpa only [aAt 7, aAt 19, next] using bNext
  have bLeftId : b.nr 11 = left.node := by
    simpa only [left, aAt 18, aAt 7] using congrArg Prod.snd bLeft
  have bRightId : b.nr 25 = right.node := by
    simpa only [right, next, aAt 18, aAt 7, aAt 19] using congrArg Prod.snd bRight
  have bPort : (b.nr 12, b.nr 13) = ports := by
    simpa only [ports, left, aAt 18, aAt 7, aAt 79] using bPorts
  have bIndex : b.nr 28 = s.nr 7 := by
    rw [bRegs 28 (by decide)]
    simp [a, saved]
  let ab := appendBlock [.natAdd 28 7 14] readRebasedCyclePairBlock
  let cInput := {relocateState 1 b with pc := 0}
  obtain ⟨c, install, cLive, cNat, cReal, cRR, cRegs⟩ :=
    installRebasedCyclePairBlock_correct (s := cInput) rfl bLive
  have cAt (r : ℕ) (h : r ∉ [0, 6] := by decide) : c.nr r = b.nr r := cRegs r h
  let abc := appendBlock ab installRebasedCyclePairBlock
  let dInput := {relocateState ab.length c with pc := 0}
  obtain ⟨d, dSteps, dCost, first, dLive, dCount, dNat, dReal, dRR, dRegs⟩ :=
    queueMatchingRebaseChildBlock_correct 11 12 (s := dInput) rfl cLive
      (((cAt 9).trans (bAt 9)).trans one) (((cAt 14).trans (bAt 14)).trans zero) (by decide) (by decide)
  have dAt (r : ℕ) (h : r ∉ [0, 6, 82] := by decide) (j : r ∉ [0, 6] := by decide) :
      d.nr r = b.nr r := (dRegs r h).trans (cAt r j)
  let abcd := appendBlock abc (queueMatchingRebaseChildBlock 11 12)
  let eInput := {relocateState abc.length d with pc := 0}
  obtain ⟨e, eSteps, eCost, second, live, eCount, eNat, eReal, eRR, eRegs⟩ :=
    queueMatchingRebaseChildBlock_correct 25 13 (s := eInput) rfl dLive
      (((dAt 9).trans (bAt 9)).trans one) (((dAt 14).trans (bAt 14)).trans zero) (by decide) (by decide)
  let t := relocateState abcd.length e
  have composite : BlockRuns rebaseMatchingCyclePairBlock (1 + readSteps + 12 + dSteps + eSteps) s t :=
    (((save.append read).append install).append first).append second
  let positions := Function.update (Function.update s.nr 28 (s.nr 7)) 7 next
  let edge := {s with nr := Function.update (Function.update positions 12 ports.1) 13 ports.2}
  let installed := {edge with nm := installedRebasedCyclePairMemory edge}
  let leftJob := queuedMatchingRebaseJob installed left.node ports.1
  have model : rebasedCyclePairState s = queuedMatchingRebaseJob leftJob right.node ports.2 := by
    simp only [rebasedCyclePairState, next, left, right, edge, positions, installed, leftJob, ports, Prod.eta]
  have installedNat : c.nm = installed.nm := by
    change c.nm = installedRebasedCyclePairMemory edge
    rw [cNat]
    have bytes : cInput.nm = s.nm := bNat
    have get (r : ℕ) (h : r ∉ [0, 6, 7, 10, 11, 12, 13, 15, 16, 17, 25] := by decide)
        (j : r ≠ 28 := by decide) : cInput.nr r = s.nr r := bAt r h j
    have aPort := congrArg Prod.fst bPort
    have bPort' := congrArg Prod.snd bPort
    have i : cInput.nr 28 = s.nr 7 := bIndex
    have j : cInput.nr 7 = next := bNext'
    have ea : cInput.nr 12 = ports.1 := aPort
    have eb : cInput.nr 13 = ports.2 := bPort'
    simp [installedRebasedCyclePairMemory, bytes, get 50, get 18, i, j, ea, eb, edge, positions]
  have cCount : c.nr 82 = s.nr 82 := (cAt 82).trans (bAt 82)
  have dCount' : d.nr 82 = leftJob.nr 82 := by
    have id : dInput.nr 11 = left.node := (cAt 11).trans bLeftId
    change d.nr 82 = _
    rw [dCount, id, show dInput.nr 82 = s.nr 82 from cCount]
    by_cases leaf : left.node = 0 <;> simp [leftJob, queuedMatchingRebaseJob, leaf, installed, edge, positions]
  have dNat' : d.nm = leftJob.nm := by
    have id : dInput.nr 11 = left.node := (cAt 11).trans bLeftId
    have port : dInput.nr 12 = ports.1 := (cAt 12).trans (congrArg Prod.fst bPort)
    have base : dInput.nr 81 = s.nr 81 := (cAt 81).trans (bAt 81)
    rw [dNat, id, port]
    have bytes : dInput.nm = installed.nm := installedNat
    by_cases leaf : left.node = 0 <;> simp [leftJob, queuedMatchingRebaseJob, leaf,
      pushedMatchingRebaseJob, matchingRebaseJobAddress, base, show dInput.nr 82 = s.nr 82 from cCount,
      bytes, installed, edge, positions]
  have eId : eInput.nr 25 = right.node := (dAt 25).trans bRightId
  refine ⟨t, _, by omega, composite, live, ?_, ?_, ?_,
    eReal.trans (dReal.trans (cReal.trans bReal)), eRR.trans (dRR.trans (cRR.trans bRR)), ?_⟩
  · exact (eRegs 7 (by decide)).trans ((dAt 7).trans bNext')
  · change e.nr 82 = _
    rw [eCount, eId, show eInput.nr 82 = leftJob.nr 82 from dCount', model]
    by_cases leaf : right.node = 0 <;> simp [queuedMatchingRebaseJob, leaf]
  · change e.nm = _
    have port : eInput.nr 13 = ports.2 := (dAt 13).trans (congrArg Prod.snd bPort)
    have base : eInput.nr 81 = leftJob.nr 81 := by
      have atBase : eInput.nr 81 = s.nr 81 := (dAt 81).trans (bAt 81)
      rw [atBase]
      by_cases leaf : left.node = 0 <;> simp [leftJob, queuedMatchingRebaseJob, leaf, installed, edge, positions]
    rw [eNat, model, eId, port]
    by_cases leaf : right.node = 0 <;> simp [queuedMatchingRebaseJob, leaf, pushedMatchingRebaseJob,
      matchingRebaseJobAddress, base, show eInput.nr 82 = leftJob.nr 82 from dCount',
      show eInput.nm = leftJob.nm from dNat']
  · intro r safe
    rw [← composite.run]
    exact arithmeticRun_keeps_from_destination_list _ (by decide) safe s _


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseWrite

/-! matching/MatchingRebaseNode.lean -/
section RppSource_MatchingRebaseNode
namespace VehicleRoutingSurvey.Routing











theorem writeMatchingRebaseFreeChildBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (zero : s.nr 14 = 0) :
    ∃ t, BlockRuns writeMatchingRebaseFreeChildBlock 5 s t ∧ t.halted = false ∧
      t.nr 7 = s.nr 46 ∧ t.nm = Function.update s.nm (s.nr 18 + 4 * s.nr 46) (s.nr 29) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 7] → t.nr r = s.nr r := by
  let t := (arithmeticStep writeMatchingRebaseFreeChildBlock)^[5] s
  have quad : s.nr 46 + s.nr 46 + (s.nr 46 + s.nr 46) = 4 * s.nr 46 := by omega
  have effect : t.pc = writeMatchingRebaseFreeChildBlock.length ∧ t.halted = false ∧
      t.nr 7 = s.nr 46 ∧ t.nm = Function.update s.nm (s.nr 18 + 4 * s.nr 46) (s.nr 29) ∧
      t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, writeMatchingRebaseFreeChildBlock, arithmeticStep, entry, running, zero,
      Function.iterate_succ_apply', quad]
  obtain ⟨exit, live, freeIndex, natural, real, realRegisters⟩ := effect
  exact ⟨t, BlockRuns.of_running_exit rfl live exit, live, freeIndex, natural, real, realRegisters,
    fun _ safe => arithmeticRun_keeps_from_destination_list _ (by decide) safe s 5⟩


















end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseNode

/-! matching/MatchingAugmentApply.lean -/
section RppSource_MatchingAugmentApply
open private moveMatchingAugmentationRepresentative VehicleRoutingSurvey.Routing.moveMatchingAugmentationRepresentative from Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
namespace VehicleRoutingSurvey.Routing









theorem recordAugmentationRepresentativeBlock_correct (port : ℕ) {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (portReg : port ∉ [6, 22, 26]) (separate : s.nr 74 + s.nm (s.nr 57 + s.nr port) ≠
      s.nr 89 + s.nm (s.nr 57 + s.nr port)) :
    let endpoint := s.nr port
    let after := queuedMatchingRebaseJob (augmentationRepresentativeUpdate s endpoint)
      (s.nm (s.nr 74 + s.nm (s.nr 57 + endpoint))) endpoint
    ∃ t steps, steps ≤ 16 ∧ BlockRuns (recordAugmentationRepresentativeBlock port) steps s t ∧
      t.halted = false ∧ t.nr 82 = after.nr 82 ∧ t.nm = after.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 22, 26, 82] → t.nr r = s.nr r := by
  intro endpoint after
  have h6 : port ≠ 6 := fun eq => portReg (by simp [eq])
  have h22 : port ≠ 22 := fun eq => portReg (by simp [eq])
  have h26 : port ≠ 26 := fun eq => portReg (by simp [eq])
  let old := s.nm (s.nr 57 + endpoint)
  let node := s.nm (s.nr 74 + old)
  let a := (arithmeticStep (moveMatchingAugmentationRepresentative port))^[9] s
  have effect : a.pc = (moveMatchingAugmentationRepresentative port).length ∧ a.halted = false ∧
      a.nr 22 = node ∧ a.nm = (augmentationRepresentativeUpdate s endpoint).nm ∧
      a.rm = s.rm ∧ a.rr = s.rr := by
    simp [a, moveMatchingAugmentationRepresentative, arithmeticStep, entry, running, h6, h22, h26,
      zero, Function.iterate_succ_apply', augmentationRepresentativeUpdate, endpoint, old, node,
      Function.update_of_ne separate]
  obtain ⟨exit, live, aNode, aNat, aReal, aRR⟩ := effect
  have move : BlockRuns (moveMatchingAugmentationRepresentative port) 9 s a :=
    BlockRuns.of_running_exit rfl live exit
  have aKeep (r : ℕ) (safe : r ∉ [0, 6, 22, 26] := by decide) : a.nr r = s.nr r := by
    apply arithmeticRun_keeps_from_destination_list [0, 6, 22, 26] _ safe
    simp [moveMatchingAugmentationRepresentative, naturalDestination]
  have aPort : a.nr port = endpoint := by
    simp [a, moveMatchingAugmentationRepresentative, arithmeticStep, entry, running, h6, h22, h26,
      Function.iterate_succ_apply', endpoint]
  let bInput := {a with pc := 0}
  obtain ⟨b, ticks, bound, push, bLive, bCount, bNat, bReal, bRR, bKeep⟩ :=
    queueMatchingRebaseChildBlock_correct 22 port (s := bInput) rfl live ((aKeep 9).trans one)
      ((aKeep 14).trans zero) (by decide) h6
  refine ⟨_, 9 + ticks, by omega, move.append push, bLive, ?_, ?_, bReal.trans aReal, bRR.trans aRR, ?_⟩
  · change b.nr 82 = after.nr 82
    rw [bCount, show bInput.nr 22 = node from aNode, show bInput.nr 82 = s.nr 82 from aKeep 82]
    by_cases singleton : node = 0 <;>
      simp [after, queuedMatchingRebaseJob, augmentationRepresentativeUpdate, node, old, singleton]
  · change b.nm = after.nm
    rw [bNat, show bInput.nr 22 = node from aNode, show bInput.nr port = endpoint from aPort]
    by_cases singleton : node = 0 <;>
      simp [after, queuedMatchingRebaseJob, augmentationRepresentativeUpdate, node, old, singleton,
        pushedMatchingRebaseJob, matchingRebaseJobAddress, show bInput.nr 81 = s.nr 81 from aKeep 81,
        show bInput.nr 82 = s.nr 82 from aKeep 82, show bInput.nm = _ from aNat]
  · intro r safe
    change b.nr r = s.nr r
    have aSafe : r ∉ [0, 6, 22, 26] := by simp at safe ⊢; omega
    have bSafe : r ∉ [0, 6, 82] := by simp at safe ⊢; omega
    exact (bKeep r bSafe).trans (aKeep r aSafe)







theorem remapAugmentationOriginalBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    let address := s.nr 57 + s.nr 44
    ∃ t, BlockRuns remapAugmentationOriginalBlock 5 s t ∧ t.halted = false ∧
      t.nm = Function.update s.nm address (s.nm (s.nr 89 + s.nm address)) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ∉ [0, 6, 15, 26] → t.nr r = s.nr r := by
  intro address
  let t := (arithmeticStep remapAugmentationOriginalBlock)^[5] s
  have effect : t.pc = remapAugmentationOriginalBlock.length ∧ t.halted = false ∧
      t.nm = Function.update s.nm address (s.nm (s.nr 89 + s.nm address)) ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, remapAugmentationOriginalBlock, arithmeticStep, entry, running, Function.iterate_succ_apply', address]
  obtain ⟨exit, live, natural, real, realRegisters⟩ := effect
  exact ⟨t, BlockRuns.of_running_exit rfl live exit, live, natural, real, realRegisters,
    fun _ safe => arithmeticRun_keeps_from_destination_list _ (by decide) safe s 5⟩




end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentApply

/-! matching/MatchingAugmentInstallCell.lean -/
section RppSource_MatchingAugmentInstallCell
namespace VehicleRoutingSurvey.Routing

def augmentationCrossingAt (s : ArithmeticState) (i : ℕ) : ℕ × ℕ :=
  (s.nm (s.nr 86 + (i + i)), s.nm (s.nr 86 + (i + i) + 1))





theorem loadInstallAugmentationCrossingBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) :
    let ports := augmentationCrossingAt s (s.nr 44)
    ∃ t, BlockRuns loadInstallAugmentationCrossingBlock 9 s t ∧ t.halted = false ∧
      (t.nr 12, t.nr 13) = ports ∧ t.nm = installedAugmentationMateMemory s ports ∧
      (∀ r, r ∉ [0, 6, 12, 13] → t.nr r = s.nr r) ∧ t.rr = s.rr ∧ t.rm = s.rm := by
  intro ports
  let t := (arithmeticStep loadInstallAugmentationCrossingBlock)^[9] s
  have ready : t.halted = false := by
    simp [t, loadInstallAugmentationCrossingBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  have exit : t.pc = loadInstallAugmentationCrossingBlock.length := by
    simp [t, loadInstallAugmentationCrossingBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_, ?_⟩
  · simp [t, ports, augmentationCrossingAt, loadInstallAugmentationCrossingBlock, arithmeticStep,
      Function.iterate_succ_apply', entry, running, one]
  · simp [t, ports, augmentationCrossingAt, installedAugmentationMateMemory, loadInstallAugmentationCrossingBlock,
      arithmeticStep, Function.iterate_succ_apply', entry, running, one]
  · intro r away
    exact arithmeticRun_keeps_from_destination_list _ (by decide) away s 9
  · simp [t, loadInstallAugmentationCrossingBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  · simp [t, loadInstallAugmentationCrossingBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]





structure AugmentationInstallView (s t : ArithmeticState) : Prop where
  memory : s.nm = t.nm
  registers : ∀ r ∈ [50, 57, 74, 81, 82, 89], s.nr r = t.nr r

theorem AugmentationInstallView.stack {s t : ArithmeticState} (same : AugmentationInstallView s t) :
    s.nr 82 = t.nr 82 := same.registers 82 (by decide)

theorem AugmentationInstallView.trans {a b c : ArithmeticState}
    (left : AugmentationInstallView a b) (right : AugmentationInstallView b c) :
    AugmentationInstallView a c :=
  ⟨left.memory.trans right.memory, fun r h => (left.registers r h).trans (right.registers r h)⟩

private theorem queuedMatchingRebaseJob_view {s t : ArithmeticState} (same : AugmentationInstallView s t)
    (node port : ℕ) :
    AugmentationInstallView (queuedMatchingRebaseJob s node port) (queuedMatchingRebaseJob t node port) := by
  by_cases empty : node = 0
  · simpa [queuedMatchingRebaseJob, empty] using same
  · constructor
    · simp [queuedMatchingRebaseJob, empty, pushedMatchingRebaseJob, matchingRebaseJobAddress,
        same.memory, same.registers 81 (by decide), same.stack]
    · intro r inLayout
      by_cases count : r = 82
      · subst r
        simp [queuedMatchingRebaseJob, empty, same.stack]
      · simpa [queuedMatchingRebaseJob, empty, Function.update_of_ne count] using same.registers r inLayout

theorem AugmentationInstallView.rebaseEndpoint {s t : ArithmeticState} (same : AugmentationInstallView s t)
    (port : ℕ) : AugmentationInstallView (rebaseAugmentationEndpoint s port) (rebaseAugmentationEndpoint t port) := by
  have repBase := same.registers 57 (by decide)
  have nodeBase := same.registers 74 (by decide)
  have workBase := same.registers 89 (by decide)
  have updated : AugmentationInstallView (augmentationRepresentativeUpdate s port)
      (augmentationRepresentativeUpdate t port) := by
    refine ⟨?_, fun r hr => same.registers r hr⟩
    simp [augmentationRepresentativeUpdate, same.memory, repBase, nodeBase, workBase]
  have node : s.nm (s.nr 74 + s.nm (s.nr 57 + port)) = t.nm (t.nr 74 + t.nm (t.nr 57 + port)) := by
    rw [same.memory, repBase, nodeBase]
  unfold rebaseAugmentationEndpoint
  dsimp only
  rw [node]
  exact queuedMatchingRebaseJob_view updated _ _

theorem AugmentationInstallView.installCrossing {s t : ArithmeticState} (same : AugmentationInstallView s t)
    (ports : ℕ × ℕ) : AugmentationInstallView (installAugmentationCrossingState s ports)
      (installAugmentationCrossingState t ports) := by
  apply AugmentationInstallView.rebaseEndpoint
  apply AugmentationInstallView.rebaseEndpoint
  refine ⟨?_, fun r hr => same.registers r hr⟩
  simp [installedAugmentationMateMemory, same.memory, same.registers 50 (by decide)]

theorem rebaseAugmentationEndpoint_keeps {s : ArithmeticState} (port r : ℕ) (away : r ≠ 82) :
    (rebaseAugmentationEndpoint s port).nr r = s.nr r := by
  simp only [rebaseAugmentationEndpoint, queuedMatchingRebaseJob]
  split <;> simp [augmentationRepresentativeUpdate, Function.update_of_ne away]

theorem installAugmentationCrossingBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (buffers : s.nr 74 ≠ s.nr 89) :
    let expected := installAugmentationCrossingState s (augmentationCrossingAt s (s.nr 44))
    ∃ (t : ArithmeticState) (steps : ℕ), BlockRuns installAugmentationCrossingBlock steps s t ∧
      t.halted = false ∧ steps ≤ 41 ∧ AugmentationInstallView t expected ∧
      (∀ r, r ∉ [0, 6, 12, 13, 22, 26, 82] → t.nr r = s.nr r) ∧ t.rr = s.rr ∧ t.rm = s.rm := by
  intro expected
  let ports := augmentationCrossingAt s (s.nr 44)
  let afterMates := {s with nm := installedAugmentationMateMemory s ports}
  obtain ⟨a, mates, aReady, loaded, aMem, aRegs, aRR, aRM⟩ :=
    loadInstallAugmentationCrossingBlock_correct entry running one
  let leftEntry := {a with pc := 0}
  have leftPort : leftEntry.nr 12 = ports.1 := congrArg Prod.fst loaded
  have rightPort : leftEntry.nr 13 = ports.2 := congrArg Prod.snd loaded
  have aView : AugmentationInstallView leftEntry afterMates := by
    refine ⟨aMem, fun r h => aRegs r ?_⟩
    simp at h ⊢
    omega
  have separateA : leftEntry.nr 74 ≠ leftEntry.nr 89 := by
    change a.nr 74 ≠ a.nr 89
    rwa [aRegs 74 (by decide), aRegs 89 (by decide)]
  obtain ⟨b, leftSteps, leftBudget, left, bReady, bJobs, bMem, bRM, bRR, bRegs⟩ :=
    recordAugmentationRepresentativeBlock_correct 12 (s := leftEntry) rfl aReady
      ((aRegs 9 (by decide)).trans one) ((aRegs 14 (by decide)).trans zero) (by decide)
      (by omega)
  let leftModel := rebaseAugmentationEndpoint leftEntry ports.1
  have leftMem : b.nm = leftModel.nm := by
    change b.nm = (rebaseAugmentationEndpoint leftEntry ports.1).nm
    rw [← leftPort]
    exact bMem
  have leftJobs : b.nr 82 = leftModel.nr 82 := by
    change b.nr 82 = (rebaseAugmentationEndpoint leftEntry ports.1).nr 82
    rw [← leftPort]
    exact bJobs
  let rightEntry := {b with pc := 0}
  have bView : AugmentationInstallView rightEntry leftModel := by
    refine ⟨leftMem, ?_⟩
    intro r inLayout
    by_cases count : r = 82
    · subst r
      exact leftJobs
    · change b.nr r = (rebaseAugmentationEndpoint leftEntry ports.1).nr r
      rw [rebaseAugmentationEndpoint_keeps _ _ count]
      apply bRegs
      simp at inLayout ⊢
      omega
  have bPort : rightEntry.nr 13 = ports.2 := (bRegs 13 (by decide)).trans rightPort
  have separateB : rightEntry.nr 74 ≠ rightEntry.nr 89 := by
    change b.nr 74 ≠ b.nr 89
    rwa [bRegs 74 (by decide), bRegs 89 (by decide)]
  obtain ⟨c, rightSteps, rightBudget, right, cReady, cJobs, cMem, cRM, cRR, cRegs⟩ :=
    recordAugmentationRepresentativeBlock_correct 13 (s := rightEntry) rfl bReady
      ((bRegs 9 (by decide)).trans ((aRegs 9 (by decide)).trans one))
      ((bRegs 14 (by decide)).trans ((aRegs 14 (by decide)).trans zero)) (by decide)
      (by omega)
  have cView : AugmentationInstallView c (rebaseAugmentationEndpoint rightEntry ports.2) := by
    constructor
    · rw [← bPort]
      exact cMem
    · intro r inLayout
      by_cases count : r = 82
      · subst r
        rw [← bPort]
        exact cJobs
      · rw [rebaseAugmentationEndpoint_keeps _ _ count]
        apply cRegs
        simp at inLayout ⊢
        omega
  have all := mates.append (left.append right)
  refine ⟨_, _, all, cReady, by omega, ?_, ?_, cRR.trans (bRR.trans aRR), cRM.trans (bRM.trans aRM)⟩
  · have observed := cView.trans ((bView.trans (aView.rebaseEndpoint ports.1)).rebaseEndpoint ports.2)
    exact ⟨observed.memory, observed.registers⟩
  · intro r away
    have rb : r ∉ [0, 6, 22, 26, 82] := by simp at away ⊢; omega
    have ra : r ∉ [0, 6, 12, 13] := by simp at away ⊢; omega
    exact (cRegs r rb).trans ((bRegs r rb).trans (aRegs r ra))

end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentInstallCell

/-! matching/MatchingAugmentInstallMemory.lean -/
section RppSource_MatchingAugmentInstallMemory
namespace VehicleRoutingSurvey.Routing





theorem AugmentationInstallLayout.map_unwritten {k : ℕ} {s : ArithmeticState}
    (layout : AugmentationInstallLayout k s) {i : ℕ} (inside : i < k) :
    AugmentationInstallUnwritten k s (s.nr 57 + i) := by
  obtain ⟨mates, nodes, pairs, work, jobs⟩ := layout
  exact ⟨.inr (by omega), .inl (by omega), .inl (by omega), .inl (by omega)⟩

theorem AugmentationInstallLayout.crossing_unwritten {k : ℕ} {s : ArithmeticState}
    (layout : AugmentationInstallLayout k s) {i : ℕ} (inside : i < k) :
    AugmentationInstallUnwritten k s (s.nr 86 + i) := by
  obtain ⟨mates, nodes, pairs, work, jobs⟩ := layout
  exact ⟨.inr (by omega), .inr (by omega), .inl (by omega), .inl (by omega)⟩

theorem AugmentationInstallLayout.prefix_unwritten {k : ℕ} {s : ArithmeticState}
    (layout : AugmentationInstallLayout k s) {address : ℕ} (below : address < s.nr 50) :
    AugmentationInstallUnwritten k s address := by
  obtain ⟨mates, nodes, pairs, work, jobs⟩ := layout
  exact ⟨.inl below, .inl (by omega), .inl (by omega), .inl (by omega)⟩

theorem installedAugmentationMateMemory_keeps {k : ℕ} {s : ArithmeticState} {ports : ℕ × ℕ}
    (left : ports.1 < k) (right : ports.2 < k) {address : ℕ}
    (away : address < s.nr 50 ∨ s.nr 50 + k ≤ address) :
    installedAugmentationMateMemory s ports address = s.nm address := by
  have first : address ≠ s.nr 50 + ports.1 := by omega
  have second : address ≠ s.nr 50 + ports.2 := by omega
  simp [installedAugmentationMateMemory, Function.update_of_ne first, Function.update_of_ne second]

theorem rebaseAugmentationEndpoint_stack_le (s : ArithmeticState) (port : ℕ) :
    (rebaseAugmentationEndpoint s port).nr 82 ≤ s.nr 82 + 1 := by
  simp only [rebaseAugmentationEndpoint, queuedMatchingRebaseJob]
  split <;> simp [augmentationRepresentativeUpdate]

theorem rebaseAugmentationEndpoint_untouched {k : ℕ} {s : ArithmeticState} {port address : ℕ}
    (finite : port < k) (repBound : s.nm (s.nr 57 + port) < k) (stackRoom : s.nr 82 < k)
    (outside : AugmentationInstallUnwritten k s address) :
    (rebaseAugmentationEndpoint s port).nm address = s.nm address := by
  obtain ⟨_, notNode, notWork, notStack⟩ := outside
  let old := s.nm (s.nr 57 + port)
  have oldBound : old < k := repBound
  have oldNode : address ≠ s.nr 74 + old := by omega
  have newNode : address ≠ s.nr 74 + port := by omega
  have replacement : address ≠ s.nr 89 + old := by omega
  have job : address ≠ s.nr 81 + 2 * s.nr 82 := by omega
  have jobNext : address ≠ s.nr 81 + 2 * s.nr 82 + 1 := by omega
  simp only [rebaseAugmentationEndpoint, queuedMatchingRebaseJob]
  split <;> simp [augmentationRepresentativeUpdate, pushedMatchingRebaseJob, matchingRebaseJobAddress,
    Function.update_of_ne (show address ≠ s.nr 74 + s.nm (s.nr 57 + port) from oldNode),
    Function.update_of_ne newNode,
    Function.update_of_ne (show address ≠ s.nr 89 + s.nm (s.nr 57 + port) from replacement),
    Function.update_of_ne job, Function.update_of_ne jobNext]



theorem installAugmentationCrossingState_stack_le (s : ArithmeticState) (ports : ℕ × ℕ) :
    (installAugmentationCrossingState s ports).nr 82 ≤ s.nr 82 + 2 := by
  let m := {s with nm := installedAugmentationMateMemory s ports}
  have first := rebaseAugmentationEndpoint_stack_le m ports.1
  have second := rebaseAugmentationEndpoint_stack_le (rebaseAugmentationEndpoint m ports.1) ports.2
  change (rebaseAugmentationEndpoint (rebaseAugmentationEndpoint m ports.1) ports.2).nr 82 ≤ s.nr 82 + 2
  change (rebaseAugmentationEndpoint m ports.1).nr 82 ≤ s.nr 82 + 1 at first
  omega

theorem installAugmentationCrossingState_untouched {k : ℕ} {s : ArithmeticState} {ports : ℕ × ℕ}
    (left : ports.1 < k) (right : ports.2 < k) (layout : AugmentationInstallLayout k s)
    (repBound : ∀ v < k, s.nm (s.nr 57 + v) < k) (room : s.nr 82 + 2 ≤ k)
    {address : ℕ} (outside : AugmentationInstallUnwritten k s address) :
    (installAugmentationCrossingState s ports).nm address = s.nm address := by
  let m := {s with nm := installedAugmentationMateMemory s ports}
  let b := rebaseAugmentationEndpoint m ports.1
  have inMap (v : ℕ) (hv : v < k) : m.nm (s.nr 57 + v) = s.nm (s.nr 57 + v) :=
    installedAugmentationMateMemory_keeps left right (layout.map_unwritten hv).1
  have firstBound : m.nm (m.nr 57 + ports.1) < k := by
    change m.nm (s.nr 57 + ports.1) < k
    rw [inMap _ left]
    exact repBound _ left
  have firstRoom : m.nr 82 < k := by change s.nr 82 < k; omega
  have bMap := rebaseAugmentationEndpoint_untouched left firstBound firstRoom (layout.map_unwritten right)
  have bRep : b.nr 57 = s.nr 57 := rebaseAugmentationEndpoint_keeps ports.1 57 (by decide)
  have secondBound : b.nm (b.nr 57 + ports.2) < k := by
    rw [bRep]
    exact (bMap.trans (inMap _ right)).trans_lt (repBound _ right)
  have spent := rebaseAugmentationEndpoint_stack_le m ports.1
  have secondRoom : b.nr 82 < k := by
    change b.nr 82 ≤ s.nr 82 + 1 at spent
    omega
  have outsideB : AugmentationInstallUnwritten k b address := by
    simpa only [b, AugmentationInstallUnwritten, rebaseAugmentationEndpoint_keeps _ 50 (by decide),
      rebaseAugmentationEndpoint_keeps _ 74 (by decide), rebaseAugmentationEndpoint_keeps _ 89 (by decide),
      rebaseAugmentationEndpoint_keeps _ 81 (by decide)] using outside
  exact (rebaseAugmentationEndpoint_untouched right secondBound secondRoom outsideB).trans
    ((rebaseAugmentationEndpoint_untouched left firstBound firstRoom outside).trans
      (installedAugmentationMateMemory_keeps left right outside.1))

end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentInstallMemory

/-! matching/MatchingAugmentInstallRAM.lean -/
section RppSource_MatchingAugmentInstallRAM
namespace VehicleRoutingSurvey.Routing



private structure AugmentationCrossingInstallScan {k : ℕ} (s : ArithmeticState)
    (rows : List (Fin k × Fin k)) (i : ℕ) (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  running : m.halted = false
  index : m.nr 44 = i
  registers : ∀ r, r ∉ [0, 6, 12, 13, 22, 26, 44, 82] → m.nr r = s.nr r
  model : AugmentationInstallView m (installAugmentationCrossingRows s (rows.take i))
  untouched : ∀ address, AugmentationInstallUnwritten k s address → m.nm address = s.nm address
  jobs : m.nr 82 ≤ 2 * i
  realRegisters : m.rr = s.rr
  realMemory : m.rm = s.rm

/-- Install the ordered original crossing edges in the original mate table,
move top-level representatives, and queue the nontrivial blossom roots.
The input crossing array, original representative map, and natural prefix
below the mate table are retained. -/
theorem installAugmentationCrossingLoop_correct {k : ℕ} {s : ArithmeticState}
    (rows : List (Fin k × Fin k)) (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 9 = 1) (zero : s.nr 14 = 0) (emptyStack : s.nr 82 = 0)
    (count : s.nr 87 = rows.length) (array : AugmentationCrossingArray s.nm (s.nr 86) rows)
    (capacity : 2 * rows.length ≤ k) (layout : AugmentationInstallLayout k s)
    (originalMap : ∀ i < k, s.nm (s.nr 57 + i) < k) :
    ∃ (t : ArithmeticState) (steps : ℕ),
      BlockRuns (countedLoopFromZero 9 44 87 installAugmentationCrossingBlock) steps s t ∧
      t.halted = false ∧ steps ≤ 44 * rows.length + 2 ∧ t.nr 82 ≤ 2 * rows.length ∧
      AugmentationInstallView t (installAugmentationCrossingRows s rows) ∧
      (∀ address, AugmentationInstallUnwritten k s address → t.nm address = s.nm address) ∧
      (∀ r, r ∉ [0, 6, 12, 13, 22, 26, 44, 82] → t.nr r = s.nr r) ∧
      t.rr = s.rr ∧ t.rm = s.rm := by
  let inv := AugmentationCrossingInstallScan s rows
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 44 0} := by
    refine ⟨rfl, running, by simp, ?_, ⟨rfl, ?_⟩, fun _ _ => rfl, by simp [emptyStack], rfl, rfl⟩
    · intro r away
      have notIndex : r ≠ 44 := by intro h; exact away (by simp [h])
      simp [Function.update_of_ne notIndex]
    · intro r layoutSlot
      have notIndex : r ≠ 44 := by intro h; simp [h] at layoutSlot
      simp [installAugmentationCrossingRows, Function.update_of_ne notIndex]
  have control (i : ℕ) (m : ArithmeticState) (hm : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 44 = i ∧ m.nr 87 = rows.length :=
    ⟨hm.entry, hm.running, hm.index, (hm.registers 87 (by decide)).trans count⟩
  have iterate (i : ℕ) (within : i < rows.length) (m : ArithmeticState) (hm : inv i m) :
      ∃ t steps, steps ≤ 41 ∧ BlockRuns installAugmentationCrossingBlock steps m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 44 (t.nr 44 + t.nr 9)} := by
    let ports := ((rows[i]).1.val, (rows[i]).2.val)
    have m50 := hm.registers 50 (by decide)
    have m57 := hm.registers 57 (by decide)
    have m74 := hm.registers 74 (by decide)
    have m81 := hm.registers 81 (by decide)
    have m86 := hm.registers 86 (by decide)
    have m89 := hm.registers 89 (by decide)
    have layoutM : AugmentationInstallLayout k m := by
      obtain ⟨mates, map, nodes, pairs, work⟩ := layout
      exact ⟨by simpa only [m50, m57] using mates,
        by simpa only [m57, m74] using map,
        by simpa only [m74, m86] using nodes,
        by simpa only [m86, m89] using pairs,
        by simpa only [m89, m81] using work⟩
    have separated : m.nr 74 ≠ m.nr 89 := by
      have prior := layoutM.nodesBeforePairs
      have later := layoutM.pairsBeforeRepresentativeWork
      omega
    have stored : augmentationCrossingAt m (m.nr 44) = ports := by
      have cell := array i within
      have firstKept := hm.untouched _ (layout.crossing_unwritten (i := i + i) (by omega))
      have secondKept := hm.untouched (s.nr 86 + (i + i + 1))
        (layout.crossing_unwritten (i := i + i + 1) (by omega))
      unfold augmentationCrossingAt
      rw [hm.index, m86]
      change (m.nm (s.nr 86 + (i + i)), m.nm (s.nr 86 + (i + i) + 1)) = ports
      have second : m.nm (s.nr 86 + (i + i) + 1) = s.nm (s.nr 86 + (i + i) + 1) := by
        simpa only [Nat.add_assoc] using secondKept
      exact Prod.ext (firstKept.trans cell.1) (second.trans cell.2)
    have mapBound (v : ℕ) (finite : v < k) : m.nm (m.nr 57 + v) < k := by
      rw [m57, hm.untouched _ (layout.map_unwritten finite)]
      exact originalMap v finite
    have available : m.nr 82 + 2 ≤ k := by
      have past := hm.jobs
      omega
    have oneM := (hm.registers 9 (by decide)).trans one
    obtain ⟨t, ticks, runs, ready, budget, observed, unchanged, rr, rm⟩ :=
      installAugmentationCrossingBlock_correct hm.entry hm.running oneM
        ((hm.registers 14 (by decide)).trans zero) separated
    have exactView : AugmentationInstallView t (installAugmentationCrossingState m ports) := by
      rwa [← stored]
    have delayed := exactView.trans (hm.model.installCrossing ports)
    have stepModel : installAugmentationCrossingRows s (rows.take (i + 1)) =
        installAugmentationCrossingState (installAugmentationCrossingRows s (rows.take i)) ports := by
      rw [List.take_succ_eq_append_getElem within]
      simp only [installAugmentationCrossingRows, List.foldl_append, List.foldl_cons, List.foldl_nil, ports]
    have newView : AugmentationInstallView t (installAugmentationCrossingRows s (rows.take (i + 1))) := by
      rwa [stepModel]
    refine ⟨t, ticks, budget, runs, ready, rfl, ready, ?_, ?_, ?_, ?_, ?_,
      rr.trans hm.realRegisters, rm.trans hm.realMemory⟩
    · simp [unchanged 44 (by decide), unchanged 9 (by decide), hm.index, oneM]
    · intro r away
      have noIndex : r ≠ 44 := by intro h; exact away (by simp [h])
      have other : r ∉ [0, 6, 12, 13, 22, 26, 82] := by simp at away ⊢; omega
      simp only [Function.update_of_ne noIndex]
      exact (unchanged r other).trans (hm.registers r away)
    · refine ⟨newView.memory, ?_⟩
      intro r inLayout
      have noIndex : r ≠ 44 := by intro h; simp [h] at inLayout
      simpa only [Function.update_of_ne noIndex] using newView.registers r inLayout
    · intro address safe
      have safeM : AugmentationInstallUnwritten k m address := by
        simpa only [AugmentationInstallUnwritten, m50, m74, m89, m81] using safe
      have first : ports.1 < k := (rows[i]).1.isLt
      have second : ports.2 < k := (rows[i]).2.isLt
      change t.nm address = s.nm address
      exact (congrFun exactView.memory address).trans
        ((installAugmentationCrossingState_untouched first second layoutM mapBound available safeM).trans
          (hm.untouched address safe))
    · have increment := installAugmentationCrossingState_stack_le m ports
      have past := hm.jobs
      change (Function.update t.nr 44 (t.nr 44 + t.nr 9)) 82 ≤ 2 * (i + 1)
      rw [Function.update_of_ne (by decide : (82 : ℕ) ≠ 44), exactView.stack]
      omega
  obtain ⟨last, steps, final, cost, ran⟩ := countedLoopFromZero_bounded 9 44 87 rows.length 41
    installAugmentationCrossingBlock inv entry running initial control iterate
  refine ⟨_, steps, ran, final.running, by omega, final.jobs, ?_,
    final.untouched, final.registers, final.realRegisters, final.realMemory⟩
  exact ⟨by simpa only [relocateState, List.take_length] using final.model.memory,
    fun r hr => by simpa only [relocateState, List.take_length] using final.model.registers r hr⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentInstallRAM

/-! matching/MatchingAugmentRemapRAM.lean -/
section RppSource_MatchingAugmentRemapRAM
namespace VehicleRoutingSurvey.Routing

private def initializedAugmentationRepresentative (s : ArithmeticState) : ArithmeticState :=
  let address := s.nr 89 + s.nr 44
  {s with
    pc := 2
    nr := Function.update s.nr 6 address
    nm := Function.update s.nm address (s.nr 44)}

private theorem initializeAugmentationRepresentative_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    BlockRuns initializeAugmentationRepresentative 2 s (initializedAugmentationRepresentative s) := by
  apply BlockRuns.of_running_exit
  · simp [initializeAugmentationRepresentative, initializedAugmentationRepresentative, arithmeticStep,
      Function.iterate_succ_apply', entry, running]
  · exact running
  · rfl

private structure AugmentationRepresentativeIdentityScan (s : ArithmeticState) (i : ℕ)
    (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  running : m.halted = false
  index : m.nr 44 = i
  fixed : ∀ r, r ≠ 6 → r ≠ 44 → m.nr r = s.nr r
  initialized : ∀ j < i, m.nm (s.nr 89 + j) = j
  unchanged : ∀ address, address < s.nr 89 ∨ s.nr 89 + i ≤ address → m.nm address = s.nm address
  realRegisters : m.rr = s.rr
  realMemory : m.rm = s.rm

theorem initializeAugmentationRepresentativeLoop_correct {s : ArithmeticState} {k : ℕ}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (dimension : s.nr 55 = k) :
    ∃ t, BlockRuns (countedLoopFromZero 9 44 55 initializeAugmentationRepresentative) (1 + (k * 5 + 1)) s t ∧
      t.halted = false ∧ (∀ j < k, t.nm (s.nr 89 + j) = j) ∧
      (∀ address, address < s.nr 89 ∨ s.nr 89 + k ≤ address → t.nm address = s.nm address) ∧
      (∀ r, r ≠ 6 → r ≠ 44 → t.nr r = s.nr r) ∧ t.rr = s.rr ∧ t.rm = s.rm := by
  let inv := AugmentationRepresentativeIdentityScan s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 44 0} := by
    refine ⟨rfl, running, by simp, ?_, ?_, fun _ _ => rfl, rfl, rfl⟩
    · intro r _ away
      simp [Function.update_of_ne away]
    · intro _ impossible
      omega
  have control (i : ℕ) (m : ArithmeticState) (hm : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 44 = i ∧ m.nr 55 = k :=
    ⟨hm.entry, hm.running, hm.index, (hm.fixed 55 (by decide) (by decide)).trans dimension⟩
  have iterate (i : ℕ) (_ : i < k) (m : ArithmeticState) (hm : inv i m) :
      ∃ u, BlockRuns initializeAugmentationRepresentative 2 m u ∧ u.halted = false ∧
        inv (i + 1) {u with pc := 0, nr := Function.update u.nr 44 (u.nr 44 + u.nr 9)} := by
    let u := initializedAugmentationRepresentative m
    have base := hm.fixed 89 (by decide) (by decide)
    have inc := (hm.fixed 9 (by decide) (by decide)).trans one
    have updated : u.nm = Function.update m.nm (s.nr 89 + i) i := by
      simp [u, initializedAugmentationRepresentative, base, hm.index]
    refine ⟨u, initializeAugmentationRepresentative_correct hm.entry hm.running, hm.running,
      rfl, hm.running, ?_, ?_, ?_, ?_, hm.realRegisters, hm.realMemory⟩
    · simp [u, initializedAugmentationRepresentative, hm.index, inc]
    · intro r awayAddress awayCounter
      simp [u, initializedAugmentationRepresentative, Function.update_of_ne awayAddress,
        Function.update_of_ne awayCounter, hm.fixed r awayAddress awayCounter]
    · intro j within
      change u.nm (s.nr 89 + j) = j
      rw [updated]
      by_cases equal : j = i
      · simp [equal]
      · rw [Function.update_of_ne (by omega)]
        exact hm.initialized j (by omega)
    · intro address outside
      change u.nm address = s.nm address
      rw [updated, Function.update_of_ne (by omega)]
      exact hm.unchanged address (by omega)
  obtain ⟨last, final, ran⟩ := countedLoopFromZero_correct 9 44 55 k 2
    initializeAugmentationRepresentative inv entry running initial control iterate
  exact ⟨_, ran, final.running, final.initialized, final.unchanged, final.fixed,
    final.realRegisters, final.realMemory⟩

private structure AugmentationRepresentativeRemapScan (s : ArithmeticState) (i : ℕ)
    (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  running : m.halted = false
  index : m.nr 44 = i
  fixed : ∀ r, r ∉ [0, 6, 15, 26, 44] → m.nr r = s.nr r
  mapped : ∀ j < i, m.nm (s.nr 57 + j) = s.nm (s.nr 89 + s.nm (s.nr 57 + j))
  unchanged : ∀ address, address < s.nr 57 ∨ s.nr 57 + i ≤ address → m.nm address = s.nm address
  realRegisters : m.rr = s.rr
  realMemory : m.rm = s.rm

/-- Repoint each original vertex at its blossom's new exposed vertex.
The work table and the blossom rebase jobs remain available. -/
theorem remapAugmentationOriginalLoop_correct {s : ArithmeticState} {k : ℕ}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (dimension : s.nr 55 = k)
    (separate : s.nr 57 + k ≤ s.nr 89) :
    ∃ t, BlockRuns (countedLoopFromZero 9 44 55 remapAugmentationOriginalBlock) (1 + (k * 8 + 1)) s t ∧
      t.halted = false ∧ (∀ j < k, t.nm (s.nr 57 + j) = s.nm (s.nr 89 + s.nm (s.nr 57 + j))) ∧
      (∀ address, address < s.nr 57 ∨ s.nr 57 + k ≤ address → t.nm address = s.nm address) ∧
      (∀ r, r ∉ [0, 6, 15, 26, 44] → t.nr r = s.nr r) ∧ t.rr = s.rr ∧ t.rm = s.rm := by
  let inv := AugmentationRepresentativeRemapScan s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 44 0} := by
    refine ⟨rfl, running, by simp, ?_, ?_, fun _ _ => rfl, rfl, rfl⟩
    · intro r away
      have notIndex : r ≠ 44 := by intro yes; exact away (by simp [yes])
      simp [Function.update_of_ne notIndex]
    · intro _ impossible
      omega
  have control (i : ℕ) (m : ArithmeticState) (hm : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 44 = i ∧ m.nr 55 = k :=
    ⟨hm.entry, hm.running, hm.index, (hm.fixed 55 (by decide)).trans dimension⟩
  have iterate (i : ℕ) (within : i < k) (m : ArithmeticState) (hm : inv i m) :
      ∃ u, BlockRuns remapAugmentationOriginalBlock 5 m u ∧ u.halted = false ∧
        inv (i + 1) {u with pc := 0, nr := Function.update u.nr 44 (u.nr 44 + u.nr 9)} := by
    obtain ⟨u, ran, ready, memory, realMemory, realRegisters, regs⟩ :=
      remapAugmentationOriginalBlock_correct hm.entry hm.running
    have original := hm.unchanged (s.nr 57 + i) (.inr (by omega))
    have mapBase := hm.fixed 57 (by decide)
    have workBase := hm.fixed 89 (by decide)
    have target : m.nm (s.nr 89 + s.nm (s.nr 57 + i)) = s.nm (s.nr 89 + s.nm (s.nr 57 + i)) :=
      hm.unchanged _ (.inr (by omega))
    have written : u.nm = Function.update m.nm (s.nr 57 + i) (s.nm (s.nr 89 + s.nm (s.nr 57 + i))) := by
      rw [memory, hm.index, mapBase, workBase, original, target]
    refine ⟨u, ran, ready, rfl, ready, ?_, ?_, ?_, ?_, realRegisters.trans hm.realRegisters,
      realMemory.trans hm.realMemory⟩
    · simp [regs 44 (by decide), regs 9 (by decide), hm.index, (hm.fixed 9 (by decide)).trans one]
    · intro r away
      have notIndex : r ≠ 44 := by intro yes; exact away (by simp [yes])
      have readOnly : r ∉ [0, 6, 15, 26] := by simp at away ⊢; omega
      simp only [Function.update_of_ne notIndex]
      exact (regs r readOnly).trans (hm.fixed r away)
    · intro j before
      change u.nm (s.nr 57 + j) = _
      rw [written]
      by_cases same : j = i
      · simp [same]
      · rw [Function.update_of_ne (by omega)]
        exact hm.mapped j (by omega)
    · intro address outside
      change u.nm address = s.nm address
      rw [written, Function.update_of_ne (by omega)]
      exact hm.unchanged address (by omega)
  obtain ⟨last, final, ran⟩ := countedLoopFromZero_correct 9 44 55 k 5 remapAugmentationOriginalBlock
    inv entry running initial control iterate
  exact ⟨_, ran, final.running, final.mapped, final.unchanged, final.fixed,
    final.realRegisters, final.realMemory⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentRemapRAM

/-! matching/MatchingAugmentPreRebase.lean -/
section RppSource_MatchingAugmentPreRebase
namespace VehicleRoutingSurvey.Routing

private def setAugmentationLoopConstants : List ArithmeticInstruction :=
  [.natConst 9 1, .natConst 14 0]

private theorem setAugmentationLoopConstants_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns setAugmentationLoopConstants 2 s t ∧ t.halted = false ∧
      t.nr 9 = 1 ∧ t.nr 14 = 0 ∧ t.nm = s.nm ∧ t.rr = s.rr ∧ t.rm = s.rm ∧
      ∀ r, r ∉ [9, 14] → t.nr r = s.nr r := by
  let t := (arithmeticStep setAugmentationLoopConstants)^[2] s
  have ready : t.halted = false := by
    simp [t, setAugmentationLoopConstants, arithmeticStep, Function.iterate_succ_apply', entry, running]
  have exit : t.pc = setAugmentationLoopConstants.length := by
    simp [t, setAugmentationLoopConstants, arithmeticStep, Function.iterate_succ_apply', entry, running]
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | intro r away
      exact arithmeticRun_keeps_from_destination_list _ (by decide) away s 2
    | simp [t, setAugmentationLoopConstants, arithmeticStep, Function.iterate_succ_apply', entry, running]

def prepareMatchingAugmentationRebaseBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock (appendBlock (appendBlock setAugmentationLoopConstants resetMatchingRebaseJobsBlock)
    (countedLoopFromZero 9 44 55 initializeAugmentationRepresentative))
      (countedLoopFromZero 9 44 87 installAugmentationCrossingBlock))
    (countedLoopFromZero 9 44 55 remapAugmentationOriginalBlock)

theorem appendBlock_assoc (a b c : List ArithmeticInstruction) :
    appendBlock (appendBlock a b) c = appendBlock a (appendBlock b c) := by
  have shifted : relocateInstruction (a.length + b.length) =
      relocateInstruction a.length ∘ relocateInstruction b.length := by
    funext ins
    cases ins <;> simp [relocateInstruction, Nat.add_assoc]
  simp only [appendBlock, List.length_append, List.length_map, List.map_append, List.map_map, List.append_assoc,
    shifted]

theorem applyMatchingAugmentationCrossingsBlock_split : applyMatchingAugmentationCrossingsBlock =
    appendBlock prepareMatchingAugmentationRebaseBlock rebaseMatchingQueuedNodesBlock := by
  simp only [applyMatchingAugmentationCrossingsBlock, prepareMatchingAugmentationRebaseBlock,
    setAugmentationLoopConstants, appendBlock_assoc]



private theorem AugmentationInstallView.crossings {k : ℕ} {s t : ArithmeticState}
    (same : AugmentationInstallView s t) (rows : List (Fin k × Fin k)) :
    AugmentationInstallView (installAugmentationCrossingRows s rows) (installAugmentationCrossingRows t rows) := by
  induction rows generalizing s t with
  | nil => exact same
  | cons p rows ih => exact ih (same.installCrossing (p.1.val, p.2.val))







theorem prepareMatchingAugmentationRebaseBlock_correct {k : ℕ} {s : ArithmeticState}
    (rows : List (Fin k × Fin k)) (entry : s.pc = 0) (running : s.halted = false)
    (dimension : s.nr 55 = k) (count : s.nr 87 = rows.length)
    (pairs : AugmentationCrossingArray s.nm (s.nr 86) rows) (capacity : 2 * rows.length ≤ k)
    (layout : AugmentationInstallLayout k (augmentationCrossingSeed s k))
    (originalMap : ∀ i < k, s.nm (s.nr 57 + i) < k) :
    ∃ (t : ArithmeticState) (steps : ℕ),
      BlockRuns prepareMatchingAugmentationRebaseBlock steps s t ∧ t.halted = false ∧
      steps ≤ 35 * k + 12 ∧ AugmentationPreRebaseReady rows s t := by
  let seed := augmentationCrossingSeed s k
  let model := installAugmentationCrossingRows seed rows
  have seedFixed (r : ℕ) (a : r ≠ 81) (b : r ≠ 82) : seed.nr r = s.nr r := by
    simp [seed, augmentationCrossingSeed, Function.update_of_ne a, Function.update_of_ne b]
  have seedBase : seed.nr 81 = s.nr 80 + 3 * k := by simp [seed, augmentationCrossingSeed]
  have seedCount : seed.nr 82 = 0 := by simp [seed, augmentationCrossingSeed]
  have startLayout : s.nr 50 + k ≤ s.nr 57 ∧ s.nr 57 + k ≤ s.nr 74 ∧ s.nr 74 + k ≤ s.nr 86 ∧
      s.nr 86 + k ≤ s.nr 89 ∧ s.nr 89 + k ≤ s.nr 80 + 3 * k := by
    change AugmentationInstallLayout k seed at layout
    obtain ⟨a, b, c, d, e⟩ := layout
    simpa only [seedFixed 50 (by decide) (by decide), seedFixed 57 (by decide) (by decide),
      seedFixed 74 (by decide) (by decide), seedFixed 86 (by decide) (by decide),
      seedFixed 89 (by decide) (by decide), seedBase] using And.intro a (And.intro b (And.intro c (And.intro d e)))
  obtain ⟨before, set, live, one, zero, beforeMemory, beforeRR, beforeRM, beforeFixed⟩ :=
    setAugmentationLoopConstants_correct entry running
  let a := {before with pc := 0}
  obtain ⟨reset, resetRun, resetLive, resetBase, resetCount, resetMemory, resetRM, resetRR, resetFixed⟩ :=
    resetMatchingRebaseJobsBlock_correct (s := a) rfl live
  have resetKept (r : ℕ) (away : r ∉ [0, 6, 9, 14, 81, 82]) : reset.nr r = s.nr r := by
    have ha : r ∉ [0, 6, 81, 82] := by simp at away ⊢; omega
    have hb : r ∉ [9, 14] := by simp at away ⊢; omega
    exact (resetFixed r ha).trans (beforeFixed r hb)
  have resetOne : reset.nr 9 = 1 := (resetFixed 9 (by decide)).trans one
  have resetZero : reset.nr 14 = 0 := (resetFixed 14 (by decide)).trans zero
  have actualBase : reset.nr 81 = seed.nr 81 := by
    rw [resetBase, seedBase]
    change before.nr 80 + 3 * before.nr 55 = _
    rw [beforeFixed 80 (by decide), beforeFixed 55 (by decide), dimension]
  let b := {reset with pc := 0}
  obtain ⟨initialized, idRun, idLive, idRows, idKept, idFixed, idRR, idRM⟩ :=
    initializeAugmentationRepresentativeLoop_correct (s := b) rfl resetLive resetOne
      ((resetKept 55 (by decide)).trans dimension)
  have idKeptReg (r : ℕ) (away : r ∉ [0, 6, 9, 14, 44, 81, 82]) : initialized.nr r = s.nr r := by
    have n6 : r ≠ 6 := by intro equal; exact away (by simp [equal])
    have n44 : r ≠ 44 := by intro equal; exact away (by simp [equal])
    have kept : r ∉ [0, 6, 9, 14, 81, 82] := by simp at away ⊢; omega
    exact (idFixed r n6 n44).trans (resetKept r kept)
  have idMemory : initialized.nm = seed.nm := by
    funext address
    have base := resetKept 89 (by decide)
    by_cases within : s.nr 89 ≤ address ∧ address < s.nr 89 + k
    · have atIndex : reset.nr 89 + (address - s.nr 89) = address := by rw [base]; omega
      have correct := idRows (address - s.nr 89) (by omega)
      change initialized.nm (reset.nr 89 + (address - s.nr 89)) = _ at correct
      rw [atIndex] at correct
      simpa [seed, augmentationCrossingSeed, within] using correct
    · have outside : address < b.nr 89 ∨ b.nr 89 + k ≤ address := by
        change address < reset.nr 89 ∨ reset.nr 89 + k ≤ address
        rw [base]
        omega
      simpa [seed, augmentationCrossingSeed, within] using
        (idKept address outside).trans ((congrFun resetMemory address).trans (congrFun beforeMemory address))
  have idBase := (idFixed 81 (by decide) (by decide)).trans actualBase
  have idCount := (idFixed 82 (by decide) (by decide)).trans resetCount
  have idOne := (idFixed 9 (by decide) (by decide)).trans resetOne
  have idZero := (idFixed 14 (by decide) (by decide)).trans resetZero
  let c := {initialized with pc := 0}
  have haveSeed : AugmentationInstallView c seed := by
    refine ⟨idMemory, ?_⟩
    intro r member
    by_cases atBase : r = 81
    · subst r; exact idBase
    by_cases atCount : r = 82
    · subst r; exact idCount.trans seedCount.symm
    · exact (idKeptReg r (by simp at member ⊢; omega)).trans (seedFixed r atBase atCount).symm
  have initLayout : AugmentationInstallLayout k c := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals
      change initialized.nr _ + k ≤ initialized.nr _
      first
      | rw [idKeptReg 50 (by decide), idKeptReg 57 (by decide)]; exact startLayout.1
      | rw [idKeptReg 57 (by decide), idKeptReg 74 (by decide)]; exact startLayout.2.1
      | rw [idKeptReg 74 (by decide), idKeptReg 86 (by decide)]; exact startLayout.2.2.1
      | rw [idKeptReg 86 (by decide), idKeptReg 89 (by decide)]; exact startLayout.2.2.2.1
      | rw [idKeptReg 89 (by decide), idBase, seedBase]; exact startLayout.2.2.2.2
  have initPairs : AugmentationCrossingArray c.nm (c.nr 86) rows := by
    change AugmentationCrossingArray initialized.nm (initialized.nr 86) rows
    rw [idKeptReg 86 (by decide), idMemory]
    intro i within
    have first : s.nr 86 + (i + i) < s.nr 89 := by have h := startLayout.2.2.2.1; omega
    have second : s.nr 86 + (i + i) + 1 < s.nr 89 := by have h := startLayout.2.2.2.1; omega
    simpa [seed, augmentationCrossingSeed, not_le.mpr first, not_le.mpr second] using pairs i within
  have initMap (i : ℕ) (finite : i < k) : c.nm (c.nr 57 + i) < k := by
    change initialized.nm (initialized.nr 57 + i) < k
    rw [idKeptReg 57 (by decide), idMemory]
    have a := startLayout.2.1
    have b := startLayout.2.2.1
    have c := startLayout.2.2.2.1
    have before : s.nr 57 + i < s.nr 89 := by omega
    simpa [seed, augmentationCrossingSeed, not_le.mpr before] using originalMap i finite
  obtain ⟨installed, spent, crossRun, crossLive, crossBudget, stackBound, crossView, crossKept,
    crossFixed, crossRR, crossRM⟩ := installAugmentationCrossingLoop_correct rows (s := c) rfl idLive
      idOne idZero idCount ((idKeptReg 87 (by decide)).trans count) initPairs capacity initLayout initMap
  have exactCross : AugmentationInstallView installed model := crossView.trans (haveSeed.crossings rows)
  have instFixed (r : ℕ) (away : r ∉ [0, 6, 9, 12, 13, 14, 22, 26, 44, 81, 82]) :
      installed.nr r = s.nr r := by
    have a : r ∉ [0, 6, 12, 13, 22, 26, 44, 82] := by simp at away ⊢; omega
    have b : r ∉ [0, 6, 9, 14, 44, 81, 82] := by simp at away ⊢; omega
    exact (crossFixed r a).trans (idKeptReg r b)
  have instOne : installed.nr 9 = 1 := (crossFixed 9 (by decide)).trans idOne
  have instZero : installed.nr 14 = 0 := (crossFixed 14 (by decide)).trans idZero
  let d := {installed with pc := 0}
  have mapSpace : d.nr 57 + k ≤ d.nr 89 := by
    change installed.nr 57 + k ≤ installed.nr 89
    rw [instFixed 57 (by decide), instFixed 89 (by decide)]
    have a := startLayout.2.1
    have b := startLayout.2.2.1
    have c := startLayout.2.2.2.1
    omega
  obtain ⟨out, remap, ready, mapped, outKept, outFixed, outRR, outRM⟩ :=
    remapAugmentationOriginalLoop_correct (s := d) rfl crossLive instOne ((instFixed 55 (by decide)).trans dimension)
      mapSpace
  have all := ((((set.append resetRun).append idRun).append crossRun).append remap)
  refine ⟨_, _, all, ready, by omega, ?_⟩
  constructor
  · exact (outFixed 9 (by decide)).trans instOne
  · exact (outFixed 14 (by decide)).trans instZero
  · exact (outFixed 82 (by decide)).trans exactCross.stack
  · change out.nr 82 ≤ _
    rwa [outFixed 82 (by decide)]
  · exact (outFixed 81 (by decide)).trans ((crossFixed 81 (by decide)).trans (idBase.trans seedBase))
  · change out.nm = remappedAugmentationMemory s model k
    funext address
    have mapBase : d.nr 57 = s.nr 57 := instFixed 57 (by decide)
    have workBase : d.nr 89 = s.nr 89 := instFixed 89 (by decide)
    by_cases within : s.nr 57 ≤ address ∧ address < s.nr 57 + k
    · have atIndex : d.nr 57 + (address - s.nr 57) = address := by rw [mapBase]; omega
      have revised := mapped (address - s.nr 57) (by omega)
      rw [atIndex, workBase] at revised
      change out.nm address = installed.nm (s.nr 89 + installed.nm address) at revised
      simpa [remappedAugmentationMemory, within, exactCross.memory] using revised
    · have outside : address < d.nr 57 ∨ d.nr 57 + k ≤ address := by rw [mapBase]; omega
      rw [remappedAugmentationMemory, if_neg within]
      exact (outKept address outside).trans (congrFun exactCross.memory address)
  · intro address away
    have crossOutside : AugmentationInstallUnwritten k c address := by
      unfold AugmentationInstallUnwritten
      rw [haveSeed.registers 50 (by decide), haveSeed.registers 74 (by decide),
        haveSeed.registers 89 (by decide), haveSeed.registers 81 (by decide)]
      exact away.1
    have initOutside : address < b.nr 89 ∨ b.nr 89 + k ≤ address := by
      change address < reset.nr 89 ∨ reset.nr 89 + k ≤ address
      rw [resetKept 89 (by decide)]
      have zone : address < seed.nr 89 ∨ seed.nr 89 + k ≤ address := away.1.2.2.1
      simpa only [seedFixed 89 (by decide) (by decide)] using zone
    have mapOutside : address < d.nr 57 ∨ d.nr 57 + k ≤ address := by
      change address < installed.nr 57 ∨ installed.nr 57 + k ≤ address
      rw [instFixed 57 (by decide)]
      exact away.2
    exact (outKept address mapOutside).trans ((crossKept address crossOutside).trans
      ((idKept address initOutside).trans ((congrFun resetMemory address).trans (congrFun beforeMemory address))))
  · intro address below
    have a := startLayout.1
    have b := startLayout.2.1
    have e := startLayout.2.2.1
    have f := startLayout.2.2.2.1
    have unchangedOut := outKept address (.inl (by change address < installed.nr 57; rw [instFixed 57 (by decide)]; omega))
    have untouchedInstall := crossKept address (initLayout.prefix_unwritten
      (by change address < initialized.nr 50; rwa [idKeptReg 50 (by decide)]))
    have untouchedSeed : initialized.nm address = s.nm address := by
      have before : address < s.nr 89 := by omega
      rw [idMemory]
      simp [seed, augmentationCrossingSeed, not_le.mpr before]
    exact unchangedOut.trans (untouchedInstall.trans untouchedSeed)
  · exact outRR.trans (crossRR.trans (idRR.trans (resetRR.trans beforeRR)))
  · exact outRM.trans (crossRM.trans (idRM.trans (resetRM.trans beforeRM)))
  · intro r away
    have a : r ∉ [0, 6, 15, 26, 44] := by simp at away ⊢; omega
    have b : r ∉ [0, 6, 9, 12, 13, 14, 22, 26, 44, 81, 82] := by simp at away ⊢; omega
    exact (outFixed r a).trans (instFixed r b)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentPreRebase

/-! matching/MatchingRebaseTaskMemory.lean -/
section RppSource_MatchingRebaseTaskMemory
namespace VehicleRoutingSurvey.Routing

theorem MatchingMemberTree.readable_after_move {tree : MatchingMemberTree}
    {before after : ℕ → ℕ} {startBase countBase : ℕ} {preserved readable : ℕ → Prop}
    (region : tree.readable before startBase countBase (fun address => preserved address ∧ readable address))
    (same : ∀ address, preserved address → after address = before address) :
    tree.readable after startBase countBase readable := by
  induction tree with
  | nil => trivial
  | leaf v siblings ih => exact ih region
  | blossom r node children siblings ihChildren ihSiblings =>
    obtain ⟨header, count, records, below, later⟩ := region
    refine ⟨header.2, count.2, ?_, ihChildren below, ihSiblings later⟩
    intro i inside word within
    rw [same (startBase + node) header.1]
    exact (records i inside word within).2

theorem MatchingMemberTree.recordsAbove_after_move {tree : MatchingMemberTree}
    {before after : ℕ → ℕ} {startBase countBase lower : ℕ} {preserved : ℕ → Prop}
    (region : tree.readable before startBase countBase preserved)
    (above : tree.recordsAbove before startBase lower)
    (same : ∀ address, preserved address → after address = before address) :
    tree.recordsAbove after startBase lower := by
  induction tree with
  | nil => trivial
  | leaf v siblings ih => exact ih region above
  | blossom r node children siblings ihChildren ihSiblings =>
    obtain ⟨header, _, _, below, later⟩ := region
    obtain ⟨address, childAbove, siblingAbove⟩ := above
    exact ⟨by rwa [same (startBase + node) header], ihChildren below childAbove, ihSiblings later siblingAbove⟩



end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseTaskMemory

/-! matching/MatchingRebaseLoad.lean -/
section RppSource_MatchingRebaseLoad
namespace VehicleRoutingSurvey.Routing

/-- A popped request names a live odd cycle and an original vertex housed in
the specified immediate child of that cycle. -/
structure MatchingRebaseCycleInput (s : ArithmeticState) (children : MatchingMemberTree)
    (free owner : ℕ) : Prop where
  members : MatchingMemberRoot s children
  odd : Odd children.arity
  fit : children.arity ≤ s.nr 55
  inside : free < children.arity
  desired : (s.nr 29, owner) ∈ matchingMemberAssignments children
  uniquely : ∀ i (hi : i < children.rootKeys.length), children.rootKeys[i].1 = owner ↔ i = free

structure MatchingRebaseCycleLoaded (s t : ArithmeticState) (children : MatchingMemberTree) (free : ℕ) : Prop where
  one : t.nr 9 = 1
  zero : t.nr 14 = 0
  halvingZero : t.nr 23 = 0
  inside : free < t.nr 19
  odd : Odd (t.nr 19)
  fit : t.nr 19 ≤ t.nr 55
  finds : ∀ i < t.nr 19,
    (matchingCycleChildAt t.nm (t.nr 18 + 4 * i)).representative = t.nm (t.nr 79 + t.nr 29) ↔ i = free
  assignments : ∀ p ∈ matchingMemberAssignments children, t.nm (t.nr 79 + p.1) = p.2
  recordBase : t.nr 18 = s.nm (s.nr 77 + s.nr 22)
  outside : ∀ a, outsideMatchingMemberScratch s a → t.nm a = s.nm a
  real : t.rm = s.rm
  realRegisters : t.rr = s.rr
  registers : ∀ r, r ∉ [0, 6, 7, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27, 28, 87] → t.nr r = s.nr r
  count : t.nr 19 = children.arity

set_option maxRecDepth 4096 in
/-- The actual member traversal and header loads establish the input of the cyclic rematch. -/
theorem loadMatchingRebaseCycleBlock_correct {s : ArithmeticState} {children : MatchingMemberTree}
    {free owner : ℕ} (request : MatchingRebaseCycleInput s children free owner)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0) :
    ∃ t steps, steps ≤ 93 * s.nr 55 + 19 ∧ BlockRuns loadMatchingRebaseCycleBlock steps s t ∧
      t.halted = false ∧ MatchingRebaseCycleLoaded s t children free := by
  let saved := {s with pc := 1, nr := Function.update s.nr 27 (s.nr 22)}
  have save : BlockRuns [.natAdd 27 22 14] 1 s saved := by
    apply BlockRuns.of_running_exit
    · simp [saved, arithmeticStep, entry, running, zero]
    · exact running
    · rfl
  let start := {saved with pc := 0}
  have bank (r : ℕ) (away : r ≠ 27 := by decide) : start.nr r = s.nr r := by simp [start, saved, away]
  have scratch : outsideMatchingMemberScratch start = outsideMatchingMemberScratch s := by
    funext a
    simp only [outsideMatchingMemberScratch, bank 79, bank 80, bank 55]
  have outsideAt (a : ℕ) (outside : outsideMatchingMemberScratch s a) :
      outsideMatchingMemberScratch start a := by
    simpa only [outsideMatchingMemberScratch, bank 79, bank 80, bank 55] using outside
  have mappedRoot : MatchingMemberRoot start children := by
    refine ⟨?_, ?_, ?_, ?_, request.members.unique, ?_, ?_⟩
    · simpa only [bank 22] using request.members.proper
    · simpa only [bank 22, bank 77, bank 78] using request.members.encoded
    · simpa only [scratch, bank 22, bank 77, bank 78] using request.members.readable
    · simpa only [bank 22, bank 77, bank 80, bank 55] using request.members.above
    · simpa only [bank 55] using request.members.valid
    · simpa only [bank 79, bank 80, bank 55] using request.members.separated
  obtain ⟨m, walkTicks, walkCost, walk, mLive, _, mZero, assignment, _, mNat, mReal, mReals, mKeeps⟩ :=
    mapMatchingCycleNodeMembers_spec start children mappedRoot rfl running ((bank 9).trans one)
  let mapExit := {m with pc := 0}
  have held (r : ℕ) (safe : r ∉ [0, 6, 7, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 28, 87] := by decide)
      (away : r ≠ 27 := by decide) : m.nr r = s.nr r := (mKeeps r safe).trans (bank r away)
  have savedNode : m.nr 27 = s.nr 22 := by
    rw [mKeeps 27 (by decide)]
    simp [start, saved]
  have beforeReads (a : ℕ) (outside : outsideMatchingMemberScratch s a) : m.nm a = s.nm a :=
    mNat a (outsideAt a outside)
  let restored := {mapExit with pc := 1, nr := Function.update mapExit.nr 22 (mapExit.nr 27)}
  have putNode : BlockRuns [.natAdd 22 27 14] 1 mapExit restored := by
    apply BlockRuns.of_running_exit
    · have liveZero : mapExit.nr 14 = 0 := (held 14).trans zero
      have live : mapExit.halted = false := mLive
      simp [restored, arithmeticStep, live, liveZero, show mapExit.pc = 0 from rfl]
    · exact mLive
    · rfl
  let headerIn := {restored with pc := 0}
  have headerFixed (r : ℕ) (safe : r ≠ 22 := by decide) : headerIn.nr r = m.nr r := by
    simp [headerIn, restored, mapExit, safe]
  have node : headerIn.nr 22 = s.nr 22 := by
    simp [headerIn, restored, mapExit, savedNode]
  obtain ⟨h, readHeader, hLive, hBase, hCount, hNat, hReal, hReals, hKeeps⟩ :=
    readMatchingCycleHeader_spec headerIn rfl mLive
  have keeps (r : ℕ) (safe : r ∉ [0, 6, 7, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27, 28, 87]) :
      h.nr r = s.nr r :=
    (hKeeps r (by simp at safe ⊢; omega)).trans ((headerFixed r (by simp at safe; omega)).trans
      (held r (by simp at safe ⊢; omega) (by simp at safe; omega)))
  have unchanged (a : ℕ) (outside : outsideMatchingMemberScratch s a) : h.nm a = s.nm a :=
    (congrFun hNat a).trans (beforeReads a outside)
  let recordBase := s.nm (s.nr 77 + s.nr 22)
  have readable := request.members.readable
  change outsideMatchingMemberScratch s (s.nr 77 + s.nr 22) ∧
    outsideMatchingMemberScratch s (s.nr 78 + s.nr 22) ∧
    (∀ i < children.arity, ∀ w < 4, outsideMatchingMemberScratch s (recordBase + 4 * i + w)) ∧ _ at readable
  have base : h.nr 18 = recordBase := by
    rw [hBase, headerFixed 77, held 77, node]
    exact beforeReads _ readable.1
  have encoding := request.members.encoded
  change s.nm (s.nr 78 + s.nr 22) = children.arity ∧
    (∀ i (hi : i < children.rootKeys.length),
      let cell := matchingCycleChildAt s.nm (recordBase + 4 * i)
      MatchingMemberTree.rootKey cell.representative cell.node = children.rootKeys[i]) ∧ _ at encoding
  have count : h.nr 19 = children.arity := by
    rw [hCount, headerFixed 78, held 78, node]
    exact (beforeReads _ readable.2.1).trans encoding.1
  have atDesired : h.nm (h.nr 79 + h.nr 29) = owner := by
    rw [keeps 79 (by decide), keeps 29 (by decide), hNat]
    exact assignment (s.nr 29, owner) request.desired
  have finds (i : ℕ) (inside : i < h.nr 19) :
      (matchingCycleChildAt h.nm (h.nr 18 + 4 * i)).representative = h.nm (h.nr 79 + h.nr 29) ↔ i = free := by
    have hi : i < children.arity := inside.trans_le (le_of_eq count)
    have onCycle : i < children.rootKeys.length := by simpa only [MatchingMemberTree.rootKeys_length] using hi
    have repBytes : h.nm (recordBase + 4 * i) = s.nm (recordBase + 4 * i) :=
      unchanged _ (by simpa only [Nat.add_zero] using readable.2.2.1 i hi 0 (by decide))
    have which : (matchingCycleChildAt s.nm (recordBase + 4 * i)).representative = children.rootKeys[i].1 :=
      congrArg Prod.fst (encoding.2.1 i onCycle)
    rw [base, atDesired]
    change h.nm (recordBase + 4 * i) = owner ↔ i = free
    rw [repBytes]
    change (matchingCycleChildAt s.nm (recordBase + 4 * i)).representative = owner ↔ i = free
    rw [which]
    exact request.uniquely i onCycle
  have run : BlockRuns loadMatchingRebaseCycleBlock (1 + (walkTicks + (1 + 4))) s _ :=
    save.append (walk.append (putNode.append readHeader))
  rw [bank 55] at walkCost
  have loaded : MatchingRebaseCycleLoaded s h children free := by
    refine ⟨(keeps 9 (by decide)).trans one, (keeps 14 (by decide)).trans zero, ?_,
      count.symm ▸ request.inside, count.symm ▸ request.odd, ?_, finds, ?_, base, unchanged,
      hReal.trans mReal, hReals.trans mReals, keeps, count⟩
    · exact (hKeeps 23 (by decide)).trans ((headerFixed 23).trans mZero)
    · rw [count, keeps 55 (by decide)]
      exact request.fit
    · intro p proper
      rw [keeps 79 (by decide), hNat]
      exact assignment p proper
  refine ⟨_, _, by omega, run, hLive, ?_⟩
  exact ⟨loaded.one, loaded.zero, loaded.halvingZero, loaded.inside, loaded.odd, loaded.fit,
    loaded.finds, loaded.assignments, loaded.recordBase, loaded.outside, loaded.real, loaded.realRegisters,
    loaded.registers, loaded.count⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseLoad

/-! matching/MatchingRebaseNodeProof.lean -/
section RppSource_MatchingRebaseNodeProof
namespace VehicleRoutingSurvey.Routing

private theorem selectMatchingRebaseChild_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (zero : s.nr 14 = 0) :
    let chosen := s.nr 15 = s.nr 27
    ∃ t steps, steps ≤ 6 ∧ BlockRuns selectMatchingRebaseChild steps s t ∧ t.halted = false ∧
      t.nr 46 = (if chosen then s.nr 7 else s.nr 46) ∧ t.nr 47 = (if chosen then s.nr 25 else s.nr 47) ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
  intro chosen
  have empty : BlockRuns [] 0 s s := ⟨fun i less => (Nat.not_lt_zero i less).elim, rfl, entry⟩
  rcases lt_trichotomy (s.nr 15) (s.nr 27) with before | equal | after
  · have inner := branchOnAtMost_right 27 15 saveMatchingRebaseChildIndex [] entry running before empty running
    have run := branchOnAtMost_left 15 27 (branchOnAtMost 27 15 saveMatchingRebaseChildIndex []) []
      entry running before.le inner running
    exact ⟨_, 3, by decide, run, running, by simp [chosen, before.ne], by simp [chosen, before.ne], rfl, rfl, rfl⟩
  · let t := {s with pc := 2, nr := Function.update (Function.update s.nr 46 (s.nr 7)) 47 (s.nr 25)}
    have remember : BlockRuns saveMatchingRebaseChildIndex 2 s t := by
      apply BlockRuns.of_running_exit
      · simp [t, saveMatchingRebaseChildIndex, arithmeticStep, entry, running, zero, Function.iterate_succ_apply']
      · exact running
      · rfl
    have inner := branchOnAtMost_left 27 15 saveMatchingRebaseChildIndex [] entry running equal.ge remember running
    have run := branchOnAtMost_left 15 27 (branchOnAtMost 27 15 saveMatchingRebaseChildIndex []) []
      entry running equal.le inner running
    exact ⟨_, 6, le_rfl, run, running, by simp [t, chosen, equal], by simp [t, chosen, equal], rfl, rfl, rfl⟩
  · have run := branchOnAtMost_right 15 27 (branchOnAtMost 27 15 saveMatchingRebaseChildIndex []) []
      entry running after empty running
    exact ⟨_, 1, by decide, run, running, by simp [chosen, after.ne'], by simp [chosen, after.ne'], rfl, rfl, rfl⟩

private theorem considerMatchingRebaseChild_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0) :
    let child := matchingCycleChildAt s.nm (s.nr 18 + 4 * s.nr 7)
    let matchesChild := child.representative = s.nr 27
    ∃ t steps, steps ≤ 16 ∧ BlockRuns considerMatchingRebaseChild steps s t ∧ t.halted = false ∧
      t.nr 46 = (if matchesChild then s.nr 7 else s.nr 46) ∧
      t.nr 47 = (if matchesChild then child.node else s.nr 47) ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 15, 16, 17, 25, 46, 47] → t.nr r = s.nr r := by
  intro child matchesChild
  obtain ⟨a, read, live, values, aNat, aReal, aRR, aRegs⟩ := readMatchingCycleChild_spec s entry running one
  let start := {a with pc := 0}
  obtain ⟨b, steps, bound, choose, bLive, index, node, bNat, bReal, bRR⟩ :=
    selectMatchingRebaseChild_correct (s := start) rfl live ((aRegs 14 (by decide)).trans zero)
  let t := relocateState readMatchingCycleChild.length b
  have composed : BlockRuns considerMatchingRebaseChild (10 + steps) s t := read.append choose
  have atRep : start.nr 15 = child.representative := congrArg MatchingCycleChild.representative values
  have atNode : start.nr 25 = child.node := congrArg MatchingCycleChild.node values
  have keeps (r : ℕ) (safe : r ∉ [0, 6, 15, 16, 17, 25] := by decide) : start.nr r = s.nr r := aRegs r safe
  refine ⟨t, _, by omega, composed, bLive, ?_, ?_, bNat.trans aNat, bReal.trans aReal, bRR.trans aRR, ?_⟩
  · change b.nr 46 = _
    simpa only [atRep, keeps 27, keeps 7, keeps 46, matchesChild] using index
  · change b.nr 47 = _
    simpa only [atRep, keeps 27, atNode, keeps 47, matchesChild] using node
  · intro r safe
    rw [← composed.run]
    exact arithmeticRun_keeps_from_destination_list _ (by decide) safe s _

private structure RebaseChildSearch (s : ArithmeticState) (free index : ℕ) (t : ArithmeticState) : Prop where
  entry : t.pc = 0
  running : t.halted = false
  indexAt : t.nr 7 = index
  wanted : t.nr 27 = s.nm (s.nr 79 + s.nr 29)
  found : t.nr 46 = if free < index then free else s.nr 19
  node : t.nr 47 = if free < index then (matchingCycleChildAt s.nm (s.nr 18 + 4 * free)).node else 0
  memory : t.nm = s.nm
  real : t.rm = s.rm
  realRegs : t.rr = s.rr
  keeps : ∀ r, r ∉ [0, 6, 7, 15, 16, 17, 25, 27, 46, 47] → t.nr r = s.nr r

set_option maxRecDepth 4096 in
private theorem locateMatchingRebaseFreeChild_correct {s : ArithmeticState} (free : ℕ)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (inside : free < s.nr 19)
    (unique : ∀ i < s.nr 19,
      (matchingCycleChildAt s.nm (s.nr 18 + 4 * i)).representative = s.nm (s.nr 79 + s.nr 29) ↔ i = free) :
    ∃ t steps, steps ≤ 19 * s.nr 19 + 6 ∧ BlockRuns locateMatchingRebaseFreeChild steps s t ∧
      t.halted = false ∧ t.nr 46 = free ∧ t.nr 47 = (matchingCycleChildAt s.nm (s.nr 18 + 4 * free)).node ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 7, 15, 16, 17, 25, 27, 46, 47] → t.nr r = s.nr r := by
  let m := s.nr 19
  let wanted := s.nm (s.nr 79 + s.nr 29)
  let freeNode := (matchingCycleChildAt s.nm (s.nr 18 + 4 * free)).node
  let seed := {s with pc := 4, nr := Function.update (Function.update (Function.update (Function.update
    s.nr 6 (s.nr 79 + s.nr 29)) 27 wanted) 46 m) 47 0}
  have setup : BlockRuns startMatchingRebaseChildSearch 4 s seed := by
    apply BlockRuns.of_running_exit
    · simp [seed, m, wanted, startMatchingRebaseChildSearch, arithmeticStep, entry, running, zero,
        Function.iterate_succ_apply']
    · exact running
    · rfl
  let start := {seed with pc := 0}
  let inv := RebaseChildSearch s free
  have init : inv 0 {start with pc := 0, nr := Function.update start.nr 7 0} := by
    refine ⟨rfl, running, by simp, by simp [start, seed, wanted], by simp [start, seed, m],
      by simp [start, seed], rfl, rfl, rfl, ?_⟩
    intro r safe
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at safe
    obtain ⟨_, h6, h7, _, _, _, _, h27, h46, h47⟩ := safe
    simp [start, seed, h6, h7, h27, h46, h47]
  have iterate (i : ℕ) (hi : i < m) (a : ArithmeticState) (ha : inv i a) :
      ∃ t steps, steps ≤ 16 ∧ BlockRuns considerMatchingRebaseChild steps a t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    have oneA := (ha.keeps 9 (by decide)).trans one
    have zeroA := (ha.keeps 14 (by decide)).trans zero
    obtain ⟨t, ticks, cost, body, live, idx, childId, tNat, tReal, tRR, tKeep⟩ :=
      considerMatchingRebaseChild_correct ha.entry ha.running oneA zeroA
    have tIndex := (tKeep 7 (by decide)).trans ha.indexAt
    have tOne := (tKeep 9 (by decide)).trans oneA
    have atChild : matchingCycleChildAt a.nm (a.nr 18 + 4 * a.nr 7) =
        matchingCycleChildAt s.nm (s.nr 18 + 4 * i) := by rw [ha.memory, ha.keeps 18 (by decide), ha.indexAt]
    have hit : (matchingCycleChildAt a.nm (a.nr 18 + 4 * a.nr 7)).representative = a.nr 27 ↔ i = free := by
      rw [atChild, ha.wanted]
      exact unique i hi
    refine ⟨t, ticks, cost, body, live, rfl, live, by simp [tIndex, tOne],
      by simp [tKeep 27 (by decide), ha.wanted], ?_, ?_, tNat.trans ha.memory,
      tReal.trans ha.real, tRR.trans ha.realRegs, ?_⟩
    · change t.nr 46 = _
      by_cases equal : i = free
      · have next : free < i + 1 := by omega
        rw [idx, if_pos (hit.mpr equal), ha.indexAt, if_pos next]
        exact equal
      · have step : free < i + 1 ↔ free < i := by omega
        simp only [idx, if_neg (mt hit.mp equal), ha.found, step]
    · change t.nr 47 = _
      by_cases equal : i = free
      · have next : free < i + 1 := by omega
        rw [childId, if_pos (hit.mpr equal), atChild, if_pos next, equal]
      · have step : free < i + 1 ↔ free < i := by omega
        simp only [childId, if_neg (mt hit.mp equal), ha.node, step]
    · intro r safe
      have original : r ∉ [0, 6, 15, 16, 17, 25, 46, 47] := by simp at safe ⊢; omega
      have notIndex : r ≠ 7 := by simp at safe; omega
      exact (Function.update_of_ne notIndex _ _).trans ((tKeep r original).trans (ha.keeps r safe))
  obtain ⟨last, ticks, checked, cost, run⟩ := countedLoopFromZero_bounded 9 7 19 m 16
    considerMatchingRebaseChild inv (s := start) rfl running init
    (fun _ _ h => ⟨h.entry, h.running, h.indexAt, h.keeps 19 (by decide)⟩) iterate
  have insideM : free < m := inside
  have idx : last.nr 46 = free := by simpa only [if_pos insideM] using checked.found
  have node : last.nr 47 = freeNode := by simpa only [if_pos insideM] using checked.node
  have budget : 4 + ticks ≤ 19 * s.nr 19 + 6 := by dsimp [m] at cost; omega
  exact ⟨_, _, budget, setup.append run, checked.running, idx, node,
    checked.memory, checked.real, checked.realRegs, checked.keeps⟩

private theorem rebaseMatchingPairIteration_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (inside : s.nr 7 < s.nr 19) :
    ∃ t ticks, ticks ≤ 64 ∧ BlockRuns rebaseMatchingPairIteration ticks s t ∧ t.halted = false ∧
      t.nr 7 = (s.nr 7 + 2) % s.nr 19 ∧ t.nr 82 = (rebasedCyclePairState s).nr 82 ∧
      t.nm = (rebasedCyclePairState s).nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 7, 10, 11, 12, 13, 15, 16, 17, 25, 28, 82] → t.nr r = s.nr r := by
  obtain ⟨a, pairTicks, cap, pair, live, index, stack, bytes, real, rr, stays⟩ :=
    rebaseMatchingCyclePairBlock_correct entry running one zero inside
  let start := {a with pc := 0}
  have count : start.nr 19 = s.nr 19 := stays 19 (by decide)
  have nextIndex : start.nr 7 = (s.nr 7 + 1) % s.nr 19 := index
  have within : start.nr 7 < start.nr 19 := by
    rw [count, nextIndex]
    exact Nat.mod_lt _ (by omega)
  obtain ⟨moveTicks, moveCost, move⟩ := advanceMatchingCycleIndexBlock_correct (s := start)
    rfl live ((stays 9 (by decide)).trans one) within
  let b := {start with pc := 3, nr := Function.update start.nr 7 ((start.nr 7 + 1) % start.nr 19)}
  let t := relocateState rebaseMatchingCyclePairBlock.length b
  have run : BlockRuns rebaseMatchingPairIteration (pairTicks + moveTicks) s t := pair.append move
  refine ⟨t, _, by omega, run, live, ?_, ?_, bytes, real, rr, ?_⟩
  · change b.nr 7 = _
    simp only [b, Function.update_self, count, nextIndex, Nat.mod_add_mod, Nat.add_assoc]
  · change b.nr 82 = _
    change Function.update start.nr 7 ((start.nr 7 + 1) % start.nr 19) 82 = _
    rw [Function.update_of_ne (by decide : (82 : ℕ) ≠ 7)]
    exact stack
  · intro r safe
    change b.nr r = _
    have notIndex : r ≠ 7 := by simp at safe; omega
    exact (Function.update_of_ne notIndex _ _).trans (stays r safe)

def rebaseMatchingPairsState (s : ArithmeticState) : ℕ → ArithmeticState
  | 0 => s
  | i + 1 =>
    let previous := rebaseMatchingPairsState s i
    let paired := rebasedCyclePairState previous
    { paired with nr := Function.update paired.nr 7 ((previous.nr 7 + 2) % previous.nr 19) }

private theorem rebasedCyclePairState_agrees {s t : ArithmeticState} (memory : s.nm = t.nm)
    (same : ∀ r ∈ [7, 18, 19, 50, 79, 81, 82], s.nr r = t.nr r) :
    (rebasedCyclePairState s).nm = (rebasedCyclePairState t).nm ∧
      (rebasedCyclePairState s).nr 82 = (rebasedCyclePairState t).nr 82 := by
  have at7 := same 7 (by decide)
  have at18 := same 18 (by decide)
  have at19 := same 19 (by decide)
  have at50 := same 50 (by decide)
  have at79 := same 79 (by decide)
  have at81 := same 81 (by decide)
  have at82 := same 82 (by decide)
  simp only [rebasedCyclePairState, memory, at7, at18, at19, at79]
  let left := matchingCycleChildAt t.nm (t.nr 18 + 4 * t.nr 7)
  let right := matchingCycleChildAt t.nm (t.nr 18 + 4 * ((t.nr 7 + 1) % t.nr 19))
  cases ports : matchingRebasePorts t.nm (t.nr 79) left with
  | mk u v =>
    have value : matchingRebasePorts t.nm (t.nr 79)
        (matchingCycleChildAt t.nm (t.nr 18 + 4 * t.nr 7)) = (u, v) := ports
    simp only [value]
    by_cases lLeaf : left.node = 0 <;> by_cases rLeaf : right.node = 0 <;>
      simp [queuedMatchingRebaseJob, installedRebasedCyclePairMemory, pushedMatchingRebaseJob,
        matchingRebaseJobAddress, left, right, lLeaf, rLeaf, memory, at7, at18, at19, at50, at81, at82]

theorem rebaseMatchingPairsState_get {s : ArithmeticState} (i r : ℕ)
    (safe : r ∉ [7, 12, 13, 28, 82]) : (rebaseMatchingPairsState s i).nr r = s.nr r := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at safe
    obtain ⟨h7, h12, h13, h28, h82⟩ := safe
    have keepsQueued (x : ArithmeticState) (node desired : ℕ) : (queuedMatchingRebaseJob x node desired).nr r = x.nr r := by
      unfold queuedMatchingRebaseJob
      split
      · rfl
      · exact Function.update_of_ne h82 _ _
    let prior := rebaseMatchingPairsState s i
    let left := matchingCycleChildAt prior.nm (prior.nr 18 + 4 * prior.nr 7)
    simp only [rebaseMatchingPairsState, Function.update_of_ne h7]
    change (rebasedCyclePairState prior).nr r = s.nr r
    cases coordinates : matchingRebasePorts prior.nm (prior.nr 79) left with
    | mk u v =>
      have ports : matchingRebasePorts prior.nm (prior.nr 79)
          (matchingCycleChildAt prior.nm (prior.nr 18 + 4 * prior.nr 7)) = (u, v) := coordinates
      simpa only [rebasedCyclePairState, ports, keepsQueued, Function.update_of_ne h7,
        Function.update_of_ne h12, Function.update_of_ne h13, Function.update_of_ne h28] using ih

theorem rebaseMatchingPairsState_index (s : ArithmeticState) (i : ℕ) (inside : s.nr 7 < s.nr 19) :
    (rebaseMatchingPairsState s i).nr 7 = (s.nr 7 + 2 * i) % s.nr 19 := by
  induction i with
  | zero => simpa only [rebaseMatchingPairsState, Nat.mul_zero, Nat.add_zero] using
      (Nat.mod_eq_of_lt inside).symm
  | succ i ih =>
    have length := rebaseMatchingPairsState_get (s := s) i 19 (by decide)
    simp only [rebaseMatchingPairsState, Function.update_self, length, ih, Nat.mod_add_mod, Nat.mul_succ, Nat.add_assoc]



private theorem cycleIndex_wrap_once {length base offset : ℕ} (hb : base < length) (ho : offset < length) :
    (base + offset) % length = if base + offset < length then base + offset else base + offset - length := by
  by_cases nowrap : base + offset < length
  · rw [if_pos nowrap, Nat.mod_eq_of_lt nowrap]
  · have wrap : length ≤ base + offset := by omega
    have reduced : base + offset - length < length := by omega
    rw [if_neg nowrap, Nat.mod_eq_sub_mod wrap, Nat.mod_eq_of_lt reduced]

private theorem cycleIndex_translate_injective {length base x y : ℕ} (hb : base < length)
    (hx : x < length) (hy : y < length) (same : (base + x) % length = (base + y) % length) : x = y := by
  rw [cycleIndex_wrap_once hb hx, cycleIndex_wrap_once hb hy] at same
  split at same <;> split at same <;> omega

/-- Pair iteration visits each child other than the new free child exactly once. -/
theorem matchingRebaseChildIndex_complete {length free : ℕ} (inside : free < length) (odd : Odd length) :
    (∀ pair < (length - 1) / 2, ∀ second : Bool,
      matchingRebaseChildIndex length free pair second < length ∧
        matchingRebaseChildIndex length free pair second ≠ free) ∧
    (∀ child < length, child ≠ free → ∃ pair < (length - 1) / 2, ∃ second : Bool,
      matchingRebaseChildIndex length free pair second = child) ∧
    (∀ pair₁ < (length - 1) / 2, ∀ pair₂ < (length - 1) / 2, ∀ second₁ second₂ : Bool,
      matchingRebaseChildIndex length free pair₁ second₁ = matchingRebaseChildIndex length free pair₂ second₂ →
        pair₁ = pair₂ ∧ second₁ = second₂) := by
  have positive : 0 < length := by omega
  have pairs : 2 * ((length - 1) / 2) + 1 = length := by
    obtain ⟨n, lengthDef⟩ := odd
    omega
  have bounds (i : ℕ) (hi : i < (length - 1) / 2) (second : Bool) :
      0 < 2 * i + (if second then 2 else 1) ∧ 2 * i + (if second then 2 else 1) < length := by
    cases second <;> simp <;> omega
  refine ⟨?_, ?_, ?_⟩
  · intro i hi second
    refine ⟨Nat.mod_lt _ positive, ?_⟩
    intro repeated
    have same : (free + (2 * i + (if second then 2 else 1))) % length = (free + 0) % length := by
      simpa [matchingRebaseChildIndex, Nat.mod_eq_of_lt inside] using repeated
    have sizes := bounds i hi second
    have offsetZero := cycleIndex_translate_injective inside sizes.2 positive same
    omega
  · intro child hc other
    let offset := if free ≤ child then child - free else length - (free - child)
    have range : 0 < offset ∧ offset < length := by
      dsimp only [offset]
      split <;> omega
    have rotation : (free + offset) % length = child := by
      rw [cycleIndex_wrap_once inside range.2]
      by_cases order : free ≤ child
      · have address : free + offset = child := by simp [offset, order] <;> omega
        rw [address, if_pos hc]
      · have address : free + offset = length + child := by simp [offset, order] <;> omega
        rw [address, if_neg (by omega : ¬length + child < length)]
        omega
    by_cases evenOffset : offset % 2 = 0
    · let i := (offset - 2) / 2
      have inverse : 2 * i + 2 = offset := by dsimp [i]; omega
      refine ⟨i, by omega, true, ?_⟩
      simpa [matchingRebaseChildIndex, inverse] using rotation
    · let i := (offset - 1) / 2
      have inverse : 2 * i + 1 = offset := by dsimp [i]; omega
      refine ⟨i, by omega, false, ?_⟩
      simpa [matchingRebaseChildIndex, inverse] using rotation
  · intro i hi j hj x y same
    have equal := cycleIndex_translate_injective inside (bounds i hi x).2 (bounds j hj y).2 same
    cases x <;> cases y <;> simp at equal ⊢ <;> omega

/-- The indices read by the RAM pair pass are the two indices in the abstract cycle order. -/
theorem rebaseMatchingPairsState_childIndices {s : ArithmeticState} {free : ℕ} (i : ℕ)
    (inside : free < s.nr 19) (start : s.nr 7 = (free + 1) % s.nr 19) :
    let cursor := (rebaseMatchingPairsState s i).nr 7
    cursor = matchingRebaseChildIndex (s.nr 19) free i false ∧
      (cursor + 1) % s.nr 19 = matchingRebaseChildIndex (s.nr 19) free i true := by
  have startInside : s.nr 7 < s.nr 19 := by rw [start]; exact Nat.mod_lt _ (by omega)
  have first := rebaseMatchingPairsState_index s i startInside
  dsimp only
  constructor <;> simp [first, start, Nat.mod_add_mod, matchingRebaseChildIndex] <;> congr 1 <;> omega

private structure RebasePairScan (s : ArithmeticState) (i : ℕ) (t : ArithmeticState) : Prop where
  entry : t.pc = 0
  running : t.halted = false
  indexAt : t.nr 24 = i
  position : t.nr 7 = (rebaseMatchingPairsState s i).nr 7
  inside : t.nr 7 < s.nr 19
  queued : t.nr 82 = (rebaseMatchingPairsState s i).nr 82
  memory : t.nm = (rebaseMatchingPairsState s i).nm
  real : t.rm = s.rm
  realRegs : t.rr = s.rr
  kept : ∀ r, r ∉ [0, 6, 7, 10, 11, 12, 13, 15, 16, 17, 24, 25, 28, 82] → t.nr r = s.nr r

set_option maxRecDepth 4096 in
private theorem rebaseMatchingPairLoop_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (inside : s.nr 7 < s.nr 19) :
    let final := rebaseMatchingPairsState s (s.nr 95)
    ∃ t steps, steps ≤ 67 * s.nr 95 + 2 ∧ BlockRuns rebaseMatchingPairLoop steps s t ∧ t.halted = false ∧
      t.nr 7 = final.nr 7 ∧ t.nr 82 = final.nr 82 ∧ t.nm = final.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 7, 10, 11, 12, 13, 15, 16, 17, 24, 25, 28, 82] → t.nr r = s.nr r := by
  intro final
  let inv := RebasePairScan s
  have init : inv 0 {s with pc := 0, nr := Function.update s.nr 24 0} := by
    refine ⟨rfl, running, by simp, by simp [rebaseMatchingPairsState], by simpa using inside,
      by simp [rebaseMatchingPairsState], rfl, rfl, rfl, ?_⟩
    intro r safe
    have away : r ≠ 24 := by simp at safe; omega
    exact Function.update_of_ne away _ _
  have iteration (i : ℕ) (_ : i < s.nr 95) (a : ArithmeticState) (ha : inv i a) :
      ∃ t ticks, ticks ≤ 64 ∧ BlockRuns rebaseMatchingPairIteration ticks a t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)} := by
    let model := rebaseMatchingPairsState s i
    have aOne := (ha.kept 9 (by decide)).trans one
    have aZero := (ha.kept 14 (by decide)).trans zero
    have count := ha.kept 19 (by decide)
    obtain ⟨t, ticks, cost, run, live, position, jobs, bytes, real, rr, fixed⟩ :=
      rebaseMatchingPairIteration_correct ha.entry ha.running aOne aZero (count.symm ▸ ha.inside)
    have agree : ∀ r ∈ [7, 18, 19, 50, 79, 81, 82], a.nr r = model.nr r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ha.position
      · exact (ha.kept 18 (by decide)).trans (rebaseMatchingPairsState_get i 18 (by decide)).symm
      · exact count.trans (rebaseMatchingPairsState_get i 19 (by decide)).symm
      · exact (ha.kept 50 (by decide)).trans (rebaseMatchingPairsState_get i 50 (by decide)).symm
      · exact (ha.kept 79 (by decide)).trans (rebaseMatchingPairsState_get i 79 (by decide)).symm
      · exact (ha.kept 81 (by decide)).trans (rebaseMatchingPairsState_get i 81 (by decide)).symm
      · exact ha.queued
    have updates := rebasedCyclePairState_agrees ha.memory agree
    refine ⟨t, ticks, cost, run, live, rfl, live, ?_, ?_, ?_, ?_, ?_, real.trans ha.real, rr.trans ha.realRegs, ?_⟩
    · simp [fixed 24 (by decide), fixed 9 (by decide), ha.indexAt, aOne]
    · change t.nr 7 = _
      rw [position, agree 7 (by decide), agree 19 (by decide)]
      simp only [model, rebaseMatchingPairsState, Function.update_self]
    · change t.nr 7 < s.nr 19
      rw [position, count]
      exact Nat.mod_lt _ (by have := ha.inside; omega)
    · change t.nr 82 = _
      rw [jobs, updates.2]
      rfl
    · exact bytes.trans updates.1
    · intro r safe
      have noIndex : r ≠ 24 := by simp at safe; omega
      have keep : r ∉ [0, 6, 7, 10, 11, 12, 13, 15, 16, 17, 25, 28, 82] := by simp at safe ⊢; omega
      exact (Function.update_of_ne noIndex _ _).trans ((fixed r keep).trans (ha.kept r safe))
  obtain ⟨last, steps, done, budget, loop⟩ := countedLoopFromZero_bounded 9 24 95 (s.nr 95) 64
    rebaseMatchingPairIteration inv entry running init
    (fun _ _ h => ⟨h.entry, h.running, h.indexAt, h.kept 95 (by decide)⟩) iteration
  exact ⟨_, steps, by omega, loop, done.running, done.position, done.queued, done.memory,
    done.real, done.realRegs, done.kept⟩

private theorem rebaseMatchingPairsState_agrees {s t : ArithmeticState} (i : ℕ) (memory : s.nm = t.nm)
    (same : ∀ r ∈ [7, 18, 19, 50, 79, 81, 82], s.nr r = t.nr r) :
    (rebaseMatchingPairsState s i).nm = (rebaseMatchingPairsState t i).nm ∧
    ∀ r ∈ [7, 18, 19, 50, 79, 81, 82],
      (rebaseMatchingPairsState s i).nr r = (rebaseMatchingPairsState t i).nr r := by
  induction i with
  | zero => exact ⟨memory, same⟩
  | succ i ih =>
    have paired := rebasedCyclePairState_agrees ih.1 ih.2
    refine ⟨paired.1, ?_⟩
    intro r hr
    by_cases position : r = 7
    · subst r
      simp only [rebaseMatchingPairsState, Function.update_self, ih.2 7 (by decide), ih.2 19 (by decide)]
    by_cases count : r = 82
    · subst r
      exact paired.2
    have away : r ∉ [7, 12, 13, 28, 82] := by simp at hr ⊢; omega
    exact (rebaseMatchingPairsState_get (i + 1) r away).trans
      ((same r hr).trans (rebaseMatchingPairsState_get (i + 1) r away).symm)

set_option maxRecDepth 4096 in
private theorem rebaseMatchingPairedChildren_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (zeroForHalving : s.nr 23 = 0) (inside : s.nr 7 < s.nr 19) (odd : Odd (s.nr 19))
    (lengthBound : s.nr 19 ≤ s.nr 55) :
    let pairs := (s.nr 19 - 1) / 2
    let model := rebaseMatchingPairsState s pairs
    ∃ t ticks, ticks ≤ 41 * s.nr 55 + 8 ∧
      BlockRuns rebaseMatchingPairedChildren ticks s t ∧ t.halted = false ∧
      t.nr 7 = model.nr 7 ∧ t.nr 82 = model.nr 82 ∧ t.nm = model.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 7, 10, 11, 12, 13, 15, 16, 17, 24, 25, 28, 46, 47, 49, 82, 95] → t.nr r = s.nr r := by
  intro pairs model
  let seed := {s with pc := 1, nr := Function.update s.nr 46 (s.nr 19 - 1)}
  have seedRun : BlockRuns [.natSub 46 19 9] 1 s seed := by
    apply BlockRuns.of_running_exit
    · simp [seed, arithmeticStep, entry, running, one]
    · exact running
    · rfl
  let a := {seed with pc := 0}
  have aKeep (r : ℕ) (safe : r ≠ 46 := by decide) : a.nr r = s.nr r := by simp [a, seed, safe]
  obtain ⟨b, halveTicks, halveCost, halve, live, balance, residual, bNat, bReal, bRR, bKeep⟩ :=
    halveExpansionDistance_spec a rfl running ((aKeep 9).trans one) ((aKeep 23).trans zeroForHalving)
      (by rw [aKeep 55]; change s.nr 19 - 1 ≤ s.nr 55; omega)
  let bInput := {relocateState 1 b with pc := 0}
  have bAt (r : ℕ) (safe : r ∉ [0, 24, 47, 49, 95] := by decide) (away : r ≠ 46 := by decide) :
      bInput.nr r = s.nr r := (bKeep r safe).trans (aKeep r away)
  have encoding : bInput.nr 95 = pairs := by
    obtain ⟨k, oddLength⟩ := odd
    change b.nr 47 + 2 * b.nr 95 = s.nr 19 - 1 at balance
    change b.nr 95 = (s.nr 19 - 1) / 2
    omega
  obtain ⟨t, scanTicks, scanCost, scan, tLive, index, jobs, bytes, tReal, tRR, tKeep⟩ :=
    rebaseMatchingPairLoop_correct (s := bInput) rfl live ((bAt 9).trans one) ((bAt 14).trans zero)
      (by rwa [bAt 7, bAt 19])
  have memory : bInput.nm = s.nm := bNat
  have agree : ∀ r ∈ [7, 18, 19, 50, 79, 81, 82], bInput.nr r = s.nr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact bAt _ (by decide) (by decide)
  have models := rebaseMatchingPairsState_agrees pairs memory agree
  have composed := (seedRun.append halve).append scan
  rw [encoding] at scanCost index jobs bytes
  rw [aKeep 55] at halveCost
  have evenLength : 2 * pairs = s.nr 19 - 1 := by
    obtain ⟨k, oddLength⟩ := odd
    dsimp [pairs]
    omega
  refine ⟨_, _, by omega, composed, tLive, index.trans (models.2 7 (by decide)),
    jobs.trans (models.2 82 (by decide)), bytes.trans models.1, tReal.trans bReal, tRR.trans bRR, ?_⟩
  intro r safe
  have notInScan : r ∉ [0, 6, 7, 10, 11, 12, 13, 15, 16, 17, 24, 25, 28, 82] := by simp at safe ⊢; omega
  have notInHalf : r ∉ [0, 24, 47, 49, 95] := by simp at safe ⊢; omega
  have notInSeed : r ≠ 46 := by simp at safe; omega
  exact (tKeep r notInScan).trans (bAt r notInHalf notInSeed)

/-- Model one full cyclic rematch. Install the exposed original in the free child,
enqueue its node, then process alternate edges beginning just after that child. -/
def rebasedMatchingCycleState (s : ArithmeticState) (free : ℕ) : ArithmeticState :=
  let address := s.nr 18 + 4 * free
  let node := (matchingCycleChildAt s.nm address).node
  let seeded := {s with
    nr := Function.update s.nr 7 ((free + 1) % s.nr 19)
    nm := Function.update s.nm address (s.nr 29) }
  rebaseMatchingPairsState (queuedMatchingRebaseJob seeded node (s.nr 29)) ((s.nr 19 - 1) / 2)

set_option maxRecDepth 4096 in
theorem rebaseMatchingCycleBlock_correct {s : ArithmeticState} (free : ℕ)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (zeroForHalving : s.nr 23 = 0) (inside : free < s.nr 19) (odd : Odd (s.nr 19))
    (lengthBound : s.nr 19 ≤ s.nr 55)
    (finds : ∀ i < s.nr 19,
      (matchingCycleChildAt s.nm (s.nr 18 + 4 * i)).representative = s.nm (s.nr 79 + s.nr 29) ↔ i = free) :
    let model := rebasedMatchingCycleState s free
    ∃ t ticks, ticks ≤ 60 * s.nr 55 + 29 ∧ BlockRuns rebaseMatchingCycleBlock ticks s t ∧ t.halted = false ∧
      t.nr 7 = model.nr 7 ∧ t.nr 82 = model.nr 82 ∧ t.nm = model.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 7, 10, 11, 12, 13, 15, 16, 17, 24, 25, 27, 28, 46, 47, 49, 82, 95] →
        t.nr r = s.nr r := by
  intro model
  let address := s.nr 18 + 4 * free
  let node := (matchingCycleChildAt s.nm address).node
  let fresh := {s with
    nr := Function.update s.nr 7 ((free + 1) % s.nr 19)
    nm := Function.update s.nm address (s.nr 29)}
  let queued := queuedMatchingRebaseJob fresh node (s.nr 29)
  have finalModel : model = rebaseMatchingPairsState queued ((s.nr 19 - 1) / 2) := rfl
  obtain ⟨a, searchTicks, searchBound, locate, aLive, freeIndex, freeNode, aNat, aReal, aReals, aKeeps⟩ :=
    locateMatchingRebaseFreeChild_correct free entry running one zero inside finds
  let aInput := {a with pc := 0}
  obtain ⟨b, write, bLive, index, bNat, bReal, bReals, bKeeps⟩ :=
    writeMatchingRebaseFreeChildBlock_correct (s := aInput) rfl aLive ((aKeeps 14 (by decide)).trans zero)
  have bSafe (r : ℕ) (safe : r ∉ [0, 6, 7] := by decide)
      (early : r ∉ [0, 6, 7, 15, 16, 17, 25, 27, 46, 47] := by decide) : b.nr r = s.nr r :=
    (bKeeps r safe).trans (aKeeps r early)
  have bNode : b.nr 47 = node := (bKeeps 47 (by decide)).trans freeNode
  have bBytes : b.nm = fresh.nm := by
    rw [bNat]
    change Function.update a.nm (a.nr 18 + 4 * a.nr 46) (a.nr 29) = _
    rw [aNat, aKeeps 18 (by decide), freeIndex, aKeeps 29 (by decide)] <;> rfl
  let bInput := {b with pc := 0}
  obtain ⟨c, pushTicks, pushCost, push, cLive, cCount, cNat, cReal, cReals, cKeeps⟩ :=
    queueMatchingRebaseChildBlock_correct 47 29 (s := bInput) rfl bLive
      ((bSafe 9).trans one) ((bSafe 14).trans zero) (by decide) (by decide)
  have cPosition : c.nr 7 = free := (cKeeps 7 (by decide)).trans (index.trans freeIndex)
  have cSafe (r : ℕ) (safe : r ∉ [0, 6, 82] := by decide)
      (before : r ∉ [0, 6, 7] := by decide)
      (early : r ∉ [0, 6, 7, 15, 16, 17, 25, 27, 46, 47] := by decide) : c.nr r = s.nr r :=
    (cKeeps r safe).trans (bSafe r before early)
  have cBytes : c.nm = queued.nm := by
    rw [cNat, show bInput.nr 47 = node from bNode, show bInput.nr 29 = s.nr 29 from bSafe 29]
    by_cases leaf : node = 0 <;> simp [queued, queuedMatchingRebaseJob, leaf,
      show bInput.nm = fresh.nm from bBytes, pushedMatchingRebaseJob, matchingRebaseJobAddress,
      show bInput.nr 81 = s.nr 81 from bSafe 81, show bInput.nr 82 = s.nr 82 from bSafe 82, fresh]
  have cPending : c.nr 82 = queued.nr 82 := by
    rw [cCount, show bInput.nr 47 = node from bNode, show bInput.nr 82 = s.nr 82 from bSafe 82]
    by_cases leaf : node = 0 <;> simp [queued, queuedMatchingRebaseJob, leaf, fresh]
  let cInput := {c with pc := 0}
  obtain ⟨advanceTicks, advanceCost, advance⟩ := advanceMatchingCycleIndexBlock_correct (s := cInput)
    rfl cLive ((cSafe 9).trans one) (by change c.nr 7 < c.nr 19; rwa [cPosition, cSafe 19])
  let d := {cInput with pc := 3, nr := Function.update cInput.nr 7 ((cInput.nr 7 + 1) % cInput.nr 19)}
  have nextIndex : d.nr 7 = (free + 1) % s.nr 19 := by
    simp [d, cInput, cPosition, cSafe 19]
  have dSafe (r : ℕ) (unmoved : r ≠ 7 := by decide) (safe : r ∉ [0, 6, 82] := by decide)
      (before : r ∉ [0, 6, 7] := by decide)
      (early : r ∉ [0, 6, 7, 15, 16, 17, 25, 27, 46, 47] := by decide) : d.nr r = s.nr r :=
    (Function.update_of_ne unmoved _ _).trans (cSafe r safe before early)
  let dInput := {d with pc := 0}
  have dWithin : dInput.nr 7 < dInput.nr 19 := by
    change d.nr 7 < d.nr 19
    rw [nextIndex, dSafe 19]
    exact Nat.mod_lt _ (by omega)
  have cycleOdd : Odd (dInput.nr 19) := (dSafe 19).symm ▸ odd
  have cycleSmall : dInput.nr 19 ≤ dInput.nr 55 := by
    change d.nr 19 ≤ d.nr 55
    rwa [dSafe 19, dSafe 55]
  obtain ⟨e, pairTicks, pairCost, paired, eLive, eIndex, eCount, eNat, eReal, eReals, eKeeps⟩ :=
    rebaseMatchingPairedChildren_correct (s := dInput) rfl cLive ((dSafe 9).trans one)
      ((dSafe 14).trans zero) ((dSafe 23).trans zeroForHalving) dWithin cycleOdd cycleSmall
  have reg (r : ℕ) (safe : r ∈ [7, 18, 19, 50, 79, 81, 82]) : dInput.nr r = queued.nr r := by
    have held (r : ℕ) (except : r ≠ 82) : queued.nr r = fresh.nr r := by
      unfold queued queuedMatchingRebaseJob
      split <;> simp [Function.update_of_ne except]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at safe
    rcases safe with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [held 7 (by decide), fresh] using nextIndex
    · simpa [held 18 (by decide), fresh] using dSafe 18
    · simpa [held 19 (by decide), fresh] using dSafe 19
    · simpa [held 50 (by decide), fresh] using dSafe 50
    · simpa [held 79 (by decide), fresh] using dSafe 79
    · simpa [held 81 (by decide), fresh] using dSafe 81
    · change Function.update cInput.nr 7 ((cInput.nr 7 + 1) % cInput.nr 19) 82 = _
      rw [Function.update_of_ne (by decide : (82 : ℕ) ≠ 7)]
      exact cPending
  have beforeModel : dInput.nm = queued.nm := cBytes
  have slots := rebaseMatchingPairsState_agrees ((s.nr 19 - 1) / 2) beforeModel reg
  have cycleCount : dInput.nr 19 = s.nr 19 := dSafe 19
  have dimension : dInput.nr 55 = s.nr 55 := dSafe 55
  rw [cycleCount] at eIndex eCount eNat
  rw [dimension] at pairCost
  have run : BlockRuns rebaseMatchingCycleBlock (searchTicks + (5 + (pushTicks + (advanceTicks + pairTicks)))) s _ :=
    locate.append (write.append (push.append (advance.append paired)))
  rw [finalModel]
  refine ⟨_, _, by omega, run, eLive, eIndex.trans (slots.2 7 (by decide)),
    eCount.trans (slots.2 82 (by decide)), eNat.trans slots.1, eReal.trans (cReal.trans (bReal.trans aReal)),
    eReals.trans (cReals.trans (bReals.trans aReals)), ?_⟩
  intro r safe
  have inPairs : r ∉ [0, 6, 7, 10, 11, 12, 13, 15, 16, 17, 24, 25, 28, 46, 47, 49, 82, 95] := by
    simp at safe ⊢
    omega
  exact (eKeeps r inPairs).trans (dSafe r (by simp at safe; omega)
    (by simp at safe ⊢; omega) (by simp at safe ⊢; omega) (by simp at safe ⊢; omega))


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseNodeProof

/-! matching/MatchingRebaseNodeJob.lean -/
section RppSource_MatchingRebaseNodeJob
namespace VehicleRoutingSurvey.Routing

/-- The logical input read from the last pending stack slot by the pop block. -/
def poppedMatchingRebaseState (s : ArithmeticState) : ArithmeticState :=
  let pending := s.nr 82 - 1
  let address := matchingRebaseJobAddress s pending
  {s with pc := 0, nr := Function.update (Function.update (Function.update
    s.nr 82 pending) 22 (s.nm address)) 29 (s.nm (address + 1))}

set_option maxRecDepth 4096 in
/-- Pop one request, walk its descendants, and rematch that node, returning the new
child representatives, mate table, and pending stack in the cyclic rematch model. -/
theorem rebaseMatchingNodeJobBlock_correct {s : ArithmeticState} {children : MatchingMemberTree}
    {free owner : ℕ} (ready : MatchingRebaseCycleInput (poppedMatchingRebaseState s) children free owner)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0) :
    ∃ t steps loaded, steps ≤ 153 * s.nr 55 + 54 ∧ BlockRuns rebaseMatchingNodeJobBlock steps s t ∧
      t.halted = false ∧ MatchingRebaseCycleLoaded (poppedMatchingRebaseState s) loaded children free ∧
      t.nr 7 = (rebasedMatchingCycleState loaded free).nr 7 ∧
      t.nr 82 = (rebasedMatchingCycleState loaded free).nr 82 ∧
      t.nm = (rebasedMatchingCycleState loaded free).nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 7, 10, 11, 12, 13, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27, 28,
        29, 46, 47, 49, 82, 87, 95] → t.nr r = s.nr r := by
  obtain ⟨a, pop, aLive, pending, readNode, readPort, aNat, aReal, aReals, aKeeps⟩ :=
    popMatchingRebaseJobBlock_correct entry running one
  let input := {a with pc := 0}
  let ghost := poppedMatchingRebaseState s
  have aFixed (r : ℕ) (safe : r ∉ [0, 6, 22, 29, 82] := by decide) : input.nr r = s.nr r := aKeeps r safe
  have readSame (r : ℕ) (h0 : r ≠ 0 := by decide) (h6 : r ≠ 6 := by decide) : input.nr r = ghost.nr r := by
    by_cases top : r = 82
    · subst r
      simpa [ghost, poppedMatchingRebaseState] using pending
    by_cases node : r = 22
    · subst r
      simpa [ghost, poppedMatchingRebaseState] using readNode
    by_cases port : r = 29
    · subst r
      simpa [ghost, poppedMatchingRebaseState] using readPort
    have away : r ∉ [0, 6, 22, 29, 82] := by simp [h0, h6, node, port, top]
    simpa [ghost, poppedMatchingRebaseState, node, port, top] using aFixed r away
  have natSame : input.nm = ghost.nm := aNat
  have scratch : outsideMatchingMemberScratch input = outsideMatchingMemberScratch ghost := by
    funext addr
    simp only [outsideMatchingMemberScratch, readSame 55, readSame 79, readSame 80]
  have inputRoot : MatchingMemberRoot input children := by
    refine ⟨?_, ?_, ?_, ?_, ready.members.unique, ?_, ?_⟩
    · simpa only [readSame 22] using ready.members.proper
    · simpa only [natSame, readSame 77, readSame 78, readSame 22] using ready.members.encoded
    · simpa only [scratch, natSame, readSame 77, readSame 78, readSame 22] using ready.members.readable
    · simpa only [natSame, readSame 77, readSame 80, readSame 55, readSame 22] using ready.members.above
    · simpa only [readSame 55] using ready.members.valid
    · simpa only [readSame 79, readSame 80, readSame 55] using ready.members.separated
  have correctInput : MatchingRebaseCycleInput input children free owner := by
    refine ⟨inputRoot, ready.odd, ?_, ready.inside, ?_, ready.uniquely⟩
    · simpa only [readSame 55] using ready.fit
    · simpa only [readSame 29] using ready.desired
  obtain ⟨b, loadTicks, loadCost, load, bLive, view⟩ :=
    loadMatchingRebaseCycleBlock_correct correctInput rfl aLive ((aFixed 9).trans one) ((aFixed 14).trans zero)
  let loaded := {b with pc := 0}
  have loadedView : MatchingRebaseCycleLoaded ghost loaded children free := by
    refine ⟨view.one, view.zero, view.halvingZero, view.inside, view.odd, view.fit,
      view.finds, view.assignments, ?_, ?_, view.real.trans aReal, view.realRegisters.trans aReals, ?_, view.count⟩
    · simpa only [natSame, readSame 77, readSame 22] using view.recordBase
    · intro addr outside
      refine (view.outside addr ?_).trans (congrFun natSame addr)
      rw [scratch]
      exact outside
    · intro r safe
      have h0 : r ≠ 0 := by simp at safe; omega
      have h6 : r ≠ 6 := by simp at safe; omega
      exact (view.registers r safe).trans (readSame r h0 h6)
  obtain ⟨c, pairs, pairCost, rebase, live, index, count, bytes, real, realRegs, cKeeps⟩ :=
    rebaseMatchingCycleBlock_correct (s := loaded) free rfl bLive view.one view.zero view.halvingZero
      view.inside view.odd view.fit view.finds
  have dimInput : input.nr 55 = s.nr 55 := aFixed 55
  have dimLoaded : loaded.nr 55 = s.nr 55 := (view.registers 55 (by decide)).trans dimInput
  rw [dimInput] at loadCost
  rw [dimLoaded] at pairCost
  have run : BlockRuns rebaseMatchingNodeJobBlock (6 + (loadTicks + pairs)) s _ := pop.append (load.append rebase)
  refine ⟨_, _, loaded, by omega, run, live, loadedView, index, count, bytes,
    real.trans (view.real.trans aReal), realRegs.trans (view.realRegisters.trans aReals), ?_⟩
  intro r safe
  exact (cKeeps r (by simp at safe ⊢; omega)).trans ((view.registers r (by simp at safe ⊢; omega)).trans
    (aFixed r (by simp at safe ⊢; omega)))


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseNodeJob

/-! matching/MatchingRebaseQueue.lean -/
section RppSource_MatchingRebaseQueue
namespace VehicleRoutingSurvey.Routing



theorem MatchingMemberTree.registeredNodes_add_arity_le_leaves (tree : MatchingMemberTree)
    (proper : tree.proper) : tree.registeredNodes + tree.arity ≤ tree.leaves.length := by
  induction tree with
  | nil => simp [MatchingMemberTree.registeredNodes, MatchingMemberTree.arity, MatchingMemberTree.leaves]
  | leaf v siblings ih =>
    have holds := ih proper
    simp only [MatchingMemberTree.registeredNodes, MatchingMemberTree.arity, MatchingMemberTree.leaves, List.length_cons]
    omega
  | blossom r id children siblings ihChildren ihSiblings =>
    obtain ⟨_, branching, hc, hs⟩ := proper
    have childBound := ihChildren hc
    have siblingBound := ihSiblings hs
    simp only [MatchingMemberTree.registeredNodes, MatchingMemberTree.arity, MatchingMemberTree.leaves, List.length_append]
    omega







@[simp] theorem matchingRebaseQueueWork_append (left right : List MatchingRebaseTask) :
    matchingRebaseQueueWork (left ++ right) = matchingRebaseQueueWork left + matchingRebaseQueueWork right := by
  simp [matchingRebaseQueueWork]

private theorem matchingRebaseQueueWork_pos {tasks : List MatchingRebaseTask} (pending : tasks ≠ []) :
    0 < matchingRebaseQueueWork tasks := by
  cases tasks with
  | nil => exact (pending rfl).elim
  | cons task tail => simp [matchingRebaseQueueWork, MatchingRebaseTask.work] <;> omega

private theorem matchingRebaseQueue_last (jobs : List MatchingRebaseTask) :
    jobs = [] ∨ ∃ earlier task, jobs = earlier ++ [task] := by
  induction jobs with
  | nil => exact Or.inl rfl
  | cons task rest ih =>
    rcases ih with rfl | ⟨earlier, last, restEq⟩
    · exact Or.inr ⟨[], task, rfl⟩
    · exact Or.inr ⟨task :: earlier, last, congrArg (task :: ·) restEq⟩

/-- The loop counter and instruction pointer are irrelevant to the represented queue. -/
def matchingRebaseQueueSnapshot (s : ArithmeticState) : ArithmeticState :=
  {s with pc := 0, nr := Function.update s.nr 43 0}

private theorem matchingRebaseQueueSnapshot_relocate (s : ArithmeticState) (pc : ℕ) :
    matchingRebaseQueueSnapshot (relocateState pc s) = matchingRebaseQueueSnapshot s := rfl

private theorem matchingRebaseQueueSnapshot_update (s : ArithmeticState) (pc index : ℕ) :
    matchingRebaseQueueSnapshot {s with pc := pc, nr := Function.update s.nr 43 index} =
      matchingRebaseQueueSnapshot s := by simp [matchingRebaseQueueSnapshot]

def matchingRebaseNodeKeeps (input output : ArithmeticState) : Prop :=
  ∀ r, r ∉ [0, 6, 7, 10, 11, 12, 13, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27, 28,
    29, 46, 47, 49, 82, 87, 95] → output.nr r = input.nr r

/-- The semantic obligations for a node are on the verified cyclic rematch model.
The callback specifies which children were queued and the remaining registry state. -/
structure MatchingRebaseQueueInterface (frame : List MatchingRebaseTask → ArithmeticState → Prop) : Prop where
  size : ∀ jobs s, frame jobs (matchingRebaseQueueSnapshot s) → s.nr 82 = jobs.length
  input : ∀ earlier task s, frame (earlier ++ [task]) (matchingRebaseQueueSnapshot s) →
    ∃ free owner, MatchingRebaseCycleInput (poppedMatchingRebaseState s) task.children free owner
  update : ∀ earlier task s loaded t free,
    frame (earlier ++ [task]) (matchingRebaseQueueSnapshot s) →
    MatchingRebaseCycleLoaded (poppedMatchingRebaseState s) loaded task.children free →
    t.nr 82 = (rebasedMatchingCycleState loaded free).nr 82 →
    t.nm = (rebasedMatchingCycleState loaded free).nm → t.rm = s.rm → t.rr = s.rr →
    matchingRebaseNodeKeeps s t →
    ∃ added, matchingRebaseQueueWork added = task.children.registeredNodes ∧
      frame (earlier ++ added) (matchingRebaseQueueSnapshot t)

private structure MatchingRebaseQueueLoopState (original : ArithmeticState)
    (frame : List MatchingRebaseTask → ArithmeticState → Prop) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 43 = i
  fixed : ∀ r, r ≠ 43 → r ∉ [0, 6, 7, 10, 11, 12, 13, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27, 28,
    29, 46, 47, 49, 82, 87, 95] → s.nr r = original.nr r
  real : s.rm = original.rm
  realRegs : s.rr = original.rr
  queue : ∃ jobs, frame jobs (matchingRebaseQueueSnapshot s) ∧
    (jobs ≠ [] → i + matchingRebaseQueueWork jobs ≤ original.nr 55)

set_option maxRecDepth 4096 in
/-- Run the actual guarded work-stack loop. Each processed node replaces its credit
by the work of its proper descendants, so the queue is empty by the final iteration. -/
theorem rebaseMatchingQueuedNodesBlock_correct {s : ArithmeticState} {jobs : List MatchingRebaseTask}
    {frame : List MatchingRebaseTask → ArithmeticState → Prop} (checked : MatchingRebaseQueueInterface frame)
    (ready : frame jobs (matchingRebaseQueueSnapshot s)) (work : matchingRebaseQueueWork jobs ≤ s.nr 55)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0) :
    ∃ t steps, steps ≤ s.nr 55 * (153 * s.nr 55 + 59) + 2 ∧
      BlockRuns rebaseMatchingQueuedNodesBlock steps s t ∧ t.halted = false ∧ t.nr 82 = 0 ∧
      frame [] (matchingRebaseQueueSnapshot t) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ≠ 43 → r ∉ [0, 6, 7, 10, 11, 12, 13, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27, 28,
        29, 46, 47, 49, 82, 87, 95] → t.nr r = s.nr r := by
  let inv := MatchingRebaseQueueLoopState s frame
  let body := branchOnUnequal 82 14 rebaseMatchingNodeJobBlock
  let initializer := {s with pc := 0, nr := Function.update s.nr 43 0}
  have init : inv 0 initializer := by
    refine ⟨rfl, running, by simp [initializer], ?_, rfl, rfl, ⟨jobs, ?_, ?_⟩⟩
    · intro r different _
      exact Function.update_of_ne different _ _
    · simpa only [initializer, matchingRebaseQueueSnapshot_update] using ready
    · intro _
      simpa only [Nat.zero_add] using work
  have iteration (i : ℕ) (_ : i < s.nr 55) (a : ArithmeticState) (ha : inv i a) :
      ∃ t ticks, ticks ≤ 153 * s.nr 55 + 56 ∧ BlockRuns body ticks a t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 43 (t.nr 43 + t.nr 9)} := by
    obtain ⟨pending, holds, fuel⟩ := ha.queue
    have oneA := (ha.fixed 9 (by decide) (by decide)).trans one
    have zeroA := (ha.fixed 14 (by decide) (by decide)).trans zero
    have size := checked.size pending a holds
    rcases matchingRebaseQueue_last pending with empty | ⟨earlier, task, asLast⟩
    · subst pending
      let t := {a with pc := body.length}
      have stopped : a.nr 82 = a.nr 14 := size.trans zeroA.symm
      have skipped : BlockRuns body 2 a t :=
        branchOnUnequal_skip 82 14 rebaseMatchingNodeJobBlock a ha.entry ha.running stopped
      refine ⟨t, 2, by omega, skipped, ha.running, rfl, ha.running, ?_, ?_, ha.real, ha.realRegs, ?_⟩
      · simp [t, ha.index, oneA]
      · intro r away safe
        exact (Function.update_of_ne away _ _).trans (ha.fixed r away safe)
      · refine ⟨[], ?_, fun future => (future rfl).elim⟩
        simpa only [t, matchingRebaseQueueSnapshot, Function.update_idem] using holds
    · subst pending
      obtain ⟨free, owner, next⟩ := checked.input earlier task a holds
      obtain ⟨c, ticks, loaded, bound, run, live, view, _, rebaseCount, rebaseBytes, rebaseReal, rebaseRegs, keeps⟩ :=
        rebaseMatchingNodeJobBlock_correct next ha.entry ha.running oneA zeroA
      obtain ⟨added, amount, newFrame⟩ := checked.update earlier task a loaded c free holds view rebaseCount
        rebaseBytes rebaseReal rebaseRegs keeps
      have enabled : a.nr 82 ≠ a.nr 14 := by simp [size, zeroA]
      let t := relocateState 3 c
      have step : BlockRuns body (2 + ticks) a t :=
        branchOnUnequal_take 82 14 rebaseMatchingNodeJobBlock ha.entry ha.running enabled run
      have dim : a.nr 55 = s.nr 55 := ha.fixed 55 (by decide) (by decide)
      rw [dim] at bound
      refine ⟨t, 2 + ticks, by omega, step, live, rfl, live, ?_, ?_, rebaseReal.trans ha.real,
        rebaseRegs.trans ha.realRegs, ?_⟩
      · simp [t, relocateState, keeps 43 (by decide), keeps 9 (by decide), ha.index, oneA]
      · intro r away safe
        exact (Function.update_of_ne away _ _).trans ((keeps r safe).trans (ha.fixed r away safe))
      · refine ⟨earlier ++ added, ?_, ?_⟩
        · simpa only [matchingRebaseQueueSnapshot_update, t, matchingRebaseQueueSnapshot_relocate] using newFrame
        · intro _
          have before := fuel (by simp)
          simp only [matchingRebaseQueueWork_append, amount] at ⊢
          rw [matchingRebaseQueueWork_append] at before
          have singleton : matchingRebaseQueueWork [task] = 1 + task.children.registeredNodes := by
            simp [matchingRebaseQueueWork, MatchingRebaseTask.work]
          omega
  obtain ⟨last, steps, final, bound, run⟩ := countedLoopFromZero_bounded 9 43 55 (s.nr 55) (153 * s.nr 55 + 56)
    body inv entry running init
    (fun _ _ h => ⟨h.entry, h.running, h.index, h.fixed 55 (by decide) (by decide)⟩) iteration
  obtain ⟨pending, lastFrame, fuel⟩ := final.queue
  have done : pending = [] := by
    by_contra nonempty
    have positive := matchingRebaseQueueWork_pos nonempty
    have stop := fuel nonempty
    omega
  subst pending
  have empty := checked.size [] last lastFrame
  have budget : steps ≤ s.nr 55 * (153 * s.nr 55 + 59) + 2 := by
    rw [show 153 * s.nr 55 + 56 + 3 = 153 * s.nr 55 + 59 by omega] at bound
    omega
  refine ⟨_, steps, budget, run, final.running, empty, ?_, final.real, final.realRegs, final.fixed⟩
  simpa only [relocateState, matchingRebaseQueueSnapshot] using lastFrame


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseQueue

/-! matching/MatchingRebaseTaskBounds.lean -/
section RppSource_MatchingRebaseTaskBounds
namespace VehicleRoutingSurvey.Routing

/-- A rebasing request selects one registered top-level subtree and chooses
an original vertex in that subtree as its exposed port. -/
def MatchingRebaseTask.fromTopJob (task : MatchingRebaseTask) (job : MatchingMemberJob) : Prop :=
  task.node = job.node ∧ job.children = some task.children ∧ task.port ∈ task.children.leaves







theorem matchingRebaseQueueWork_perm {first second : List MatchingRebaseTask} (perm : first.Perm second) :
    matchingRebaseQueueWork first = matchingRebaseQueueWork second :=
  (perm.map MatchingRebaseTask.work).sum_nat

theorem MatchingRebaseTask.work_add_one_le_leaves (task : MatchingRebaseTask)
    (proper : (MatchingMemberTree.blossom 0 task.node task.children .nil).proper) :
    task.work + 1 ≤ task.children.leaves.length := by
  have bound := task.children.registeredNodes_add_arity_le_leaves proper.2.2.1
  have branching := proper.2.1
  unfold MatchingRebaseTask.work
  omega

theorem matchingRebaseQueueWork_le_leaves (tasks : List MatchingRebaseTask)
    (proper : ∀ task ∈ tasks, (MatchingMemberTree.blossom 0 task.node task.children .nil).proper) :
    matchingRebaseQueueWork tasks ≤ (matchingRebaseTaskLeaves tasks).length := by
  induction tasks with
  | nil => rfl
  | cons task tail ih =>
    have first := task.work_add_one_le_leaves (proper task (by simp))
    have rest := ih (fun r here => proper r (List.mem_cons_of_mem _ here))
    simp only [matchingRebaseQueueWork, matchingRebaseTaskLeaves, List.map_cons, List.sum_cons,
      List.flatMap_cons, List.length_append] at rest ⊢
    omega

private theorem matchingRebaseTaskLeaves_eq_frontier {tasks : List MatchingRebaseTask}
    {sources : List MatchingMemberJob} (paired : List.Forall₂ MatchingRebaseTask.fromTopJob tasks sources) :
    matchingRebaseTaskLeaves tasks = (MatchingMemberJob.frontier sources).map Prod.fst := by
  induction paired with
  | nil => rfl
  | @cons task job tasks sources pair tail ih =>
    obtain ⟨_, children, _⟩ := pair
    change task.children.leaves ++ matchingRebaseTaskLeaves tasks =
      (job.assignments ++ MatchingMemberJob.frontier sources).map Prod.fst
    rw [List.map_append, ← ih]
    simp [MatchingMemberJob.assignments, children, List.map_map, Function.comp_def]

theorem matchingRebaseTaskLeaves_subperm {tasks : List MatchingRebaseTask} {sources : List MatchingMemberJob}
    {top : MatchingMemberTree} {owner : Option ℕ}
    (paired : List.Forall₂ MatchingRebaseTask.fromTopJob tasks sources)
    (selected : List.Subperm sources (top.jobs owner)) :
    List.Subperm (matchingRebaseTaskLeaves tasks) top.leaves := by
  obtain ⟨ordered, reorders, sublist⟩ := List.subperm_iff.mp selected
  have permuted := (reorders.flatMap_right MatchingMemberJob.assignments).map Prod.fst
  have included := (sublist.flatMap MatchingMemberJob.assignments).map Prod.fst
  refine List.subperm_iff.mpr ⟨(MatchingMemberJob.frontier ordered).map Prod.fst, ?_, ?_⟩
  · rw [← top.jobs_frontier_vertices owner]
    exact permuted
  · rw [matchingRebaseTaskLeaves_eq_frontier paired]
    exact included



private theorem boundedDistinctLeaves {leaves : List ℕ} {k : ℕ}
    (distinct : leaves.Nodup) (finite : ∀ v ∈ leaves, v < k) : leaves.length ≤ k := by
  have subset : leaves.toFinset ⊆ Finset.range k := by
    intro v belongs
    exact Finset.mem_range.mpr (finite v (List.mem_toFinset.mp belongs))
  simpa only [List.toFinset_card_of_nodup distinct, Finset.card_range] using Finset.card_le_card subset







private theorem matchingRebaseQueue_length_le_work (tasks : List MatchingRebaseTask) :
    tasks.length ≤ matchingRebaseQueueWork tasks := by
  induction tasks with
  | nil => rfl
  | cons task rest ih =>
    simp only [List.length_cons, matchingRebaseQueueWork, List.map_cons, List.sum_cons,
      MatchingRebaseTask.work] at ih ⊢
    omega

/-- Replacing the top request by one slot per child fits in the original
vertex dimension, even before the singleton children are discarded. -/
theorem matchingRebaseQueue_arity_capacity {earlier : List MatchingRebaseTask} {task : MatchingRebaseTask}
    {k : ℕ} (proper : ∀ t ∈ earlier ++ [task], (MatchingMemberTree.blossom 0 t.node t.children .nil).proper)
    (distinct : (matchingRebaseTaskLeaves (earlier ++ [task])).Nodup)
    (valid : ∀ v ∈ matchingRebaseTaskLeaves (earlier ++ [task]), v < k) :
    earlier.length + task.children.arity ≤ k := by
  have earlierWork := matchingRebaseQueueWork_le_leaves earlier
    (fun t found => proper t (List.mem_append_left _ found))
  change matchingRebaseQueueWork earlier ≤ (earlier.flatMap fun t => t.children.leaves).length at earlierWork
  have earlierSize := matchingRebaseQueue_length_le_work earlier
  have child := task.children.registeredNodes_add_arity_le_leaves (proper task (by simp)).2.2.1
  have total := boundedDistinctLeaves distinct valid
  simp only [matchingRebaseTaskLeaves, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.length_append] at total
  omega

end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseTaskBounds

/-! matching/MatchingRebaseFrontier.lean -/
section RppSource_MatchingRebaseFrontier
namespace VehicleRoutingSurvey.Routing





theorem MatchingMemberTree.jobs_registryIds (tree : MatchingMemberTree) (owner : Option ℕ) :
    ((tree.jobs owner).flatMap fun job => job.tree.registryIds) = tree.registryIds := by
  induction tree with
  | nil => rfl
  | leaf v rest ih => simpa [MatchingMemberTree.jobs, MatchingMemberJob.tree, MatchingMemberTree.registryIds] using ih
  | blossom r n child rest _ ih =>
    simp [MatchingMemberTree.jobs, MatchingMemberJob.tree, MatchingMemberTree.registryIds]
    exact ih

private theorem matchingRebaseQueueIds_sources {tasks : List MatchingRebaseTask} {sources : List MatchingMemberJob}
    (paired : List.Forall₂ MatchingRebaseTask.fromTopJob tasks sources) :
    matchingRebaseQueueIds tasks = sources.flatMap (fun j => j.tree.registryIds) := by
  induction paired with
  | nil => rfl
  | @cons t j ts js fromJob _ ih =>
    change t.registryIds ++ matchingRebaseQueueIds ts = j.tree.registryIds ++ _
    rw [ih]
    change t.registryIds ++ js.flatMap (fun j => j.tree.registryIds) =
      j.tree.registryIds ++ js.flatMap (fun j => j.tree.registryIds)
    apply congrArg (· ++ js.flatMap (fun j => j.tree.registryIds))
    obtain ⟨id, kind, _⟩ := fromJob
    simp [MatchingRebaseTask.registryIds, MatchingMemberJob.tree, kind, MatchingMemberTree.registryIds, id]

/-- Separate live registry IDs stay separate when the rematch pushes its
registered children and retires the processed task from the frontier. -/
theorem matchingRebaseQueueIds_subperm {tasks : List MatchingRebaseTask} {sources : List MatchingMemberJob}
    {tree : MatchingMemberTree} (paired : List.Forall₂ MatchingRebaseTask.fromTopJob tasks sources)
    (selection : sources.Subperm (tree.jobs none)) : (matchingRebaseQueueIds tasks).Subperm tree.registryIds := by
  obtain ⟨ordered, reorders, sublist⟩ := List.subperm_iff.mp selection
  refine List.subperm_iff.mpr ⟨ordered.flatMap (fun j => j.tree.registryIds), ?_, ?_⟩
  · rw [← tree.jobs_registryIds none]
    exact reorders.flatMap_right _
  · rw [matchingRebaseQueueIds_sources paired]
    exact sublist.flatMap _

private theorem subperm_nodup {α : Type*} {new old : List α} (sub : new.Subperm old) (unique : old.Nodup) :
    new.Nodup := by
  obtain ⟨ordered, permuted, included⟩ := List.subperm_iff.mp sub
  exact included.nodup (permuted.nodup_iff.mpr unique)

theorem matchingRebaseFrontier_replace {earlier added : List MatchingRebaseTask} {task : MatchingRebaseTask}
    {sources : List MatchingMemberJob} (paired : List.Forall₂ MatchingRebaseTask.fromTopJob added sources)
    (select : sources.Subperm (task.children.jobs none))
    (leaves : (matchingRebaseTaskLeaves (earlier ++ [task])).Nodup)
    (ids : (matchingRebaseQueueIds (earlier ++ [task])).Nodup) :
    (matchingRebaseTaskLeaves (earlier ++ added)).Nodup ∧ (matchingRebaseQueueIds (earlier ++ added)).Nodup ∧
      task.node ∉ matchingRebaseQueueIds (earlier ++ added) ∧
      (∀ n ∈ matchingRebaseQueueIds (earlier ++ added), n ∈ matchingRebaseQueueIds (earlier ++ [task])) ∧
      (∀ v ∈ matchingRebaseTaskLeaves (earlier ++ added), v ∈ matchingRebaseTaskLeaves (earlier ++ [task])) := by
  have idsSub := matchingRebaseQueueIds_subperm paired select
  have leavesSub := matchingRebaseTaskLeaves_subperm paired select
  simp only [matchingRebaseQueueIds, matchingRebaseTaskLeaves, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, MatchingRebaseTask.registryIds] at ids leaves ⊢
  have restIds := List.nodup_append.mp ids
  have restLeaves := List.nodup_append.mp leaves
  have child := List.nodup_cons.mp restIds.2.1
  refine ⟨List.nodup_append.mpr ⟨restLeaves.1, subperm_nodup leavesSub restLeaves.2.1, ?_⟩,
    List.nodup_append.mpr ⟨restIds.1, subperm_nodup idsSub child.2, ?_⟩, ?_, ?_, ?_⟩
  · intro x hx y hy
    exact restLeaves.2.2 x hx y (leavesSub.subset hy)
  · intro x hx y hy
    exact restIds.2.2 x hx y (List.mem_cons_of_mem _ (idsSub.subset hy))
  · intro member
    rcases List.mem_append.mp member with old | descendant
    · exact restIds.2.2 task.node old task.node (by simp) rfl
    · exact child.1 (idsSub.subset descendant)
  · intro n member
    rcases List.mem_append.mp member with old | descendant
    · exact List.mem_append_left _ old
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (idsSub.subset descendant))
  · intro v member
    rcases List.mem_append.mp member with old | descendant
    · exact List.mem_append_left _ old
    · exact List.mem_append_right _ (leavesSub.subset descendant)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseFrontier

/-! matching/MatchingRebaseQueueMemory.lean -/
section RppSource_MatchingRebaseQueueMemory
namespace VehicleRoutingSurvey.Routing



theorem MatchingRebaseQueueEncoding.transport {s t : ArithmeticState} {tasks : List MatchingRebaseTask}
    (encoding : MatchingRebaseQueueEncoding s tasks) (base : t.nr 81 = s.nr 81) (count : t.nr 82 = s.nr 82)
    (bytes : ∀ a, s.nr 81 ≤ a → a < s.nr 81 + 2 * tasks.length → t.nm a = s.nm a) :
    MatchingRebaseQueueEncoding t tasks := by
  refine ⟨count.trans encoding.count, ?_⟩
  intro i inside
  have asAddress : matchingRebaseJobAddress t i = matchingRebaseJobAddress s i := by simp [matchingRebaseJobAddress, base]
  rw [asAddress]
  have lower : s.nr 81 ≤ matchingRebaseJobAddress s i := by simp [matchingRebaseJobAddress]
  have upper : matchingRebaseJobAddress s i + 1 < s.nr 81 + 2 * tasks.length := by
    unfold matchingRebaseJobAddress
    omega
  rw [bytes _ lower (by omega), bytes _ (by omega) upper]
  exact encoding.words i inside

theorem MatchingRebaseQueueEncoding.pop {s : ArithmeticState} {earlier : List MatchingRebaseTask}
    {task : MatchingRebaseTask} (encoding : MatchingRebaseQueueEncoding s (earlier ++ [task])) :
    MatchingRebaseQueueEncoding (poppedMatchingRebaseState s) earlier ∧
      (poppedMatchingRebaseState s).nr 22 = task.node ∧ (poppedMatchingRebaseState s).nr 29 = task.port := by
  have index : s.nr 82 - 1 = earlier.length := by simp [encoding.count]
  have atTop := encoding.words earlier.length (by simp)
  rw [List.getElem_append_right (Nat.le_refl _)] at atTop
  simp only [Nat.sub_self, List.getElem_cons_zero] at atTop
  refine ⟨⟨by simp [poppedMatchingRebaseState, index], ?_⟩, ?_, ?_⟩
  · intro i inside
    have row := encoding.words i (by simp only [List.length_append, List.length_singleton]; omega)
    rw [List.getElem_append_left inside] at row
    simpa [poppedMatchingRebaseState, matchingRebaseJobAddress] using row
  · simpa [poppedMatchingRebaseState, index] using congrArg Prod.fst atTop
  · simpa [poppedMatchingRebaseState, index] using congrArg Prod.snd atTop

theorem MatchingRebaseQueueEncoding.push {s : ArithmeticState} {tasks : List MatchingRebaseTask}
    (encoding : MatchingRebaseQueueEncoding s tasks) (task : MatchingRebaseTask) (registered : task.node ≠ 0) :
    MatchingRebaseQueueEncoding (queuedMatchingRebaseJob s task.node task.port) (tasks ++ [task]) := by
  let t := queuedMatchingRebaseJob s task.node task.port
  let top := matchingRebaseJobAddress s tasks.length
  have tBase : t.nr 81 = s.nr 81 := by simp [t, queuedMatchingRebaseJob, registered]
  have newWords : t.nm = Function.update (Function.update s.nm top task.node) (top + 1) task.port := by
    simp [t, queuedMatchingRebaseJob, registered, pushedMatchingRebaseJob, encoding.count, top]
  refine ⟨by simp [t, queuedMatchingRebaseJob, registered, encoding.count], ?_⟩
  intro i within
  have location : matchingRebaseJobAddress t i = matchingRebaseJobAddress s i := by simp [matchingRebaseJobAddress, tBase]
  rcases Nat.lt_or_ge i tasks.length with before | last
  · have first : matchingRebaseJobAddress s i + 1 < top := by dsimp [top, matchingRebaseJobAddress]; omega
    rw [location, List.getElem_append_left before, newWords]
    have x₀ : matchingRebaseJobAddress s i ≠ top := by omega
    have x₁ : matchingRebaseJobAddress s i ≠ top + 1 := by omega
    have y₀ : matchingRebaseJobAddress s i + 1 ≠ top := by omega
    have y₁ : matchingRebaseJobAddress s i + 1 ≠ top + 1 := by omega
    simpa only [Function.update_of_ne x₀, Function.update_of_ne x₁, Function.update_of_ne y₀,
      Function.update_of_ne y₁] using (show _ = _ from encoding.words i before)
  · have bound : i = tasks.length := by simp only [List.length_append, List.length_singleton] at within; omega
    subst i
    rw [location, List.getElem_append_right (Nat.le_refl _), newWords]
    change (Function.update (Function.update s.nm top task.node) (top + 1) task.port top,
      Function.update (Function.update s.nm top task.node) (top + 1) task.port (top + 1)) = _
    simp [Function.update_of_ne (show top ≠ top + 1 by omega)]

/-- Attach the chosen port to an immediate child when it owns a registered subtree. -/
def MatchingMemberJob.rebaseTask (choosePort : MatchingMemberJob → ℕ) (child : MatchingMemberJob) :
    Option MatchingRebaseTask :=
  child.children.map fun children => ⟨child.node, choosePort child, children⟩

theorem MatchingMemberTree.rebaseTasks_work (tree : MatchingMemberTree) (choosePort : MatchingMemberJob → ℕ) :
    matchingRebaseQueueWork ((tree.jobs none).filterMap (MatchingMemberJob.rebaseTask choosePort)) =
      tree.registeredNodes := by
  induction tree with
  | nil => rfl
  | leaf v siblings ih => simpa only [MatchingMemberTree.jobs, List.filterMap_cons,
      MatchingMemberJob.rebaseTask, Option.map_none, MatchingMemberTree.registeredNodes] using ih
  | blossom r node children siblings _ ih =>
    simp [MatchingMemberTree.jobs, MatchingMemberJob.rebaseTask, matchingRebaseQueueWork, MatchingRebaseTask.work,
      MatchingMemberTree.registeredNodes] at ih ⊢ <;> omega


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseQueueMemory

/-! matching/MatchingRebasePairSemantics.lean -/
section RppSource_MatchingRebasePairSemantics
namespace VehicleRoutingSurvey.Routing

def MatchingRebaseTask.queued (task : MatchingRebaseTask) : List MatchingRebaseTask :=
  if task.node = 0 then [] else [task]

theorem MatchingRebaseQueueEncoding.queue {s : ArithmeticState} {tasks : List MatchingRebaseTask}
    (encoding : MatchingRebaseQueueEncoding s tasks) (task : MatchingRebaseTask) :
    MatchingRebaseQueueEncoding (queuedMatchingRebaseJob s task.node task.port) (tasks ++ task.queued) := by
  by_cases singleton : task.node = 0
  · simpa [MatchingRebaseTask.queued, queuedMatchingRebaseJob, singleton] using encoding
  · simpa [MatchingRebaseTask.queued, singleton] using encoding.push task singleton

private theorem installedRebasedCyclePairMemory_outside (s : ArithmeticState) (a : ℕ)
    (outside : a ≠ s.nr 50 + s.nr 12 ∧ a ≠ s.nr 50 + s.nr 13 ∧
      a ≠ s.nr 18 + 4 * s.nr 28 ∧ a ≠ s.nr 18 + 4 * s.nr 7) :
    installedRebasedCyclePairMemory s a = s.nm a := by
  obtain ⟨mateLeft, mateRight, childLeft, childRight⟩ := outside
  simp only [installedRebasedCyclePairMemory, Function.update_of_ne mateLeft, Function.update_of_ne mateRight,
    Function.update_of_ne childLeft, Function.update_of_ne childRight]

/-- One pair adds its two nontrivial subtree requests to the work stack in order. The
mate and child representative writes are outside the previously occupied queue cells. -/
theorem rebasedCyclePairState_queue {s : ArithmeticState} {tasks : List MatchingRebaseTask}
    (encoding : MatchingRebaseQueueEncoding s tasks) (leftTree rightTree : MatchingMemberTree)
    (mates : s.nr 50 + s.nr 55 ≤ s.nr 81) (records : s.nr 81 + 2 * tasks.length ≤ s.nr 18)
    (portsInRange : let left := matchingCycleChildAt s.nm (s.nr 18 + 4 * s.nr 7)
      let ports := matchingRebasePorts s.nm (s.nr 79) left
      ports.1 < s.nr 55 ∧ ports.2 < s.nr 55) :
    let next := (s.nr 7 + 1) % s.nr 19
    let left := matchingCycleChildAt s.nm (s.nr 18 + 4 * s.nr 7)
    let right := matchingCycleChildAt s.nm (s.nr 18 + 4 * next)
    let ports := matchingRebasePorts s.nm (s.nr 79) left
    let leftTask : MatchingRebaseTask := ⟨left.node, ports.1, leftTree⟩
    let rightTask : MatchingRebaseTask := ⟨right.node, ports.2, rightTree⟩
    MatchingRebaseQueueEncoding (rebasedCyclePairState s) (tasks ++ leftTask.queued ++ rightTask.queued) := by
  intro next left right ports leftTask rightTask
  let positions := Function.update (Function.update s.nr 28 (s.nr 7)) 7 next
  let pair := {s with nr := Function.update (Function.update positions 12 ports.1) 13 ports.2}
  let installed := {pair with nm := installedRebasedCyclePairMemory pair}
  have step : rebasedCyclePairState s = queuedMatchingRebaseJob
      (queuedMatchingRebaseJob installed leftTask.node leftTask.port) rightTask.node rightTask.port := by
    simp only [rebasedCyclePairState, next, left, right, ports, leftTask, rightTask, positions, pair, installed, Prod.eta]
  have beforeQueue : MatchingRebaseQueueEncoding installed tasks := by
    apply encoding.transport (t := installed) (by simp [installed, pair, positions]) (by simp [installed, pair, positions])
    intro addr atLeast beforeEnd
    have selectedLeft : pair.nr 12 = ports.1 := by simp [pair]
    have selectedRight : pair.nr 13 = ports.2 := by simp [pair]
    have sameMateBase : pair.nr 50 = s.nr 50 := by simp [pair, positions]
    have sameCycleBase : pair.nr 18 = s.nr 18 := by simp [pair, positions]
    have leftWithin : ports.1 < s.nr 55 := portsInRange.1
    have rightWithin : ports.2 < s.nr 55 := portsInRange.2
    change installedRebasedCyclePairMemory pair addr = s.nm addr
    apply installedRebasedCyclePairMemory_outside pair addr
    rw [sameMateBase, sameCycleBase, selectedLeft, selectedRight]
    exact ⟨by omega, by omega, by omega, by omega⟩
  rw [step]
  exact (beforeQueue.queue leftTask).queue rightTask

/-- The free child's new representative is recorded before the first pair. Its
descendant job is queued under the same rule as the paired children. -/
theorem rebasedMatchingFreeChild_queue {s : ArithmeticState} {tasks : List MatchingRebaseTask}
    (encoding : MatchingRebaseQueueEncoding s tasks) (free : ℕ) (subtree : MatchingMemberTree)
    (records : s.nr 81 + 2 * tasks.length ≤ s.nr 18) :
    let address := s.nr 18 + 4 * free
    let node := (matchingCycleChildAt s.nm address).node
    let task : MatchingRebaseTask := ⟨node, s.nr 29, subtree⟩
    let seeded := {s with
      nr := Function.update s.nr 7 ((free + 1) % s.nr 19)
      nm := Function.update s.nm address (s.nr 29)}
    MatchingRebaseQueueEncoding (queuedMatchingRebaseJob seeded node (s.nr 29)) (tasks ++ task.queued) := by
  intro address node task seeded
  have beforeQueue : MatchingRebaseQueueEncoding seeded tasks := by
    apply encoding.transport (t := seeded) (by simp [seeded]) (by simp [seeded])
    intro a _ beforeEnd
    have away : a ≠ address := by dsimp [address]; omega
    exact Function.update_of_ne away _ _
  exact beforeQueue.queue task


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebasePairSemantics

/-! matching/MatchingRebasePairFrame.lean -/
section RppSource_MatchingRebasePairFrame
namespace VehicleRoutingSurvey.Routing

def OutsideRebaseMateAndStack (s : ArithmeticState) (address : ℕ) : Prop :=
  (address < s.nr 50 ∨ s.nr 50 + s.nr 55 ≤ address) ∧
  (address < s.nr 81 ∨ s.nr 81 + 2 * s.nr 55 ≤ address)

theorem queuedMatchingRebaseJob_keeps {s : ArithmeticState} (node port r : ℕ) (different : r ≠ 82) :
    (queuedMatchingRebaseJob s node port).nr r = s.nr r := by
  by_cases singleton : node = 0 <;> simp [queuedMatchingRebaseJob, singleton, Function.update_of_ne different]

theorem queuedMatchingRebaseJob_count_le (s : ArithmeticState) (node port : ℕ) :
    (queuedMatchingRebaseJob s node port).nr 82 ≤ s.nr 82 + 1 := by
  by_cases singleton : node = 0 <;> simp [queuedMatchingRebaseJob, singleton]

theorem queuedMatchingRebaseJob_untouched {s : ArithmeticState} (node port address : ℕ)
    (capacity : s.nr 82 < s.nr 55)
    (outside : address < s.nr 81 ∨ s.nr 81 + 2 * s.nr 55 ≤ address) :
    (queuedMatchingRebaseJob s node port).nm address = s.nm address := by
  have index₀ : address ≠ matchingRebaseJobAddress s (s.nr 82) := by unfold matchingRebaseJobAddress; omega
  have index₁ : address ≠ matchingRebaseJobAddress s (s.nr 82) + 1 := by unfold matchingRebaseJobAddress; omega
  by_cases singleton : node = 0 <;> simp [queuedMatchingRebaseJob, singleton, pushedMatchingRebaseJob,
    Function.update_of_ne index₀, Function.update_of_ne index₁]

def seedMatchingCycleRebase (s : ArithmeticState) (free : ℕ) : ArithmeticState :=
  let address := s.nr 18 + 4 * free
  let node := (matchingCycleChildAt s.nm address).node
  let seeded := {s with
    nr := Function.update s.nr 7 ((free + 1) % s.nr 19)
    nm := Function.update s.nm address (s.nr 29)}
  queuedMatchingRebaseJob seeded node (s.nr 29)

theorem seedMatchingCycleRebase_keeps {s : ArithmeticState} (free r : ℕ) (n7 : r ≠ 7) (n82 : r ≠ 82) :
    (seedMatchingCycleRebase s free).nr r = s.nr r := by
  simp [seedMatchingCycleRebase, queuedMatchingRebaseJob_keeps _ _ _ n82, Function.update_of_ne n7]

@[simp] theorem seedMatchingCycleRebase_index (s : ArithmeticState) (free : ℕ) :
    (seedMatchingCycleRebase s free).nr 7 = (free + 1) % s.nr 19 := by
  simp [seedMatchingCycleRebase, queuedMatchingRebaseJob_keeps _ _ _ (by decide : (7 : ℕ) ≠ 82)]

theorem seedMatchingCycleRebase_untouched {s : ArithmeticState} {free address : ℕ}
    (capacity : s.nr 82 < s.nr 55)
    (outside : address < s.nr 81 ∨ s.nr 81 + 2 * s.nr 55 ≤ address)
    (away : address ≠ s.nr 18 + 4 * free) : (seedMatchingCycleRebase s free).nm address = s.nm address := by
  let cell := s.nr 18 + 4 * free
  let seeded := {s with
    nr := Function.update s.nr 7 ((free + 1) % s.nr 19)
    nm := Function.update s.nm cell (s.nr 29)}
  let node := (matchingCycleChildAt s.nm cell).node
  change (queuedMatchingRebaseJob seeded node (s.nr 29)).nm address = s.nm address
  have room : seeded.nr 82 < seeded.nr 55 := by simpa [seeded] using capacity
  have safe : address < seeded.nr 81 ∨ seeded.nr 81 + 2 * seeded.nr 55 ≤ address := by
    simpa [seeded] using outside
  exact (queuedMatchingRebaseJob_untouched node (s.nr 29) address room safe).trans
    (Function.update_of_ne away _ _)

theorem rebasedMatchingCycleState_seed (s : ArithmeticState) (free : ℕ) :
    rebasedMatchingCycleState s free = rebaseMatchingPairsState (seedMatchingCycleRebase s free) ((s.nr 19 - 1) / 2) := rfl

/-- A pair can change only both mate slots, the two representative words,
and newly appended stack entries. In particular its stored node IDs and
original crossing edge endpoints stay readable throughout the scan. -/
theorem rebasedCyclePairState_untouched {s : ArithmeticState} {address : ℕ}
    (room : s.nr 82 + 2 ≤ s.nr 55) (outside : OutsideRebaseMateAndStack s address)
    (awayLeft : address ≠ s.nr 18 + 4 * s.nr 7)
    (awayRight : address ≠ s.nr 18 + 4 * ((s.nr 7 + 1) % s.nr 19))
    (portsInRange : let child := matchingCycleChildAt s.nm (s.nr 18 + 4 * s.nr 7)
      let ports := matchingRebasePorts s.nm (s.nr 79) child
      ports.1 < s.nr 55 ∧ ports.2 < s.nr 55) :
    (rebasedCyclePairState s).nm address = s.nm address := by
  let next := (s.nr 7 + 1) % s.nr 19
  let left := matchingCycleChildAt s.nm (s.nr 18 + 4 * s.nr 7)
  let right := matchingCycleChildAt s.nm (s.nr 18 + 4 * next)
  let ports := matchingRebasePorts s.nm (s.nr 79) left
  let positions := Function.update (Function.update s.nr 28 (s.nr 7)) 7 next
  let pair := {s with nr := Function.update (Function.update positions 12 ports.1) 13 ports.2}
  let installed := {pair with nm := installedRebasedCyclePairMemory pair}
  let first := queuedMatchingRebaseJob installed left.node ports.1
  have effect : rebasedCyclePairState s = queuedMatchingRebaseJob first right.node ports.2 := by
    simp only [rebasedCyclePairState, first, next, left, right, ports, positions, pair, installed]
  have inst81 : installed.nr 81 = s.nr 81 := by simp [installed, pair, positions]
  have inst82 : installed.nr 82 = s.nr 82 := by simp [installed, pair, positions]
  have inst55 : installed.nr 55 = s.nr 55 := by simp [installed, pair, positions]
  have first81 : first.nr 81 = s.nr 81 :=
    (queuedMatchingRebaseJob_keeps _ _ _ (by decide)).trans inst81
  have first55 : first.nr 55 = s.nr 55 :=
    (queuedMatchingRebaseJob_keeps _ _ _ (by decide)).trans inst55
  have firstBound : first.nr 82 ≤ installed.nr 82 + 1 := queuedMatchingRebaseJob_count_le _ _ _
  have enoughL : installed.nr 82 < installed.nr 55 := by rw [inst82, inst55]; omega
  have enoughR : first.nr 82 < first.nr 55 := by rw [first55]; omega
  have safeL : address < installed.nr 81 ∨ installed.nr 81 + 2 * installed.nr 55 ≤ address := by
    simpa only [inst81, inst55] using outside.2
  have safeR : address < first.nr 81 ∨ first.nr 81 + 2 * first.nr 55 ≤ address := by
    simpa only [first81, first55] using outside.2
  have firstPort : ports.1 < s.nr 55 := portsInRange.1
  have secondPort : ports.2 < s.nr 55 := portsInRange.2
  have notMate₁ : address ≠ s.nr 50 + ports.1 := by have b := outside.1; omega
  have notMate₂ : address ≠ s.nr 50 + ports.2 := by have b := outside.1; omega
  have mateWrites : installed.nm address = s.nm address := by
    simp [installed, installedRebasedCyclePairMemory, pair, positions, next, Function.update_of_ne notMate₁,
      Function.update_of_ne notMate₂, Function.update_of_ne awayLeft, Function.update_of_ne awayRight]
  rw [effect]
  exact (queuedMatchingRebaseJob_untouched right.node ports.2 address enoughR safeR).trans
    ((queuedMatchingRebaseJob_untouched left.node ports.1 address enoughL safeL).trans mateWrites)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebasePairFrame

/-! matching/MatchingRebasePairValues.lean -/
section RppSource_MatchingRebasePairValues
namespace VehicleRoutingSurvey.Routing

/-- Below or above the job stack, the queue writes leave the four mate and
representative updates of the current pair unchanged. -/
theorem rebasedCyclePairState_values {s : ArithmeticState} (address : ℕ)
    (capacity : s.nr 82 + 2 ≤ s.nr 55)
    (outside : address < s.nr 81 ∨ s.nr 81 + 2 * s.nr 55 ≤ address) :
    let right := (s.nr 7 + 1) % s.nr 19
    let row := matchingCycleChildAt s.nm (s.nr 18 + 4 * s.nr 7)
    let ports := matchingRebasePorts s.nm (s.nr 79) row
    (rebasedCyclePairState s).nm address =
      Function.update (Function.update (Function.update (Function.update
        s.nm (s.nr 50 + ports.1) ports.2) (s.nr 50 + ports.2) ports.1)
        (s.nr 18 + 4 * s.nr 7) ports.1) (s.nr 18 + 4 * right) ports.2 address := by
  intro right row ports
  let next := matchingCycleChildAt s.nm (s.nr 18 + 4 * right)
  let positions := Function.update (Function.update s.nr 28 (s.nr 7)) 7 right
  let pair := {s with nr := Function.update (Function.update positions 12 ports.1) 13 ports.2}
  let installed := {pair with nm := installedRebasedCyclePairMemory pair}
  let first := queuedMatchingRebaseJob installed row.node ports.1
  have model : rebasedCyclePairState s = queuedMatchingRebaseJob first next.node ports.2 := by
    simp only [rebasedCyclePairState, first, right, row, next, ports, positions, pair, installed]
  have stack (r : ℕ) (safe : r ∉ [7, 12, 13, 28]) : installed.nr r = s.nr r := by
    have n7 : r ≠ 7 := by simp at safe; omega
    have n12 : r ≠ 12 := by simp at safe; omega
    have n13 : r ≠ 13 := by simp at safe; omega
    have n28 : r ≠ 28 := by simp at safe; omega
    simp [installed, pair, positions, Function.update_of_ne n7, Function.update_of_ne n12,
      Function.update_of_ne n13, Function.update_of_ne n28]
  have inst81 := stack 81 (by decide)
  have inst82 := stack 82 (by decide)
  have inst55 := stack 55 (by decide)
  have first81 : first.nr 81 = s.nr 81 := (queuedMatchingRebaseJob_keeps _ _ _ (by decide)).trans inst81
  have first55 : first.nr 55 = s.nr 55 := (queuedMatchingRebaseJob_keeps _ _ _ (by decide)).trans inst55
  have firstCount : first.nr 82 ≤ installed.nr 82 + 1 := queuedMatchingRebaseJob_count_le _ _ _
  have roomFirst : installed.nr 82 < installed.nr 55 := by rw [inst82, inst55]; omega
  have roomLast : first.nr 82 < first.nr 55 := by rw [first55]; omega
  have safeFirst : address < installed.nr 81 ∨ installed.nr 81 + 2 * installed.nr 55 ≤ address := by
    simpa only [inst81, inst55] using outside
  have safeLast : address < first.nr 81 ∨ first.nr 81 + 2 * first.nr 55 ≤ address := by
    simpa only [first81, first55] using outside
  rw [model, queuedMatchingRebaseJob_untouched next.node ports.2 address roomLast safeLast]
  change first.nm address = _
  rw [show first.nm address = installed.nm address from
    queuedMatchingRebaseJob_untouched row.node ports.1 address roomFirst safeFirst] <;>
    simp [installed, installedRebasedCyclePairMemory, pair, positions]

theorem rebasedCyclePairState_mateTable {s : ArithmeticState} (v : ℕ) (inside : v < s.nr 55)
    (capacity : s.nr 82 + 2 ≤ s.nr 55) (matesBeforeJobs : s.nr 50 + s.nr 55 ≤ s.nr 81)
    (jobsBeforeCycle : s.nr 81 ≤ s.nr 18) :
    let ports := matchingRebasePorts s.nm (s.nr 79) (matchingCycleChildAt s.nm (s.nr 18 + 4 * s.nr 7))
    (rebasedCyclePairState s).nm (s.nr 50 + v) =
      Function.update (Function.update (fun x => s.nm (s.nr 50 + x)) ports.1 ports.2) ports.2 ports.1 v := by
  intro ports
  rw [rebasedCyclePairState_values (s.nr 50 + v) capacity (.inl (by omega))]
  have awayLeft : s.nr 50 + v ≠ s.nr 18 + 4 * s.nr 7 := by omega
  have awayRight : s.nr 50 + v ≠ s.nr 18 + 4 * ((s.nr 7 + 1) % s.nr 19) := by omega
  change Function.update (Function.update (Function.update (Function.update
    s.nm (s.nr 50 + ports.1) ports.2) (s.nr 50 + ports.2) ports.1)
    (s.nr 18 + 4 * s.nr 7) ports.1) (s.nr 18 + 4 * ((s.nr 7 + 1) % s.nr 19)) ports.2 (s.nr 50 + v) = _
  rw [Function.update_of_ne awayRight, Function.update_of_ne awayLeft]
  by_cases second : v = ports.2
  · subst v
    simp
  · rw [Function.update_of_ne second, Function.update_of_ne (by omega : s.nr 50 + v ≠ s.nr 50 + ports.2)]
    by_cases first : v = ports.1
    · subst v
      simp
    · rw [Function.update_of_ne first, Function.update_of_ne (by omega : s.nr 50 + v ≠ s.nr 50 + ports.1)]


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebasePairValues

/-! matching/MatchingRebaseRowValues.lean -/
section RppSource_MatchingRebaseRowValues
namespace VehicleRoutingSurvey.Routing

/-- Installing the free child changes its row representative to the requested
original port and preserves every other representative. -/
theorem seedMatchingCycleRebase_row {s : ArithmeticState} {free v : ℕ}
    (capacity : s.nr 82 < s.nr 55) (afterStack : s.nr 81 + 2 * s.nr 55 ≤ s.nr 18) :
    (seedMatchingCycleRebase s free).nm (s.nr 18 + 4 * v) =
      Function.update (fun x => s.nm (s.nr 18 + 4 * x)) free (s.nr 29) v := by
  let base := s.nr 18 + 4 * free
  let next := {s with nr := Function.update s.nr 7 ((free + 1) % s.nr 19), nm := Function.update s.nm base (s.nr 29)}
  let node := (matchingCycleChildAt s.nm base).node
  have room : next.nr 82 < next.nr 55 := by simpa [next] using capacity
  have outside : next.nr 81 + 2 * next.nr 55 ≤ s.nr 18 + 4 * v := by simp [next]; omega
  change (queuedMatchingRebaseJob next node (s.nr 29)).nm _ = _
  rw [queuedMatchingRebaseJob_untouched _ _ _ room (.inr outside)]
  by_cases same : v = free
  · subst v
    simp [next, base]
  · have diff : s.nr 18 + 4 * v ≠ base := by dsimp [base]; omega
    simp [next, Function.update_of_ne diff, Function.update_of_ne same]

/-- Both representative cells receive exactly the original vertices installed
in the two mate slots. This equality holds on every physical child row. -/
theorem rebasedCyclePairState_row {s : ArithmeticState} (v : ℕ)
    (capacity : s.nr 82 + 2 ≤ s.nr 55) (afterStack : s.nr 81 + 2 * s.nr 55 ≤ s.nr 18)
    (afterMates : s.nr 50 + s.nr 55 ≤ s.nr 18)
    (bounded : let p := matchingRebasePorts s.nm (s.nr 79) (matchingCycleChildAt s.nm (s.nr 18 + 4 * s.nr 7))
      p.1 < s.nr 55 ∧ p.2 < s.nr 55) :
    let right := (s.nr 7 + 1) % s.nr 19
    let ports := matchingRebasePorts s.nm (s.nr 79) (matchingCycleChildAt s.nm (s.nr 18 + 4 * s.nr 7))
    (rebasedCyclePairState s).nm (s.nr 18 + 4 * v) =
      Function.update (Function.update (fun x => s.nm (s.nr 18 + 4 * x)) (s.nr 7) ports.1) right ports.2 v := by
  intro right ports
  rw [rebasedCyclePairState_values _ capacity (.inr (by omega))]
  change Function.update (Function.update (Function.update (Function.update
      s.nm (s.nr 50 + ports.1) ports.2) (s.nr 50 + ports.2) ports.1) (s.nr 18 + 4 * s.nr 7) ports.1)
    (s.nr 18 + 4 * right) ports.2 (s.nr 18 + 4 * v) = _
  by_cases second : v = right
  · subst v
    simp
  · rw [Function.update_of_ne (by omega : s.nr 18 + 4 * v ≠ s.nr 18 + 4 * right), Function.update_of_ne second]
    by_cases first : v = s.nr 7
    · subst v
      simp
    · have valid : ports.1 < s.nr 55 ∧ ports.2 < s.nr 55 := bounded
      rw [Function.update_of_ne (by omega : s.nr 18 + 4 * v ≠ s.nr 18 + 4 * s.nr 7), Function.update_of_ne first,
        Function.update_of_ne (by omega : s.nr 18 + 4 * v ≠ s.nr 50 + ports.2),
        Function.update_of_ne (by omega : s.nr 18 + 4 * v ≠ s.nr 50 + ports.1)]


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseRowValues

/-! matching/MatchingRebaseCycleTaskOrder.lean -/
section RppSource_MatchingRebaseCycleTaskOrder
namespace VehicleRoutingSurvey.Routing

def MatchingMemberJob.chosenRebaseTask (job : MatchingMemberJob) (choosePort : MatchingMemberJob → ℕ) :
    MatchingRebaseTask := ⟨job.node, choosePort job, job.children.getD .nil⟩

theorem MatchingMemberJob.queued_of_proper (job : MatchingMemberJob) (choosePort : MatchingMemberJob → ℕ)
    (wellFormed : job.proper) :
    ([job].filterMap (MatchingMemberJob.rebaseTask choosePort)) = (job.chosenRebaseTask choosePort).queued := by
  cases form : job.children with
  | none =>
    have singleton : job.node = 0 := by simpa [MatchingMemberJob.proper, form] using wellFormed
    simp [MatchingMemberJob.rebaseTask, MatchingMemberJob.chosenRebaseTask, MatchingRebaseTask.queued, form, singleton]
  | some children =>
    have proper : 0 < job.node ∧ 2 ≤ children.arity ∧ children.proper := by
      simpa [MatchingMemberJob.proper, form] using wellFormed
    simp [MatchingMemberJob.rebaseTask, MatchingMemberJob.chosenRebaseTask, MatchingRebaseTask.queued,
      form, Nat.ne_of_gt proper.1]

/-- The requests added after the new free child and `pairs` alternating pairs. -/
def matchingRebaseCycleTaskPrefix (children : MatchingMemberTree) (choosePort : MatchingMemberJob → ℕ)
    (free pairs : ℕ) : List MatchingRebaseTask :=
  (((children.jobs none).rotate free).take (2 * pairs + 1)).filterMap (MatchingMemberJob.rebaseTask choosePort)

theorem matchingRebaseCycleTaskPrefix_length (children : MatchingMemberTree)
    (choosePort : MatchingMemberJob → ℕ) (free pairs : ℕ) :
    (matchingRebaseCycleTaskPrefix children choosePort free pairs).length ≤ 2 * pairs + 1 := by
  unfold matchingRebaseCycleTaskPrefix
  exact (List.length_filterMap_le _ _).trans (by simp [List.length_take])

theorem matchingRebaseCycleTaskPrefix_start (children : MatchingMemberTree) (choosePort : MatchingMemberJob → ℕ)
    {free : ℕ} (inside : free < (children.jobs none).length) (proper : children.proper) :
    matchingRebaseCycleTaskPrefix children choosePort free 0 =
      ((children.jobs none)[free].chosenRebaseTask choosePort).queued := by
  let jobs := children.jobs none
  have nonempty : 0 < (jobs.rotate free).length := by simp [jobs]; omega
  have first : (jobs.rotate free)[0] = jobs[free] := by
    have noWrap : free % jobs.length = free := Nat.mod_eq_of_lt inside
    simp only [List.getElem_rotate, Nat.zero_add, noWrap]
  unfold matchingRebaseCycleTaskPrefix
  change ((jobs.rotate free).take (0 + 1)).filterMap _ = _
  rw [List.take_succ_eq_append_getElem nonempty, List.take_zero, List.nil_append, first]
  exact (jobs[free]).queued_of_proper choosePort (children.jobs_proper none proper _ (List.getElem_mem inside))

theorem matchingRebaseCycleTaskPrefix_next (children : MatchingMemberTree) (choosePort : MatchingMemberJob → ℕ)
    {free pair : ℕ} (proper : children.proper) (odd : Odd (children.jobs none).length)
    (within : pair < ((children.jobs none).length - 1) / 2) :
    let jobs := children.jobs none
    let left := matchingRebaseChildIndex jobs.length free pair false
    let right := matchingRebaseChildIndex jobs.length free pair true
    let leftJob := jobs[left]'(Nat.mod_lt _ (show 0 < (children.jobs none).length by omega))
    let rightJob := jobs[right]'(Nat.mod_lt _ (show 0 < (children.jobs none).length by omega))
    matchingRebaseCycleTaskPrefix children choosePort free (pair + 1) =
      matchingRebaseCycleTaskPrefix children choosePort free pair ++
        (leftJob.chosenRebaseTask choosePort).queued ++ (rightJob.chosenRebaseTask choosePort).queued := by
  intro jobs left right leftJob rightJob
  have leftIn : 2 * pair + 1 < (jobs.rotate free).length := by
    rw [List.length_rotate]
    change pair < (jobs.length - 1) / 2 at within
    omega
  have rightIn : 2 * pair + 1 + 1 < (jobs.rotate free).length := by
    rw [List.length_rotate]
    change pair < (jobs.length - 1) / 2 at within
    omega
  have leftAt : (jobs.rotate free)[2 * pair + 1] = leftJob := by
    simp [leftJob, left, matchingRebaseChildIndex, Nat.add_comm]
  have rightAt : (jobs.rotate free)[2 * pair + 1 + 1] = rightJob := by
    simp [rightJob, right, matchingRebaseChildIndex, Nat.add_comm]
    have shift : 1 + (1 + 2 * pair) = 2 + 2 * pair := by omega
    simp only [shift]
  have leftTyped : leftJob.proper := children.jobs_proper none proper _ (List.getElem_mem _)
  have rightTyped : rightJob.proper := children.jobs_proper none proper _ (List.getElem_mem _)
  unfold matchingRebaseCycleTaskPrefix
  change ((jobs.rotate free).take (2 * (pair + 1) + 1)).filterMap _ = _
  rw [show 2 * (pair + 1) + 1 = 2 * pair + 1 + 1 + 1 by omega,
    List.take_succ_eq_append_getElem rightIn, List.take_succ_eq_append_getElem leftIn, leftAt, rightAt,
    List.filterMap_append, List.filterMap_append, leftJob.queued_of_proper choosePort leftTyped,
    rightJob.queued_of_proper choosePort rightTyped]

/-- The order of rotation affects execution order and preserves the exact
number of registered descendants that remain pending. -/
theorem matchingRebaseCycleTaskPrefix_work (children : MatchingMemberTree) (choosePort : MatchingMemberJob → ℕ)
    (free : ℕ) (odd : Odd (children.jobs none).length) :
    matchingRebaseQueueWork (matchingRebaseCycleTaskPrefix children choosePort free
      (((children.jobs none).length - 1) / 2)) = children.registeredNodes := by
  let jobs := children.jobs none
  have all : 2 * ((jobs.length - 1) / 2) + 1 = jobs.length := by
    change Odd jobs.length at odd
    obtain ⟨half, size⟩ := odd
    omega
  unfold matchingRebaseCycleTaskPrefix
  change matchingRebaseQueueWork (((jobs.rotate free).take (2 * ((jobs.length - 1) / 2) + 1)).filterMap _) = _
  rw [all, ← List.length_rotate jobs free, List.take_length]
  · have ordered := (List.rotate_perm jobs free).filterMap (MatchingMemberJob.rebaseTask choosePort)
    exact (matchingRebaseQueueWork_perm ordered).trans (children.rebaseTasks_work choosePort)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseCycleTaskOrder

/-! matching/MatchingRebaseCycleQueue.lean -/
section RppSource_MatchingRebaseCycleQueue
namespace VehicleRoutingSurvey.Routing

private theorem matchingRebasePorts_inRange (memory : ℕ → ℕ) (mapBase : ℕ)
    (child : MatchingCycleChild) {k : ℕ} (a : child.endpointA < k) (b : child.endpointB < k) :
    (matchingRebasePorts memory mapBase child).1 < k ∧ (matchingRebasePorts memory mapBase child).2 < k := by
  unfold matchingRebasePorts
  split
  · exact ⟨a, b⟩
  · exact ⟨b, a⟩

/-- Recorded children and chosen ports for the current cycle, in its physical
array order. The work stack is stored between the member map and the cycle. -/
structure MatchingRebaseCycleQueueInput (s : ArithmeticState) (children : MatchingMemberTree)
    (free : ℕ) (prior : List MatchingRebaseTask) (choosePort : MatchingMemberJob → ℕ) : Prop where
  encoded : MatchingRebaseQueueEncoding s prior
  proper : children.proper
  size : s.nr 19 = (children.jobs none).length
  odd : Odd (s.nr 19)
  inside : free < s.nr 19
  capacity : prior.length + s.nr 19 ≤ s.nr 55
  matesBeforeMap : s.nr 50 + s.nr 55 ≤ s.nr 79
  mapBeforeStack : s.nr 79 + s.nr 55 ≤ s.nr 81
  stackBeforeRecord : s.nr 81 + 2 * s.nr 55 ≤ s.nr 18
  nodes : ∀ i, ∀ hi : i < (children.jobs none).length,
    (matchingCycleChildAt s.nm (s.nr 18 + 4 * i)).node = ((children.jobs none)[i]).node
  endpoints : ∀ i < s.nr 19,
    let child := matchingCycleChildAt s.nm (s.nr 18 + 4 * i)
    child.endpointA < s.nr 55 ∧ child.endpointB < s.nr 55
  exposed : choosePort ((children.jobs none)[free]'(size ▸ inside)) = s.nr 29
  ports : ∀ i < (s.nr 19 - 1) / 2,
    let left := matchingRebaseChildIndex (s.nr 19) free i false
    let right := matchingRebaseChildIndex (s.nr 19) free i true
    let lhs := (children.jobs none)[left]'(size ▸ Nat.mod_lt _ (by omega))
    let rhs := (children.jobs none)[right]'(size ▸ Nat.mod_lt _ (by omega))
    matchingRebasePorts s.nm (s.nr 79) (matchingCycleChildAt s.nm (s.nr 18 + 4 * left)) =
      (choosePort lhs, choosePort rhs)

def OutsideEarlierCycleWrites (s : ArithmeticState) (free pairs address : ℕ) : Prop :=
  OutsideRebaseMateAndStack s address ∧ address ≠ s.nr 18 + 4 * free ∧
    ∀ i < pairs, ∀ side : Bool,
      address ≠ s.nr 18 + 4 * matchingRebaseChildIndex (s.nr 19) free i side

/-- Original endpoint pair for a rotated cycle edge, before the scan changes representatives. -/
def matchingRebaseOriginalPair (s : ArithmeticState) (free i : ℕ) : ℕ × ℕ :=
  let left := matchingRebaseChildIndex (s.nr 19) free i false
  matchingRebasePorts s.nm (s.nr 79) (matchingCycleChildAt s.nm (s.nr 18 + 4 * left))

/-- The original-vertex mate table after installing the first `pairs` edges. -/
def matchingRebaseMatePrefix (mate : ℕ → ℕ) (edge : ℕ → ℕ × ℕ) : ℕ → ℕ → ℕ
  | 0 => mate
  | i + 1 => Function.update (Function.update (matchingRebaseMatePrefix mate edge i)
      (edge i).1 (edge i).2) (edge i).2 (edge i).1

/-- Representative in every stored child row after `i` installed pairs. -/
def matchingRebaseRepresentativePrefix (s : ArithmeticState) (free : ℕ) : ℕ → ℕ → ℕ
  | 0 => Function.update (fun j => s.nm (s.nr 18 + 4 * j)) free (s.nr 29)
  | i + 1 => Function.update (Function.update (matchingRebaseRepresentativePrefix s free i)
      (matchingRebaseChildIndex (s.nr 19) free i false) (matchingRebaseOriginalPair s free i).1)
      (matchingRebaseChildIndex (s.nr 19) free i true) (matchingRebaseOriginalPair s free i).2

/-- The actual rematch model queues exactly the registered children, visiting
the free child first and then the two children of each alternating edge. -/
theorem rebasedMatchingCycleState_fullEffects {s : ArithmeticState} {children : MatchingMemberTree}
    {free : ℕ} {prior : List MatchingRebaseTask} {choosePort : MatchingMemberJob → ℕ}
    (frame : MatchingRebaseCycleQueueInput s children free prior choosePort) :
    let added := matchingRebaseCycleTaskPrefix children choosePort free ((s.nr 19 - 1) / 2)
    MatchingRebaseQueueEncoding (rebasedMatchingCycleState s free) (prior ++ added) ∧
      matchingRebaseQueueWork added = children.registeredNodes ∧
      (∀ address, OutsideEarlierCycleWrites s free ((s.nr 19 - 1) / 2) address →
        (rebasedMatchingCycleState s free).nm address = s.nm address) ∧
      (∀ v < s.nr 55, (rebasedMatchingCycleState s free).nm (s.nr 50 + v) =
        matchingRebaseMatePrefix (fun x => s.nm (s.nr 50 + x))
          (matchingRebaseOriginalPair s free) ((s.nr 19 - 1) / 2) v) ∧
      ∀ v, (rebasedMatchingCycleState s free).nm (s.nr 18 + 4 * v) =
        matchingRebaseRepresentativePrefix s free ((s.nr 19 - 1) / 2) v := by
  intro added
  let jobs := children.jobs none
  let total := (s.nr 19 - 1) / 2
  let start := seedMatchingCycleRebase s free
  let state (i : ℕ) := rebaseMatchingPairsState start i
  let pending (i : ℕ) := prior ++ matchingRebaseCycleTaskPrefix children choosePort free i
  have size : s.nr 19 = jobs.length := frame.size
  have freeIn : free < s.nr 19 := frame.inside
  have odd : Odd jobs.length := size ▸ frame.odd
  have room := frame.capacity
  have mateMap := frame.matesBeforeMap
  have mapStack := frame.mapBeforeStack
  have stackRecords := frame.stackBeforeRecord
  have fullCount : 2 * total + 1 = s.nr 19 := by
    obtain ⟨n, length⟩ := frame.odd
    change 2 * ((s.nr 19 - 1) / 2) + 1 = s.nr 19
    omega
  have indices := matchingRebaseChildIndex_complete frame.inside frame.odd
  have start19 : start.nr 19 = s.nr 19 := seedMatchingCycleRebase_keeps free 19 (by decide) (by decide)
  have startIndex : start.nr 7 = (free + 1) % start.nr 19 := by
    rw [start19]
    exact seedMatchingCycleRebase_index s free
  have unchangedRegister (i r : ℕ) (away : r ∉ [7, 12, 13, 28, 82]) : (state i).nr r = s.nr r := by
    refine (rebaseMatchingPairsState_get (s := start) i r away).trans ?_
    exact seedMatchingCycleRebase_keeps free r (by simp at away; omega) (by simp at away; omega)
  have initialEncoding : MatchingRebaseQueueEncoding start (pending 0) := by
    have freeJob : free < jobs.length := size ▸ freeIn
    rw [show pending 0 = prior ++ (jobs[free].chosenRebaseTask choosePort).queued from
      congrArg (prior ++ ·) (matchingRebaseCycleTaskPrefix_start children choosePort freeJob frame.proper)]
    have lower : s.nr 81 + 2 * prior.length ≤ s.nr 18 := by omega
    have runs := rebasedMatchingFreeChild_queue frame.encoded free (jobs[free].children.getD .nil) lower
    have nodeAt : (matchingCycleChildAt s.nm (s.nr 18 + 4 * free)).node = jobs[free].node := frame.nodes free freeJob
    have portAt : s.nr 29 = choosePort jobs[free] := frame.exposed.symm
    change MatchingRebaseQueueEncoding start (prior ++
      (MatchingRebaseTask.mk (matchingCycleChildAt s.nm (s.nr 18 + 4 * free)).node (s.nr 29)
        (jobs[free].children.getD .nil)).queued) at runs
    rw [nodeAt, portAt] at runs
    exact runs
  have progress (i : ℕ) (atMost : i ≤ total) :
      MatchingRebaseQueueEncoding (state i) (pending i) ∧
      (∀ address, OutsideEarlierCycleWrites s free i address → (state i).nm address = s.nm address) ∧
      (∀ v < s.nr 55, (state i).nm (s.nr 50 + v) =
        matchingRebaseMatePrefix (fun x => s.nm (s.nr 50 + x)) (matchingRebaseOriginalPair s free) i v) ∧
      ∀ v, (state i).nm (s.nr 18 + 4 * v) = matchingRebaseRepresentativePrefix s free i v := by
    induction i with
    | zero =>
      refine ⟨initialEncoding, ?_, ?_, ?_⟩
      · intro address untouched
        apply seedMatchingCycleRebase_untouched _ untouched.1.2 untouched.2.1
        rw [frame.encoded.count]
        omega
      · intro v inside
        apply seedMatchingCycleRebase_untouched _ (.inl (by omega)) (by omega)
        rw [frame.encoded.count]
        omega
      · intro v
        apply seedMatchingCycleRebase_row _ stackRecords
        rw [frame.encoded.count]
        omega
    | succ i ih =>
      have within : i < total := atMost
      obtain ⟨before, frozen, mates, representatives⟩ := ih within.le
      let previous := state i
      let childIndex (side : Bool) := matchingRebaseChildIndex (s.nr 19) free i side
      have fixed (r : ℕ) (away : r ∉ [7, 12, 13, 28, 82]) : previous.nr r = s.nr r :=
        unchangedRegister i r away
      have position := rebaseMatchingPairsState_childIndices (s := start) i
        (by rwa [start19]) startIndex
      have positionL : previous.nr 7 = childIndex false := by
        simpa only [state, previous, childIndex, start19] using position.1
      have positionR : (previous.nr 7 + 1) % previous.nr 19 = childIndex true := by
        have derived : (previous.nr 7 + 1) % start.nr 19 = childIndex true := by
          simpa only [state, previous, childIndex, start19] using position.2
        rwa [fixed 19 (by decide), ← start19]
      have bounded (side : Bool) : childIndex side < s.nr 19 := (indices.1 i within side).1
      have stableWord (side : Bool) (w : ℕ) (width : w < 4) :
          previous.nm (s.nr 18 + 4 * childIndex side + w) = s.nm (s.nr 18 + 4 * childIndex side + w) := by
        apply frozen
        refine ⟨⟨.inr (by omega), .inr (by omega)⟩, ?_, ?_⟩
        · have fresh : childIndex side ≠ free := (indices.1 i within side).2
          omega
        · intro earlier strict which
          intro equal
          have atWord : childIndex side = matchingRebaseChildIndex (s.nr 19) free earlier which := by omega
          have matchIndex := indices.2.2 i within earlier (strict.trans within) side which atWord
          omega
      have sameRow (side : Bool) :
          matchingCycleChildAt previous.nm (s.nr 18 + 4 * childIndex side) =
          matchingCycleChildAt s.nm (s.nr 18 + 4 * childIndex side) := by
        have zero := stableWord side 0 (by decide)
        rw [Nat.add_zero] at zero
        simp only [matchingCycleChildAt, zero, stableWord side 1 (by decide), stableWord side 2 (by decide),
          stableWord side 3 (by decide)]
      let originalLeft := matchingCycleChildAt s.nm (s.nr 18 + 4 * childIndex false)
      let originalRight := matchingCycleChildAt s.nm (s.nr 18 + 4 * childIndex true)
      have lhs : matchingCycleChildAt previous.nm (previous.nr 18 + 4 * previous.nr 7) = originalLeft := by
        rw [fixed 18 (by decide), positionL]
        exact sameRow false
      have rhs : matchingCycleChildAt previous.nm (previous.nr 18 + 4 * ((previous.nr 7 + 1) % previous.nr 19)) =
          originalRight := by
        rw [fixed 18 (by decide), positionR]
        exact sameRow true
      have edgeRange : originalLeft.endpointA < s.nr 55 ∧ originalLeft.endpointB < s.nr 55 :=
        frame.endpoints _ (bounded false)
      have stableMap : previous.nm (s.nr 79 + originalLeft.endpointA) = s.nm (s.nr 79 + originalLeft.endpointA) := by
        apply frozen
        have inside := edgeRange.1
        exact ⟨⟨.inr (by omega), .inl (by omega)⟩, by omega, fun _ _ _ => by omega⟩
      have samePorts : matchingRebasePorts previous.nm (previous.nr 79) originalLeft =
          matchingRebasePorts s.nm (s.nr 79) originalLeft := by
        rw [fixed 79 (by decide)]
        simp [matchingRebasePorts, stableMap]
      let leftJob := jobs[childIndex false]'(size ▸ bounded false)
      let rightJob := jobs[childIndex true]'(size ▸ bounded true)
      have ports : matchingRebasePorts previous.nm (previous.nr 79)
          (matchingCycleChildAt previous.nm (previous.nr 18 + 4 * previous.nr 7)) =
          (choosePort leftJob, choosePort rightJob) := by
        rw [lhs, samePorts]
        exact frame.ports i within
      have range : let child := matchingCycleChildAt previous.nm (previous.nr 18 + 4 * previous.nr 7)
          let ports := matchingRebasePorts previous.nm (previous.nr 79) child
          ports.1 < previous.nr 55 ∧ ports.2 < previous.nr 55 := by
        change (matchingRebasePorts previous.nm (previous.nr 79)
          (matchingCycleChildAt previous.nm (previous.nr 18 + 4 * previous.nr 7))).1 < previous.nr 55 ∧ _
        rw [lhs, samePorts, fixed 55 (by decide)]
        exact matchingRebasePorts_inRange s.nm (s.nr 79) originalLeft edgeRange.1 edgeRange.2
      have maxPending : (pending i).length + 2 ≤ s.nr 55 := by
        have used := matchingRebaseCycleTaskPrefix_length children choosePort free i
        change (prior ++ matchingRebaseCycleTaskPrefix children choosePort free i).length + 2 ≤ s.nr 55
        rw [List.length_append]
        omega
      have roomNow : previous.nr 82 + 2 ≤ previous.nr 55 := by
        have counted : previous.nr 82 = (pending i).length := before.count
        rw [counted, fixed 55 (by decide)]
        exact maxPending
      have mateSafe : previous.nr 50 + previous.nr 55 ≤ previous.nr 81 := by
        rw [fixed 50 (by decide), fixed 55 (by decide), fixed 81 (by decide)]
        omega
      have stackSafe : previous.nr 81 + 2 * (pending i).length ≤ previous.nr 18 := by
        rw [fixed 81 (by decide), fixed 18 (by decide)]
        omega
      have pushes := rebasedCyclePairState_queue (s := previous) before (leftJob.children.getD .nil) (rightJob.children.getD .nil)
        mateSafe stackSafe range
      have leftNode : originalLeft.node = leftJob.node := frame.nodes _ (size ▸ bounded false)
      have rightNode : originalRight.node = rightJob.node := frame.nodes _ (size ▸ bounded true)
      have originalPorts : matchingRebasePorts previous.nm (previous.nr 79) originalLeft =
          (choosePort leftJob, choosePort rightJob) := by simpa only [lhs] using ports
      have queue : MatchingRebaseQueueEncoding (rebasedCyclePairState previous)
          ((pending i) ++ (leftJob.chosenRebaseTask choosePort).queued ++ (rightJob.chosenRebaseTask choosePort).queued) := by
        simpa only [lhs, rhs, originalPorts, leftNode, rightNode, MatchingMemberJob.chosenRebaseTask] using pushes
      have order := matchingRebaseCycleTaskPrefix_next children choosePort (free := free) (pair := i)
        frame.proper odd (by rwa [← size])
      have nonemptyJobs : 0 < jobs.length := size ▸ Nat.zero_lt_of_lt freeIn
      have oldIndex (side : Bool) :
          jobs[matchingRebaseChildIndex jobs.length free i side]'(Nat.mod_lt _ nonemptyJobs) =
            jobs[childIndex side]'(size ▸ bounded side) := by
        apply getElem_congr_idx
        exact congrArg (fun n => matchingRebaseChildIndex n free i side) size.symm
      have sameJobs :
          (jobs[matchingRebaseChildIndex jobs.length free i false]'(Nat.mod_lt _ nonemptyJobs),
            jobs[matchingRebaseChildIndex jobs.length free i true]'(Nat.mod_lt _ nonemptyJobs)) = (leftJob, rightJob) :=
        Prod.ext (oldIndex false) (oldIndex true)
      have sameTasks := congrArg (fun pair : MatchingMemberJob × MatchingMemberJob =>
        matchingRebaseCycleTaskPrefix children choosePort free i ++
          (pair.1.chosenRebaseTask choosePort).queued ++ (pair.2.chosenRebaseTask choosePort).queued)
        sameJobs
      have nextOrder : matchingRebaseCycleTaskPrefix children choosePort free (i + 1) =
          matchingRebaseCycleTaskPrefix children choosePort free i ++
            (leftJob.chosenRebaseTask choosePort).queued ++ (rightJob.chosenRebaseTask choosePort).queued :=
        order.trans sameTasks
      have nextList : pending (i + 1) =
          pending i ++ (leftJob.chosenRebaseTask choosePort).queued ++ (rightJob.chosenRebaseTask choosePort).queued := by
        simp only [pending, nextOrder, List.append_assoc]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [nextList]
        let paired := rebasedCyclePairState previous
        let following := {paired with nr := Function.update paired.nr 7 ((previous.nr 7 + 2) % previous.nr 19)}
        change MatchingRebaseQueueEncoding following _
        exact queue.transport (by simp [following, paired]) (by simp [following, paired]) (fun _ _ _ => rfl)
      · intro address untouched
        have outsideCurrent : OutsideRebaseMateAndStack previous address := by
          simpa only [OutsideRebaseMateAndStack, fixed 50 (by decide), fixed 55 (by decide),
            fixed 81 (by decide)] using untouched.1
        have leftAway : address ≠ previous.nr 18 + 4 * previous.nr 7 := by
          rw [fixed 18 (by decide), positionL]
          exact untouched.2.2 i (by omega) false
        have rightAway : address ≠ previous.nr 18 + 4 * ((previous.nr 7 + 1) % previous.nr 19) := by
          rw [fixed 18 (by decide), positionR]
          exact untouched.2.2 i (by omega) true
        change (rebasedCyclePairState previous).nm address = s.nm address
        exact (rebasedCyclePairState_untouched roomNow outsideCurrent leftAway rightAway range).trans
          (frozen address ⟨untouched.1, untouched.2.1, fun j hj b => untouched.2.2 j (by omega) b⟩)
      · intro v inside
        let edge := matchingRebaseOriginalPair s free i
        have asEdge : matchingRebasePorts previous.nm (previous.nr 79)
            (matchingCycleChildAt previous.nm (previous.nr 18 + 4 * previous.nr 7)) = edge := by
          rw [lhs, samePorts]
          rfl
        have boundedV : v < previous.nr 55 := by rwa [fixed 55 (by decide)]
        have records : previous.nr 81 ≤ previous.nr 18 := by
          rw [fixed 81 (by decide), fixed 18 (by decide)]
          omega
        have install := rebasedCyclePairState_mateTable (s := previous) v boundedV roomNow mateSafe records
        dsimp only at install
        rw [asEdge, fixed 50 (by decide)] at install
        change (rebasedCyclePairState previous).nm (s.nr 50 + v) =
          Function.update (Function.update (matchingRebaseMatePrefix (fun x => s.nm (s.nr 50 + x))
            (matchingRebaseOriginalPair s free) i) edge.1 edge.2) edge.2 edge.1 v
        rw [install]
        by_cases second : v = edge.2
        · simp [second]
        · rw [Function.update_of_ne second, Function.update_of_ne second]
          by_cases first : v = edge.1
          · simp [first]
          · rw [Function.update_of_ne first, Function.update_of_ne first]
            exact mates v inside
      · intro v
        have afterStack : previous.nr 81 + 2 * previous.nr 55 ≤ previous.nr 18 := by
          rwa [fixed 81 (by decide), fixed 55 (by decide), fixed 18 (by decide)]
        have afterMates : previous.nr 50 + previous.nr 55 ≤ previous.nr 18 := by omega
        have rowValue := rebasedCyclePairState_row (s := previous) v roomNow afterStack afterMates range
        let edge := matchingRebaseOriginalPair s free i
        have asEdge : matchingRebasePorts previous.nm (previous.nr 79)
            (matchingCycleChildAt previous.nm (previous.nr 18 + 4 * previous.nr 7)) = edge := by
          rw [lhs, samePorts]
          rfl
        dsimp only at rowValue
        rw [asEdge, positionR, fixed 18 (by decide), positionL] at rowValue
        change (rebasedCyclePairState previous).nm (s.nr 18 + 4 * v) =
          Function.update (Function.update (matchingRebaseRepresentativePrefix s free i)
            (childIndex false) edge.1) (childIndex true) edge.2 v
        rw [rowValue]
        by_cases right : v = childIndex true
        · simp [right]
        · rw [Function.update_of_ne right, Function.update_of_ne right]
          by_cases left : v = childIndex false
          · simp [left]
          · rw [Function.update_of_ne left, Function.update_of_ne left]
            exact representatives v
  rw [rebasedMatchingCycleState_seed]
  have checked := progress total le_rfl
  have work : matchingRebaseQueueWork added = children.registeredNodes := by
    change matchingRebaseQueueWork (matchingRebaseCycleTaskPrefix children choosePort free total) = _
    rw [show total = (jobs.length - 1) / 2 by simp [total, size]]
    exact matchingRebaseCycleTaskPrefix_work children choosePort free odd
  exact ⟨checked.1, work, checked.2⟩

theorem rebasedMatchingCycleState_effects {s : ArithmeticState} {children : MatchingMemberTree}
    {free : ℕ} {prior : List MatchingRebaseTask} {choosePort : MatchingMemberJob → ℕ}
    (frame : MatchingRebaseCycleQueueInput s children free prior choosePort) :
    let added := matchingRebaseCycleTaskPrefix children choosePort free ((s.nr 19 - 1) / 2)
    MatchingRebaseQueueEncoding (rebasedMatchingCycleState s free) (prior ++ added) ∧
      matchingRebaseQueueWork added = children.registeredNodes ∧
      (∀ address, OutsideEarlierCycleWrites s free ((s.nr 19 - 1) / 2) address →
        (rebasedMatchingCycleState s free).nm address = s.nm address) ∧
      ∀ v < s.nr 55, (rebasedMatchingCycleState s free).nm (s.nr 50 + v) =
        matchingRebaseMatePrefix (fun x => s.nm (s.nr 50 + x))
          (matchingRebaseOriginalPair s free) ((s.nr 19 - 1) / 2) v := by
  have result := rebasedMatchingCycleState_fullEffects frame
  exact ⟨result.1, result.2.1, result.2.2.1, result.2.2.2.1⟩

theorem rebasedMatchingCycleState_queue {s : ArithmeticState} {children : MatchingMemberTree}
    {free : ℕ} {prior : List MatchingRebaseTask} {choosePort : MatchingMemberJob → ℕ}
    (frame : MatchingRebaseCycleQueueInput s children free prior choosePort) :
    let added := matchingRebaseCycleTaskPrefix children choosePort free ((s.nr 19 - 1) / 2)
    MatchingRebaseQueueEncoding (rebasedMatchingCycleState s free) (prior ++ added) ∧
      matchingRebaseQueueWork added = children.registeredNodes ∧
      ∀ address, OutsideEarlierCycleWrites s free ((s.nr 19 - 1) / 2) address →
        (rebasedMatchingCycleState s free).nm address = s.nm address :=
  ⟨(rebasedMatchingCycleState_effects frame).1, (rebasedMatchingCycleState_effects frame).2.1,
    (rebasedMatchingCycleState_effects frame).2.2.1⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseCycleQueue

/-! matching/MatchingRebaseQueueUpdate.lean -/
section RppSource_MatchingRebaseQueueUpdate
namespace VehicleRoutingSurvey.Routing

/-- Loading the cycle may reuse the membership map and DFS stack. The
remaining jobs are kept in the separate rebase stack. -/
theorem MatchingRebaseCycleLoaded.queueEncoding {s loaded : ArithmeticState}
    {children : MatchingMemberTree} {free : ℕ} {prior : List MatchingRebaseTask}
    (view : MatchingRebaseCycleLoaded s loaded children free)
    (priorEncoding : MatchingRebaseQueueEncoding s prior)
    (mapBeforeStack : s.nr 79 + s.nr 55 ≤ s.nr 81)
    (walkBeforeStack : s.nr 80 + 3 * s.nr 55 ≤ s.nr 81) :
    MatchingRebaseQueueEncoding loaded prior := by
  apply priorEncoding.transport (view.registers 81 (by decide)) (view.registers 82 (by decide))
  intro a lower _
  exact view.outside a ⟨Or.inr (mapBeforeStack.trans lower), Or.inr (walkBeforeStack.trans lower)⟩

theorem rebasedMatchingCycleState_stackBase (s : ArithmeticState) (free : ℕ) :
    (rebasedMatchingCycleState s free).nr 81 = s.nr 81 := by
  rw [rebasedMatchingCycleState_seed]
  exact (rebaseMatchingPairsState_get ((s.nr 19 - 1) / 2) 81 (by decide)).trans
    (seedMatchingCycleRebase_keeps free 81 (by decide) (by decide))

/-- Transfer the cyclic model's stack update to the actual state returned
by `rebaseMatchingNodeJobBlock_correct`. -/
theorem MatchingRebaseCycleQueueInput.actualQueueUpdate {s loaded t : ArithmeticState}
    {earlier : List MatchingRebaseTask} {task : MatchingRebaseTask} {free : ℕ}
    {choosePort : MatchingMemberJob → ℕ}
    (cycle : MatchingRebaseCycleQueueInput loaded task.children free earlier choosePort)
    (view : MatchingRebaseCycleLoaded (poppedMatchingRebaseState s) loaded task.children free)
    (count : t.nr 82 = (rebasedMatchingCycleState loaded free).nr 82)
    (bytes : t.nm = (rebasedMatchingCycleState loaded free).nm)
    (keeps : matchingRebaseNodeKeeps s t) :
    let added := matchingRebaseCycleTaskPrefix task.children choosePort free ((loaded.nr 19 - 1) / 2)
    MatchingRebaseQueueEncoding (matchingRebaseQueueSnapshot t) (earlier ++ added) ∧
      matchingRebaseQueueWork added = task.children.registeredNodes ∧
      ∀ address, OutsideEarlierCycleWrites loaded free ((loaded.nr 19 - 1) / 2) address →
        t.nm address = loaded.nm address := by
  intro added
  obtain ⟨encoded, work, untouched⟩ := rebasedMatchingCycleState_queue cycle
  have loadedBase : loaded.nr 81 = s.nr 81 := by
    simpa [poppedMatchingRebaseState] using view.registers 81 (by decide)
  have base : (matchingRebaseQueueSnapshot t).nr 81 = (rebasedMatchingCycleState loaded free).nr 81 := by
    rw [rebasedMatchingCycleState_stackBase, loadedBase]
    simpa [matchingRebaseQueueSnapshot] using keeps 81 (by decide)
  have targetCount : (matchingRebaseQueueSnapshot t).nr 82 = (rebasedMatchingCycleState loaded free).nr 82 := by
    simpa [matchingRebaseQueueSnapshot] using count
  refine ⟨encoded.transport base targetCount (fun a _ _ => congrFun bytes a), work, ?_⟩
  intro a safe
  exact (congrFun bytes a).trans (untouched a safe)

/-- One complete node step preserves the original input and any other
natural data laid out below its mate table. -/
theorem MatchingRebaseCycleQueueInput.keepsBeforeMate {s loaded t : ArithmeticState}
    {earlier : List MatchingRebaseTask} {task : MatchingRebaseTask} {free : ℕ}
    {choosePort : MatchingMemberJob → ℕ}
    (cycle : MatchingRebaseCycleQueueInput loaded task.children free earlier choosePort)
    (view : MatchingRebaseCycleLoaded (poppedMatchingRebaseState s) loaded task.children free)
    (bytes : t.nm = (rebasedMatchingCycleState loaded free).nm)
    (mateBeforeWalk : s.nr 50 ≤ s.nr 80) (address : ℕ) (below : address < s.nr 50) :
    t.nm address = s.nm address := by
  have mate : loaded.nr 50 = s.nr 50 := by
    simpa [poppedMatchingRebaseState] using view.registers 50 (by decide)
  have map : loaded.nr 79 = s.nr 79 := by
    simpa [poppedMatchingRebaseState] using view.registers 79 (by decide)
  have m := cycle.matesBeforeMap
  have q := cycle.mapBeforeStack
  have r := cycle.stackBeforeRecord
  have safeLoaded : OutsideEarlierCycleWrites loaded free ((loaded.nr 19 - 1) / 2) address := by
    refine ⟨⟨.inl (by omega), .inl (by omega)⟩, by omega, ?_⟩
    intro i _ side
    omega
  have safeInput : outsideMatchingMemberScratch (poppedMatchingRebaseState s) address := by
    have belowMap : address < s.nr 79 := by omega
    have belowWalk : address < s.nr 80 := below.trans_le mateBeforeWalk
    simp [outsideMatchingMemberScratch, poppedMatchingRebaseState, belowMap, belowWalk]
  have modelKeeps := (rebasedMatchingCycleState_queue cycle).2.2 address safeLoaded
  exact (congrFun bytes address).trans (modelKeeps.trans (view.outside address safeInput))


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseQueueUpdate

/-! matching/MatchingRebaseLoadedQueue.lean -/
section RppSource_MatchingRebaseLoadedQueue
namespace VehicleRoutingSurvey.Routing

/-- Loading a live cycle leaves every one of the four words of its rows intact. -/
theorem MatchingRebaseCycleLoaded.childRow {s loaded : ArithmeticState}
    {children : MatchingMemberTree} {free requested owner : ℕ}
    (view : MatchingRebaseCycleLoaded s loaded children free)
    (input : MatchingRebaseCycleInput s children requested owner) (i : ℕ) (inside : i < children.arity) :
    matchingCycleChildAt loaded.nm (loaded.nr 18 + 4 * i) =
      matchingCycleChildAt s.nm (s.nm (s.nr 77 + s.nr 22) + 4 * i) := by
  let base := s.nm (s.nr 77 + s.nr 22)
  have readable : ∀ j < children.arity, ∀ w < 4,
      outsideMatchingMemberScratch s (base + 4 * j + w) := input.members.readable.2.2.1
  have same (w : ℕ) (within : w < 4) : loaded.nm (base + 4 * i + w) = s.nm (base + 4 * i + w) :=
    view.outside _ (readable i inside w within)
  have sameZero : loaded.nm (base + 4 * i) = s.nm (base + 4 * i) := by
    simpa only [Nat.add_zero] using same 0 (by decide)
  rw [view.recordBase]
  change matchingCycleChildAt loaded.nm (base + 4 * i) = matchingCycleChildAt s.nm (base + 4 * i)
  simp only [matchingCycleChildAt, sameZero, same 1 (by decide), same 2 (by decide), same 3 (by decide)]

/-- The membership traversal fills the owner table without changing the
stored child IDs, endpoint words, or existing queue entries. This transports
the ready-to-rematch frame to the exact machine state after that traversal. -/
theorem MatchingRebaseCycleQueueInput.of_loaded {s loaded : ArithmeticState}
    {children : MatchingMemberTree} {free owner : ℕ} {prior : List MatchingRebaseTask}
    {choosePort : MatchingMemberJob → ℕ}
    (input : MatchingRebaseCycleInput s children free owner)
    (view : MatchingRebaseCycleLoaded s loaded children free)
    (encoded : MatchingRebaseQueueEncoding s prior)
    (capacity : prior.length + children.arity ≤ s.nr 55)
    (matesBeforeMap : s.nr 50 + s.nr 55 ≤ s.nr 79)
    (mapBeforeStack : s.nr 79 + s.nr 55 ≤ s.nr 81)
    (walkBeforeStack : s.nr 80 + 3 * s.nr 55 ≤ s.nr 81)
    (stackBeforeRecord : s.nr 81 + 2 * s.nr 55 ≤ s.nm (s.nr 77 + s.nr 22))
    (endpoints : ∀ i < children.arity,
      let row := matchingCycleChildAt s.nm (s.nm (s.nr 77 + s.nr 22) + 4 * i)
      row.endpointA < s.nr 55 ∧ row.endpointB < s.nr 55)
    (exposed : choosePort ((children.jobs none)[free]'(by simpa only [children.jobs_length none] using input.inside)) =
      s.nr 29)
    (oriented : ∀ i < (loaded.nr 19 - 1) / 2,
      let left := matchingRebaseChildIndex (loaded.nr 19) free i false
      let right := matchingRebaseChildIndex (loaded.nr 19) free i true
      let lhs := (children.jobs none)[left]'(by
        rw [children.jobs_length none, ← view.count]
        exact Nat.mod_lt _ (by have := view.inside; omega))
      let rhs := (children.jobs none)[right]'(by
        rw [children.jobs_length none, ← view.count]
        exact Nat.mod_lt _ (by have := view.inside; omega))
      matchingRebasePorts loaded.nm (loaded.nr 79)
        (matchingCycleChildAt s.nm (s.nm (s.nr 77 + s.nr 22) + 4 * left)) =
        (choosePort lhs, choosePort rhs)) :
    MatchingRebaseCycleQueueInput loaded children free prior choosePort := by
  have size : loaded.nr 19 = (children.jobs none).length := view.count.trans (children.jobs_length none).symm
  refine ⟨view.queueEncoding encoded mapBeforeStack walkBeforeStack, input.members.proper.2.2.1,
    size, view.odd, view.inside, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [view.count, view.registers 55 (by decide)]
  · rwa [view.registers 50 (by decide), view.registers 55 (by decide), view.registers 79 (by decide)]
  · rwa [view.registers 79 (by decide), view.registers 55 (by decide), view.registers 81 (by decide)]
  · rwa [view.registers 81 (by decide), view.registers 55 (by decide), view.recordBase]
  · intro i hi
    have inside : i < children.arity := by simpa only [children.jobs_length none] using hi
    rw [view.childRow input i inside]
    exact congrArg Prod.snd ((matchingMemberJobRows input.members.encoded.2.1 i hi).1)
  · intro i hi
    have inside : i < children.arity := view.count ▸ hi
    dsimp only
    rw [view.childRow input i inside, view.registers 55 (by decide)]
    exact endpoints i inside
  · rw [view.registers 29 (by decide)]
    exact exposed
  · intro i hi
    dsimp only
    have inside : matchingRebaseChildIndex (loaded.nr 19) free i false < children.arity := by
      rw [← view.count]
      exact Nat.mod_lt _ (by have := view.inside; omega)
    rw [view.childRow input _ inside]
    exact oriented i hi


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseLoadedQueue

/-! matching/MatchingRebaseTaskOwner.lean -/
section RppSource_MatchingRebaseTaskOwner
namespace VehicleRoutingSurvey.Routing

theorem MatchingMemberJob.assignments_vertices (job : MatchingMemberJob) :
    job.assignments.map Prod.fst = job.tree.leaves := by
  cases kind : job.children <;>
    simp [MatchingMemberJob.assignments, MatchingMemberJob.tree, MatchingMemberTree.leaves,
      kind, List.map_map, Function.comp_def]





private theorem MatchingMemberJob.owner_of_assignment {job : MatchingMemberJob} {leaf owner : ℕ}
    (included : (leaf, owner) ∈ job.assignments) : owner = job.owner := by
  cases kind : job.children with
  | none =>
    have lone : (leaf, owner) = (job.representative, job.owner) := by
      simpa [MatchingMemberJob.assignments, kind] using included
    exact congrArg Prod.snd lone
  | some children =>
    rw [MatchingMemberJob.assignments, kind] at included
    obtain ⟨_, _, equal⟩ := List.mem_map.mp included
    exact (congrArg Prod.snd equal).symm

theorem MatchingMemberTree.rebaseOwnerOfLeaf (children : MatchingMemberTree) {port : ℕ}
    (belongs : port ∈ children.leaves) (distinct : (children.rootKeys.map Prod.fst).Nodup) :
    ∃ (free owner : ℕ), free < children.arity ∧ (port, owner) ∈ matchingMemberAssignments children ∧
      ∀ i, ∀ within : i < children.rootKeys.length, children.rootKeys[i].1 = owner ↔ i = free := by
  have verts : (matchingMemberAssignments children).map Prod.fst = children.leaves :=
    children.jobs_frontier_vertices none
  have hasOwner : port ∈ (matchingMemberAssignments children).map Prod.fst := by rwa [verts]
  obtain ⟨⟨leaf, owner⟩, recorded, same⟩ := List.mem_map.mp hasOwner
  change leaf = port at same
  subst leaf
  have chosen : (port, owner) ∈ (children.jobs none).flatMap MatchingMemberJob.assignments := recorded
  obtain ⟨job, member, assignment⟩ := List.mem_flatMap.mp chosen
  have represents : job.representative = owner :=
    ((children.jobs_owner none job member : job.owner = (none : Option ℕ).getD job.representative).symm).trans
      (MatchingMemberJob.owner_of_assignment assignment).symm
  have among : owner ∈ children.rootKeys.map Prod.fst := by
    rw [← children.jobs_rootKeys none, List.map_map]
    exact List.mem_map.mpr ⟨job, member, represents⟩
  obtain ⟨free, freeIn, found⟩ := List.mem_iff_getElem.mp among
  have rootIn : free < children.rootKeys.length := by simpa only [List.length_map] using freeIn
  have atRoot : children.rootKeys[free].1 = owner := by simpa only [List.getElem_map] using found
  refine ⟨free, owner, by simpa only [MatchingMemberTree.rootKeys_length] using rootIn, recorded, ?_⟩
  intro i inside
  constructor
  · intro equal
    have onMap : i < (children.rootKeys.map Prod.fst).length := by simpa only [List.length_map] using inside
    have value : (children.rootKeys.map Prod.fst)[i]'onMap =
        (children.rootKeys.map Prod.fst)[free]'freeIn := by
      simpa only [List.getElem_map] using equal.trans atRoot.symm
    exact (List.Nodup.getElem_inj_iff distinct).mp value
  · intro same
    subst i
    exact atRoot

/-- A valid member-root encoding plus a selected leaf determines all of
the cyclic rematch input parameters. -/
theorem MatchingRebaseCycleInput.of_memberRoot {s : ArithmeticState} {children : MatchingMemberTree}
    (root : MatchingMemberRoot s children) (odd : Odd children.arity)
    (port : s.nr 29 ∈ children.leaves) (distinct : (children.rootKeys.map Prod.fst).Nodup) :
    ∃ free owner, MatchingRebaseCycleInput s children free owner := by
  obtain ⟨free, owner, inCycle, found, unique⟩ := children.rebaseOwnerOfLeaf port distinct
  have verts : (matchingMemberAssignments children).map Prod.fst = children.leaves :=
    children.jobs_frontier_vertices none
  have assigned : ∀ p ∈ matchingMemberAssignments children, p.1 < s.nr 55 := by
    intro p h
    apply root.valid p.1
    rw [← verts]
    exact List.mem_map.mpr ⟨p, h, rfl⟩
  have leafBound : children.leaves.length ≤ s.nr 55 := by
    rw [← verts, List.length_map]
    exact MatchingMemberJob.boundedAssignments_length _ _ (verts.symm ▸ root.unique) assigned
  have counts := children.nodes_add_arity_le root.proper.2.2.1
  have arity := children.arity_le_nodes
  exact ⟨free, owner, ⟨root, odd, by omega, inCycle, found, unique⟩⟩

/-- The requested exposed vertex belongs to the exact physical child chosen by
the ownership witness. -/
theorem MatchingRebaseCycleInput.desired_in_freeChild {s : ArithmeticState} {children : MatchingMemberTree}
    {free owner : ℕ} (input : MatchingRebaseCycleInput s children free owner) :
    s.nr 29 ∈ ((children.jobs none)[free]'(by simpa only [children.jobs_length none] using input.inside)).tree.leaves := by
  let jobs := children.jobs none
  have found : (s.nr 29, owner) ∈ jobs.flatMap MatchingMemberJob.assignments := input.desired
  obtain ⟨job, belongs, assignment⟩ := List.mem_flatMap.mp found
  obtain ⟨i, within, atIndex⟩ := List.mem_iff_getElem.mp belongs
  have isOwner : owner = job.owner := MatchingMemberJob.owner_of_assignment assignment
  have code : job.owner = job.representative := children.jobs_owner none job belongs
  have withinJobs : i < (children.jobs none).length := within
  have onKeys : i < children.rootKeys.length := by
    simpa only [MatchingMemberTree.rootKeys_length, children.jobs_length none] using withinJobs
  have rows := matchingMemberJobRows (owner := none) input.members.encoded.2.1 i withinJobs
  have key : children.rootKeys[i].1 = jobs[i].representative :=
    (congrArg Prod.fst (input.members.encoded.2.1 i onKeys)).symm.trans (congrArg Prod.fst rows.1)
  have representative : children.rootKeys[i].1 = owner := by
    rw [key]
    exact (congrArg MatchingMemberJob.representative atIndex).trans (code.symm.trans isOwner.symm)
  have chosen := (input.uniquely i onKeys).mp representative
  subst i
  change s.nr 29 ∈ jobs[free].tree.leaves
  rw [atIndex, ← job.assignments_vertices]
  exact List.mem_map.mpr ⟨(s.nr 29, owner), assignment, rfl⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseTaskOwner

/-! matching/MatchingRebasePortOrientation.lean -/
section RppSource_MatchingRebasePortOrientation
namespace VehicleRoutingSurvey.Routing

private theorem MatchingMemberJob.assignment_of_leaf (job : MatchingMemberJob) {v : ℕ}
    (inside : v ∈ job.tree.leaves) : (v, job.owner) ∈ job.assignments := by
  cases kind : job.children with
  | none =>
    have equal : v = job.representative := by simpa [MatchingMemberJob.tree, MatchingMemberTree.leaves, kind] using inside
    simp [MatchingMemberJob.assignments, kind, equal]
  | some children =>
    have leaf : v ∈ children.leaves := by simpa [MatchingMemberJob.tree, MatchingMemberTree.leaves, kind] using inside
    rw [MatchingMemberJob.assignments, kind]
    exact List.mem_map.mpr ⟨v, leaf, rfl⟩

theorem MatchingRebaseCycleLoaded.ownerAtChild {s loaded : ArithmeticState}
    {children : MatchingMemberTree} {free v : ℕ}
    (view : MatchingRebaseCycleLoaded s loaded children free)
    (job : MatchingMemberJob) (listed : job ∈ children.jobs none) (inside : v ∈ job.tree.leaves) :
    loaded.nm (loaded.nr 79 + v) = job.representative := by
  have assignment : (v, job.owner) ∈ matchingMemberAssignments children :=
    List.mem_flatMap.mpr ⟨job, listed, job.assignment_of_leaf inside⟩
  exact (view.assignments _ assignment).trans (children.jobs_owner none job listed)

/-- The machine orders an undirected edge by the owner of its first endpoint.
For endpoints from different child subtrees this produces their directed ports. -/
theorem matchingRebasePorts_of_members {s loaded : ArithmeticState}
    {children : MatchingMemberTree} {free firstPort secondPort : ℕ}
    (view : MatchingRebaseCycleLoaded s loaded children free)
    (first second : MatchingMemberJob) (firstListed : first ∈ children.jobs none)
    (secondListed : second ∈ children.jobs none) (different : second.representative ≠ first.representative)
    (firstInside : firstPort ∈ first.tree.leaves) (secondInside : secondPort ∈ second.tree.leaves)
    (row : MatchingCycleChild) (key : row.representative = first.representative)
    (endpoints : (row.endpointA, row.endpointB) = (firstPort, secondPort) ∨
      (row.endpointA, row.endpointB) = (secondPort, firstPort)) :
    matchingRebasePorts loaded.nm (loaded.nr 79) row = (firstPort, secondPort) := by
  have firstOwner := view.ownerAtChild first firstListed firstInside
  have secondOwner := view.ownerAtChild second secondListed secondInside
  rcases endpoints with forward | reverse
  · have a := congrArg Prod.fst forward
    have b := congrArg Prod.snd forward
    change row.endpointA = firstPort at a
    change row.endpointB = secondPort at b
    simp [matchingRebasePorts, a, b, key, firstOwner]
  · have a := congrArg Prod.fst reverse
    have b := congrArg Prod.snd reverse
    change row.endpointA = secondPort at a
    change row.endpointB = firstPort at b
    simp [matchingRebasePorts, a, b, key, secondOwner, different]


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebasePortOrientation

/-! matching/MatchingRebasePortLabels.lean -/
section RppSource_MatchingRebasePortLabels
namespace VehicleRoutingSurvey.Routing

/-- The free child and the alternating pairs label distinct physical rows. -/
theorem matchingRebaseChildPorts_exists {α : Type*} {size free : ℕ} (inside : free < size) (odd : Odd size)
    (freePort : α) (pairPort : ℕ → Bool → α) :
    ∃ label : ℕ → α, label free = freePort ∧
      ∀ pair < (size - 1) / 2, ∀ second : Bool,
        label (matchingRebaseChildIndex size free pair second) = pairPort pair second := by
  classical
  obtain ⟨bounds, _, unique⟩ := matchingRebaseChildIndex_complete inside odd
  let assigned (i : ℕ) := ∃ pair < (size - 1) / 2, ∃ second : Bool,
    matchingRebaseChildIndex size free pair second = i
  let label (i : ℕ) := if i = free then freePort else
    if h : assigned i then pairPort (Classical.choose h) (Classical.choose (Classical.choose_spec h).2) else freePort
  refine ⟨label, by simp [label], ?_⟩
  intro pair within second
  let index := matchingRebaseChildIndex size free pair second
  have different : index ≠ free := (bounds pair within second).2
  have hasPair : assigned index := ⟨pair, within, second, rfl⟩
  change label index = _
  simp only [label, if_neg different, dif_pos hasPair]
  let prior := Classical.choose hasPair
  let priorSide := Classical.choose (Classical.choose_spec hasPair).2
  have priorIn : prior < (size - 1) / 2 := (Classical.choose_spec hasPair).1
  have same : matchingRebaseChildIndex size free prior priorSide = index :=
    Classical.choose_spec (Classical.choose_spec hasPair).2
  obtain ⟨left, right⟩ := unique prior priorIn pair within priorSide second same
  change pairPort prior priorSide = pairPort pair second
  rw [left, right]

/-- A port associated to each physical row defines a port function on child jobs
when the rows have distinct representatives. -/
theorem MatchingMemberTree.childPorts_of_index (children : MatchingMemberTree)
    (distinct : (children.rootKeys.map Prod.fst).Nodup) (label : ℕ → ℕ) :
    ∃ choosePort : MatchingMemberJob → ℕ,
      ∀ i, ∀ hi : i < (children.jobs none).length, choosePort ((children.jobs none)[i]) = label i := by
  classical
  let jobs := children.jobs none
  have unique : (jobs.map MatchingMemberJob.representative).Nodup := by
    rw [← children.jobs_rootKeys none, List.map_map] at distinct
    exact distinct
  let present (job : MatchingMemberJob) := ∃ j : Fin jobs.length, jobs[j.val]'j.isLt = job
  let choosePort (job : MatchingMemberJob) := if h : present job then label (Classical.choose h).val else 0
  refine ⟨choosePort, ?_⟩
  intro i hi
  have belongs : present jobs[i] := ⟨⟨i, hi⟩, rfl⟩
  change choosePort jobs[i] = label i
  simp only [choosePort, dif_pos belongs]
  let earlier := Classical.choose belongs
  have equalJobs : jobs[earlier.val]'earlier.isLt = jobs[i] := Classical.choose_spec belongs
  have eqReps : (jobs.map MatchingMemberJob.representative)[earlier.val]'(by simpa only [List.length_map] using earlier.isLt) =
      (jobs.map MatchingMemberJob.representative)[i]'(by simpa only [List.length_map] using hi) := by
    simpa only [List.getElem_map] using congrArg MatchingMemberJob.representative equalJobs
  have sameIndex : earlier.val = i := (List.Nodup.getElem_inj_iff unique).mp eqReps
  exact congrArg label sameIndex


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebasePortLabels

/-! matching/MatchingRebasePortSelection.lean -/
section RppSource_MatchingRebasePortSelection
namespace VehicleRoutingSurvey.Routing

theorem MatchingMemberTree.childReps_ne_of_distinct (tree : MatchingMemberTree)
    (distinct : (tree.rootKeys.map Prod.fst).Nodup) {i j : ℕ} {hi : i < (tree.jobs none).length}
    {hj : j < (tree.jobs none).length} (different : i ≠ j) :
    ((tree.jobs none)[i]).representative ≠ ((tree.jobs none)[j]).representative := by
  intro equal
  let representatives := (tree.jobs none).map MatchingMemberJob.representative
  have unique : representatives.Nodup := by
    rw [← tree.jobs_rootKeys none, List.map_map] at distinct
    exact distinct
  have hi' : i < representatives.length := by simpa [representatives] using hi
  have hj' : j < representatives.length := by simpa [representatives] using hj
  have same : representatives[i]'hi' = representatives[j]'hj' := by
    simpa only [representatives, List.getElem_map] using equal
  exact different ((List.Nodup.getElem_inj_iff unique).mp same)

/-- The pair-selection model chooses a port from each immediate child. The
undirected edge occurring in a row gives exactly the two ports for its pair. -/
theorem MatchingRebaseCycleLoaded.choosePorts {s loaded : ArithmeticState} {children : MatchingMemberTree}
    {free owner : ℕ} (view : MatchingRebaseCycleLoaded s loaded children free)
    (input : MatchingRebaseCycleInput s children free owner)
    (distinct : (children.rootKeys.map Prod.fst).Nodup)
    (edge : ℕ → ℕ × ℕ)
    (crossings : ∀ i < (loaded.nr 19 - 1) / 2,
      let left := matchingRebaseChildIndex (loaded.nr 19) free i false
      let right := matchingRebaseChildIndex (loaded.nr 19) free i true
      let a := (children.jobs none)[left]'(by
        rw [children.jobs_length none, ← view.count]
        exact Nat.mod_lt _ (Nat.zero_lt_of_lt view.inside))
      let b := (children.jobs none)[right]'(by
        rw [children.jobs_length none, ← view.count]
        exact Nat.mod_lt _ (Nat.zero_lt_of_lt view.inside))
      let row := matchingCycleChildAt s.nm (s.nm (s.nr 77 + s.nr 22) + 4 * left)
      (edge i).1 ∈ a.tree.leaves ∧ (edge i).2 ∈ b.tree.leaves ∧
        ((row.endpointA, row.endpointB) = edge i ∨ (row.endpointA, row.endpointB) = (edge i).swap)) :
    ∃ choosePort : MatchingMemberJob → ℕ,
      choosePort ((children.jobs none)[free]'(by simpa only [children.jobs_length none] using input.inside)) = s.nr 29 ∧
      (∀ job ∈ children.jobs none, choosePort job ∈ job.tree.leaves) ∧
      ∀ i < (loaded.nr 19 - 1) / 2,
        let left := matchingRebaseChildIndex (loaded.nr 19) free i false
        let right := matchingRebaseChildIndex (loaded.nr 19) free i true
        let a := (children.jobs none)[left]'(by
          rw [children.jobs_length none, ← view.count]
          exact Nat.mod_lt _ (Nat.zero_lt_of_lt view.inside))
        let b := (children.jobs none)[right]'(by
          rw [children.jobs_length none, ← view.count]
          exact Nat.mod_lt _ (Nat.zero_lt_of_lt view.inside))
        matchingRebasePorts loaded.nm (loaded.nr 79)
          (matchingCycleChildAt s.nm (s.nm (s.nr 77 + s.nr 22) + 4 * left)) = (choosePort a, choosePort b) := by
  let size := loaded.nr 19
  let jobs := children.jobs none
  let sideIndex (i : ℕ) (side : Bool) := matchingRebaseChildIndex size free i side
  have positive : 0 < size := Nat.zero_lt_of_lt view.inside
  have sizeEq : size = jobs.length := view.count.trans (children.jobs_length none).symm
  have jobIndex (i : ℕ) (side : Bool) : sideIndex i side < jobs.length := by
    rw [← sizeEq]
    exact Nat.mod_lt _ positive
  let sideJob (i : ℕ) (side : Bool) := jobs[sideIndex i side]'(jobIndex i side)
  let row (i : ℕ) := matchingCycleChildAt s.nm (s.nm (s.nr 77 + s.nr 22) + 4 * sideIndex i false)
  let pairPort (i : ℕ) (side : Bool) := if side then (edge i).2 else (edge i).1
  obtain ⟨indexed, atFree, atPair⟩ := matchingRebaseChildPorts_exists view.inside view.odd (s.nr 29) pairPort
  obtain ⟨choosePort, atJob⟩ := children.childPorts_of_index distinct indexed
  obtain ⟨_, everyIndex, indexUnique⟩ := matchingRebaseChildIndex_complete view.inside view.odd
  refine ⟨choosePort, (atJob free _).trans atFree, ?_, ?_⟩
  · intro job belongs
    obtain ⟨index, range, atIndex⟩ := List.mem_iff_getElem.mp belongs
    subst job
    rw [atJob index range]
    by_cases freeRow : index = free
    · subst index
      rw [atFree]
      exact input.desired_in_freeChild
    · have rangeSize : index < size := sizeEq.symm ▸ range
      obtain ⟨i, within, side, atSide⟩ := everyIndex index rangeSize freeRow
      have port : indexed index = pairPort i side := (congrArg indexed atSide.symm).trans (atPair i within side)
      rw [port]
      have ownSide : pairPort i side ∈ (sideJob i side).tree.leaves := by
        cases side
        · exact (crossings i within).1
        · exact (crossings i within).2.1
      have sameJob : sideJob i side = jobs[index]'range := by
        change jobs[sideIndex i side]'(jobIndex i side) = jobs[index]'range
        exact getElem_congr_idx (show sideIndex i side = index from atSide)
      exact sameJob ▸ ownSide
  · intro i within
    change matchingRebasePorts loaded.nm (loaded.nr 79) (row i) = (choosePort (sideJob i false), choosePort (sideJob i true))
    have pairDiff : sideIndex i true ≠ sideIndex i false := by
      intro same
      have sides := (indexUnique i within i within true false same).2
      cases sides
    have repDiff : (sideJob i true).representative ≠ (sideJob i false).representative :=
      children.childReps_ne_of_distinct distinct pairDiff
    have key : (row i).representative = (sideJob i false).representative :=
      congrArg Prod.fst (matchingMemberJobRows input.members.encoded.2.1 (sideIndex i false) (jobIndex i false)).1
    have orient := matchingRebasePorts_of_members view (sideJob i false) (sideJob i true)
      (List.getElem_mem _) (List.getElem_mem _) repDiff (crossings i within).1 (crossings i within).2.1
      (row i) key (crossings i within).2.2
    have left : choosePort (sideJob i false) = (edge i).1 :=
      (atJob _ (jobIndex i false)).trans (atPair i within false)
    have right : choosePort (sideJob i true) = (edge i).2 :=
      (atJob _ (jobIndex i true)).trans (atPair i within true)
    rw [left, right]
    exact orient

private theorem chosenMatchingRebaseTasks_sources (jobs : List MatchingMemberJob)
    (choosePort : MatchingMemberJob → ℕ) (inside : ∀ job ∈ jobs, choosePort job ∈ job.tree.leaves) :
    ∃ sources, List.Forall₂ MatchingRebaseTask.fromTopJob
      (jobs.filterMap (MatchingMemberJob.rebaseTask choosePort)) sources ∧ sources.Sublist jobs := by
  induction jobs with
  | nil => exact ⟨[], .nil, .slnil⟩
  | cons job tail ih =>
    obtain ⟨sources, same, usingTail⟩ := ih (fun child belongs => inside child (List.mem_cons_of_mem _ belongs))
    cases kind : job.children with
    | none =>
      refine ⟨sources, ?_, List.Sublist.cons job usingTail⟩
      simpa [MatchingMemberJob.rebaseTask, kind] using same
    | some children =>
      let task : MatchingRebaseTask := ⟨job.node, choosePort job, children⟩
      have correct : task.fromTopJob job := by
        refine ⟨rfl, kind, ?_⟩
        have member : choosePort job ∈ job.tree.leaves := inside job (by simp)
        simpa [task, MatchingMemberJob.tree, kind, MatchingMemberTree.leaves] using member
      refine ⟨job :: sources, ?_, List.Sublist.cons_cons job usingTail⟩
      simpa [MatchingMemberJob.rebaseTask, kind, task] using List.Forall₂.cons correct same

/-- Every queued descendant comes from a distinct physical child record, and
the pending descendants continue to occupy disjoint subsets of the old leaves. -/
theorem matchingRebaseCycleTaskPrefix_sources (children : MatchingMemberTree)
    (choosePort : MatchingMemberJob → ℕ) (free pairs : ℕ)
    (ports : ∀ job ∈ children.jobs none, choosePort job ∈ job.tree.leaves) :
    ∃ sources, List.Forall₂ MatchingRebaseTask.fromTopJob
      (matchingRebaseCycleTaskPrefix children choosePort free pairs) sources ∧
      sources.Subperm (children.jobs none) := by
  let rotated := (children.jobs none).rotate free
  let rows := rotated.take (2 * pairs + 1)
  have rotate := List.rotate_perm (children.jobs none) free
  have prefixRows : rows.Sublist rotated := List.take_sublist _ _
  obtain ⟨sources, relates, sourcesIn⟩ := chosenMatchingRebaseTasks_sources rows choosePort
    (fun job belongs => ports job (rotate.mem_iff.mp (prefixRows.subset belongs)))
  exact ⟨sources, relates, (sourcesIn.trans prefixRows).subperm.trans rotate.subperm⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebasePortSelection

/-! matching/MatchingRebaseGeometry.lean -/
section RppSource_MatchingRebaseGeometry
namespace VehicleRoutingSurvey.Routing

/-- The input row located by the executable membership search is unique. -/
theorem MatchingRebaseCycleLoaded.free_eq {s loaded : ArithmeticState} {children : MatchingMemberTree}
    {actual requested owner : ℕ} (view : MatchingRebaseCycleLoaded s loaded children actual)
    (input : MatchingRebaseCycleInput s children requested owner) : actual = requested := by
  have onKeys : requested < children.rootKeys.length := by simpa using input.inside
  have key := congrArg Prod.fst (input.members.encoded.2.1 requested onKeys)
  have desired : children.rootKeys[requested].1 = owner := (input.uniquely requested onKeys).2 rfl
  have wanted := view.assignments _ input.desired
  have atRow := view.childRow input requested input.inside
  have keyLoaded := (congrArg MatchingCycleChild.representative atRow).trans (key.trans desired)
  have within : requested < loaded.nr 19 := view.count.symm ▸ input.inside
  apply ((view.finds requested within).mp ?_).symm
  rw [view.registers 29 (by decide)]
  exact keyLoaded.trans wanted.symm



/-- All original endpoints of the raw rows are inside the compact matching dimension. -/
theorem MatchingRebaseCycleGeometry.endpoints {s : ArithmeticState} {children : MatchingMemberTree}
    (geom : MatchingRebaseCycleGeometry s children)
    (valid : ∀ v ∈ children.leaves, v < s.nr 55) (i : ℕ) (inside : i < children.arity) :
    let row := matchingCycleChildAt s.nm (s.nm (s.nr 77 + s.nr 22) + 4 * i)
    row.endpointA < s.nr 55 ∧ row.endpointB < s.nr 55 := by
  intro row
  have inJobs : i < (children.jobs none).length := by rwa [children.jobs_length none]
  have subset (job : MatchingMemberJob) (listed : job ∈ children.jobs none) (v : ℕ)
      (belongs : v ∈ job.tree.leaves) : v ∈ children.leaves := by
    have inAssigned : v ∈ job.assignments.map Prod.fst := by rwa [job.assignments_vertices]
    obtain ⟨p, hp, atV⟩ := List.mem_map.mp inAssigned
    rw [← children.jobs_frontier_vertices none]
    exact List.mem_map.mpr ⟨p, List.mem_flatMap.mpr ⟨job, listed, hp⟩, atV⟩
  have first := valid _ (subset _ (List.getElem_mem _) _ (geom.source i inJobs))
  have second := valid _ (subset _ (List.getElem_mem _) _ (geom.target i inJobs))
  rcases geom.row i inside with forward | backward
  · have a : row.endpointA = (geom.edge i).1 := congrArg Prod.fst forward
    have b : row.endpointB = (geom.edge i).2 := congrArg Prod.snd forward
    rw [a, b]
    exact ⟨first, second⟩
  · have a : row.endpointA = (geom.edge i).2 := congrArg Prod.fst backward
    have b : row.endpointB = (geom.edge i).1 := congrArg Prod.snd backward
    rw [a, b]
    exact ⟨second, first⟩

/-- Reading the recorded edge after the free child supplies the oriented witnesses
required by the RAM port selector. -/
theorem MatchingRebaseCycleGeometry.ports {s loaded : ArithmeticState} {children : MatchingMemberTree}
    {free owner : ℕ} (geom : MatchingRebaseCycleGeometry s children)
    (input : MatchingRebaseCycleInput s children free owner) (view : MatchingRebaseCycleLoaded s loaded children free)
    (distinct : (children.rootKeys.map Prod.fst).Nodup) :
    ∃ choosePort : MatchingMemberJob → ℕ,
      choosePort ((children.jobs none)[free]'(by simpa only [children.jobs_length none] using input.inside)) = s.nr 29 ∧
      (∀ job ∈ children.jobs none, choosePort job ∈ job.tree.leaves) ∧
      ∀ i < (loaded.nr 19 - 1) / 2,
        let left := matchingRebaseChildIndex (loaded.nr 19) free i false
        let right := matchingRebaseChildIndex (loaded.nr 19) free i true
        let a := (children.jobs none)[left]'(by
          rw [children.jobs_length none, ← view.count]
          exact Nat.mod_lt _ (Nat.zero_lt_of_lt view.inside))
        let b := (children.jobs none)[right]'(by
          rw [children.jobs_length none, ← view.count]
          exact Nat.mod_lt _ (Nat.zero_lt_of_lt view.inside))
        matchingRebasePorts loaded.nm (loaded.nr 79)
          (matchingCycleChildAt s.nm (s.nm (s.nr 77 + s.nr 22) + 4 * left)) = (choosePort a, choosePort b) := by
  let length := loaded.nr 19
  let left (i : ℕ) := matchingRebaseChildIndex length free i false
  apply view.choosePorts input distinct (fun i => geom.edge (left i))
  intro i _
  have lengthEq : (children.jobs none).length = length := (children.jobs_length none).trans view.count.symm
  have positive : 0 < length := Nat.zero_lt_of_lt view.inside
  have inJobs : left i < (children.jobs none).length := by rw [lengthEq]; exact Nat.mod_lt _ positive
  have successor : (left i + 1) % (children.jobs none).length = matchingRebaseChildIndex length free i true := by
    rw [lengthEq]
    change (((free + (2 * i + 1)) % length) + 1) % length = (free + (2 * i + 2)) % length
    rw [Nat.mod_add_mod]
    exact congrArg (· % length) (by omega)
  have sameJob :
      (children.jobs none)[(left i + 1) % (children.jobs none).length]'(Nat.mod_lt _ (by omega)) =
        (children.jobs none)[matchingRebaseChildIndex length free i true]'(by rw [lengthEq]; exact Nat.mod_lt _ positive) :=
    getElem_congr_idx successor
  exact ⟨geom.source _ inJobs, sameJob ▸ geom.target _ inJobs,
    geom.row _ (by rw [← children.jobs_length none]; exact inJobs)⟩

/-- The RAM writes precisely the oriented original edge of this archive
row, independently of the order of its two stored endpoint words. -/
theorem MatchingRebaseCycleGeometry.originalPair {s loaded : ArithmeticState} {children : MatchingMemberTree}
    {free owner : ℕ} (geom : MatchingRebaseCycleGeometry s children)
    (input : MatchingRebaseCycleInput s children free owner) (view : MatchingRebaseCycleLoaded s loaded children free)
    (distinct : (children.rootKeys.map Prod.fst).Nodup) (i : ℕ) (within : i < (loaded.nr 19 - 1) / 2) :
    matchingRebaseOriginalPair loaded free i = geom.edge (matchingRebaseChildIndex children.arity free i false) := by
  let jobs := children.jobs none
  let left := matchingRebaseChildIndex (loaded.nr 19) free i false
  let right := matchingRebaseChildIndex (loaded.nr 19) free i true
  have length : jobs.length = loaded.nr 19 := (children.jobs_length none).trans view.count.symm
  have pos := Nat.zero_lt_of_lt view.inside
  have lhs : left < jobs.length := by rw [length]; exact Nat.mod_lt _ pos
  have rhs : right < jobs.length := by rw [length]; exact Nat.mod_lt _ pos
  have successor : (left + 1) % jobs.length = right := by
    rw [length]
    change (((free + (2 * i + 1)) % loaded.nr 19) + 1) % loaded.nr 19 = (free + (2 * i + 2)) % loaded.nr 19
    rw [Nat.mod_add_mod]
    exact congrArg (· % loaded.nr 19) (by omega)
  have same : jobs[(left + 1) % jobs.length]'(Nat.mod_lt _ (by omega)) = jobs[right]'rhs := getElem_congr_idx successor
  have diff : right ≠ left := by
    intro eq
    have side := ((matchingRebaseChildIndex_complete view.inside view.odd).2.2 i within i within true false eq).2
    cases side
  have distinctJobs : jobs[right].representative ≠ jobs[left].representative :=
    children.childReps_ne_of_distinct distinct diff
  have inside : left < children.arity := by rw [← children.jobs_length none]; exact lhs
  have key := congrArg Prod.fst (matchingMemberJobRows (owner := none) input.members.encoded.2.1 left lhs).1
  change matchingRebasePorts loaded.nm (loaded.nr 79) (matchingCycleChildAt loaded.nm (loaded.nr 18 + 4 * left)) = _
  rw [view.childRow input _ inside, ← view.count]
  exact matchingRebasePorts_of_members view jobs[left] jobs[right] (List.getElem_mem _) (List.getElem_mem _)
    distinctJobs (geom.source left lhs) (same ▸ geom.target left lhs) _ key (geom.row left inside)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseGeometry

/-! matching/MatchingCycleRecordOrder.lean -/
section RppSource_MatchingCycleRecordOrder
namespace VehicleRoutingSurvey.Routing











/-- Distinct allocated IDs have disjoint physical record rows. -/
theorem MatchingCycleRecordOrder.disjoint {s : ArithmeticState} (order : MatchingCycleRecordOrder s)
    {left right address : ℕ} (leftLive : 0 < left ∧ left < s.nr 76) (rightLive : 0 < right ∧ right < s.nr 76)
    (different : left ≠ right) (onLeft : matchingCycleRecordStart s left ≤ address)
    (beforeEnd : address < matchingCycleRecordEnd s left) :
    address < matchingCycleRecordStart s right ∨ matchingCycleRecordEnd s right ≤ address := by
  rcases Nat.lt_or_gt_of_ne different with before | after
  · exact .inl (beforeEnd.trans_le (order.ordered _ _ leftLive.1 before rightLive.2))
  · exact .inr ((order.ordered _ _ rightLive.1 after leftLive.2).trans onLeft)






end VehicleRoutingSurvey.Routing
end RppSource_MatchingCycleRecordOrder

/-! matching/MatchingRebaseArchive.lean -/
section RppSource_MatchingRebaseArchive
namespace VehicleRoutingSurvey.Routing













def matchingRebaseLayoutRegisters : List ℕ := [50, 55, 68, 76, 77, 78, 79, 80, 81]

/-- Recover a typed node and its original edge witnesses by reading only
the subset of the archived registry owned by this pending subtree. -/
def MatchingArchivedCycle.restore {base s : ArithmeticState} {n : ℕ} {c : MatchingMemberTree}
    (arch : MatchingArchivedCycle base n c)
    (fixed : ∀ r ∈ matchingRebaseLayoutRegisters, s.nr r = base.nr r)
    (bytes : ∀ a, matchingRebaseRecordArea base (n :: c.registryIds) a → s.nm a = base.nm a) :
    MatchingMemberRoot (matchingRebaseNodeState s n) c ×'
      MatchingRebaseCycleGeometry (matchingRebaseNodeState s n) c := by
  let tree := MatchingMemberTree.blossom 0 n c .nil
  let region := matchingRebaseRecordArea base (n :: c.registryIds)
  have fresh (a : ℕ) (h : region a ∧ outsideMatchingMemberScratch base a) : s.nm a = base.nm a :=
    bytes a h.1
  have keep (r : ℕ) (inside : r ∈ matchingRebaseLayoutRegisters := by decide) : s.nr r = base.nr r := fixed r inside
  have scratch : outsideMatchingMemberScratch s = outsideMatchingMemberScratch base := by
    funext a
    simp only [outsideMatchingMemberScratch, keep 55, keep 79, keep 80]
  have old : MatchingMemberRoot (matchingRebaseNodeState base n) c := arch.members
  have enc : tree.encoded base.nm (base.nr 77) (base.nr 78) := by
    simpa [tree, matchingRebaseNodeState] using old.encoded
  have above : tree.recordsAbove base.nm (base.nr 77) (base.nr 80 + 3 * base.nr 55) := by
    simpa [tree, matchingRebaseNodeState] using old.above
  have valid : ∀ v ∈ c.leaves, v < base.nr 55 := by simpa [matchingRebaseNodeState] using old.valid
  have separate : base.nr 79 + base.nr 55 ≤ base.nr 80 := by simpa [matchingRebaseNodeState] using old.separated
  have newRoot : MatchingMemberRoot (matchingRebaseNodeState s n) c := by
    refine ⟨?_, ?_, ?_, ?_, old.unique, ?_, ?_⟩
    · simpa [matchingRebaseNodeState] using old.proper
    · simpa [tree, matchingRebaseNodeState, keep 77, keep 78] using
        (MatchingMemberTree.encoded_congr enc arch.footprint fresh)
    · have readable := MatchingMemberTree.readable_after_move arch.footprint bytes
      have same : outsideMatchingMemberScratch (matchingRebaseNodeState s n) = outsideMatchingMemberScratch base := by
        funext a
        simp [outsideMatchingMemberScratch, matchingRebaseNodeState, keep 55, keep 79, keep 80]
      rw [same]
      simpa [matchingRebaseNodeState, keep 77, keep 78] using readable
    · simpa [tree, matchingRebaseNodeState, keep 77, keep 80, keep 55] using
        (MatchingMemberTree.recordsAbove_after_move arch.footprint above fresh)
    · simpa [matchingRebaseNodeState, keep 55] using valid
    · simpa [matchingRebaseNodeState, keep 79, keep 55, keep 80] using separate
  refine ⟨newRoot, ⟨arch.geometry.edge, arch.geometry.source, arch.geometry.target, ?_⟩⟩
  intro i hi
  have header := bytes _ arch.footprint.1.1
  have row (w : ℕ) (hw : w < 4) := bytes _ (arch.footprint.2.2.1 i hi w hw).1
  simpa [matchingRebaseNodeState, keep 77, header, matchingCycleChildAt, row 2 (by decide),
    row 3 (by decide)] using arch.geometry.row i hi


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseArchive

/-! matching/MatchingAugmentHandler.lean -/
section RppSource_MatchingAugmentHandler
namespace VehicleRoutingSurvey.Routing

theorem finishMatchingAugmentationBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    let t := {s with pc := 2, nr := Function.update (Function.update s.nr 1 0) 33 0}
    BlockRuns finishMatchingAugmentationBlock 2 s t ∧ t.halted = false := by
  dsimp only
  refine ⟨BlockRuns.of_running_exit ?_ running rfl, running⟩
  simp [finishMatchingAugmentationBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']

/-- The dual sweep leaves the emitted crossings and all original matching bytes intact. -/
theorem prepareMatchingAugmentationBlock_correct {k : ℕ} {rows : List (Fin k × Fin k)}
    {s emitted : ArithmeticState} {emitSteps : ℕ}
    (emit : BlockRuns writeAugmentationCrossingsBlock emitSteps s emitted)
    (running : emitted.halted = false) (ready : AugmentationCrossingsReady rows s emitted)
    (cost : emitSteps ≤ 17 * k + 21) (dimension : s.nr 55 = k) (one : s.nr 9 = 1)
    (rolesBelow : s.nr 51 + k ≤ s.nr 86) (repsBelow : s.nr 57 + k ≤ s.nr 86)
    (nodesBelow : s.nr 74 + k ≤ s.nr 86) (repValid : ∀ i < k, s.nm (s.nr 57 + i) < k) :
    ∃ t ticks, ticks ≤ 48 * k + 27 ∧ BlockRuns prepareMatchingAugmentationBlock ticks s t ∧
      t.halted = false ∧ t.nm = emitted.nm ∧ t.nr 86 = s.nr 86 ∧ t.nr 87 = rows.length ∧
      t.nr 9 = 1 ∧ t.nr 55 = k ∧ AugmentationCrossingArray t.nm (t.nr 86) rows ∧
      t.rr 1 = s.rr 1 ∧ t.rr 15 = s.rr 15 + s.rr 1 ∧
      t.rm = iterateBlossomDuals {s with rm := advancedEffectiveMemory s} k := by
  let input := {emitted with pc := 0}
  have oneAt : input.nr 9 = 1 := (ready.fixed 9 (by decide)).trans one
  have sizeAt : input.nr 55 = k := (ready.fixed 55 (by decide)).trans dimension
  obtain ⟨out, dualTicks, bound, dual, live, natural, delta, total, _, fixed, memory⟩ :=
    advanceMatchingEventDuals_spec input rfl running oneAt
  rw [sizeAt] at bound memory
  have base : out.nr 86 = s.nr 86 := (fixed 86 (by decide)).trans ready.base
  have count : out.nr 87 = rows.length := (fixed 87 (by decide)).trans ready.count
  have bytes : AugmentationCrossingArray out.nm (out.nr 86) rows := by rw [natural, base]; exact ready.array
  have nr (r : ℕ) (safe : r ∉ [3, 4, 5, 6, 7, 15, 16, 17, 18, 19, 87] := by decide) :
      input.nr r = s.nr r := ready.fixed r safe
  have before (a : ℕ) (low : a < s.nr 86) : input.nm a = s.nm a := ready.natural a (Or.inl low)
  have oneDelta : input.rr 1 = s.rr 1 := congrFun ready.realRegisters 1
  have oldMemory : input.rm = s.rm := ready.realMemory
  have effective : advancedEffectiveMemory input = advancedEffectiveMemory s := by
    funext a
    simp only [advancedEffectiveMemory, nr 62, nr 55]
    by_cases inside : s.nr 62 ≤ a ∧ a < s.nr 62 + s.nr 55
    · have boundIndex : a - s.nr 62 < k := by omega
      have rep := repValid (a - s.nr 62) boundIndex
      have atRep := before (s.nr 57 + (a - s.nr 62)) (by omega)
      have atRole := before (s.nr 51 + s.nm (s.nr 57 + (a - s.nr 62))) (by omega)
      simp [inside, effectivePotentialAfterDelta, effectiveRoleAt, nr 51, nr 57, nr 62,
        atRep, atRole, oldMemory, oneDelta]
    · simp [inside, oldMemory]
  have sweeps (i : ℕ) (hi : i ≤ k) :
      iterateBlossomDuals {input with rm := advancedEffectiveMemory input} i =
        iterateBlossomDuals {s with rm := advancedEffectiveMemory s} i := by
    induction i with
    | zero => exact effective
    | succ i ih =>
      have prior := ih (by omega)
      simp only [iterateBlossomDuals, modifyBlossomDualAt, blossomDualAfterDelta]
      change (if blossomNodeAt input i = 0 ∨ blossomRoleAt input i = 0 then _ else _) = _
      simp [blossomRoleAt, blossomNodeAt, nr 51, nr 74, nr 75,
        before (s.nr 51 + i) (by omega), before (s.nr 74 + i) (by omega), prior, oneDelta] <;> rfl
  refine ⟨relocateState writeAugmentationCrossingsBlock.length out, emitSteps + dualTicks, by omega,
    emit.append dual, live, natural, base, count, (fixed 9 (by decide)).trans oneAt,
    (fixed 55 (by decide)).trans sizeAt, bytes, delta.trans ?_, total.trans ?_, ?_⟩
  · exact congrFun ready.realRegisters 1
  · exact congrArg₂ (· + ·) (congrFun ready.realRegisters 15) (congrFun ready.realRegisters 1)
  · exact memory.trans (sweeps k le_rfl)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentHandler

/-! matching/MatchingAugmentCrossingSemantics.lean -/
section RppSource_MatchingAugmentCrossingSemantics
namespace VehicleRoutingSurvey.Routing

theorem AugmentationInstallLayout.transport {k : ℕ} {s t : ArithmeticState}
    (layout : AugmentationInstallLayout k s) (fixed : ∀ r ∈ [50, 57, 74, 81, 86, 89], t.nr r = s.nr r) :
    AugmentationInstallLayout k t := by
  obtain ⟨mates, map, nodes, pairs, work⟩ := layout
  exact ⟨by simpa only [fixed 50 (by decide), fixed 57 (by decide)] using mates,
    by simpa only [fixed 57 (by decide), fixed 74 (by decide)] using map,
    by simpa only [fixed 74 (by decide), fixed 86 (by decide)] using nodes,
    by simpa only [fixed 86 (by decide), fixed 89 (by decide)] using pairs,
    by simpa only [fixed 89 (by decide), fixed 81 (by decide)] using work⟩











end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentCrossingSemantics

/-! matching/MatchingAugmentComplete.lean -/
section RppSource_MatchingAugmentComplete
namespace VehicleRoutingSurvey.Routing

/-- The actual crossing-installation and recursive-rebase bytecode, with
the queue invariant supplied by the live blossom representation. -/
theorem applyMatchingAugmentationCrossingsBlock_correct {k : ℕ} {s : ArithmeticState}
    (rows : List (Fin k × Fin k)) (entry : s.pc = 0) (running : s.halted = false)
    (dimension : s.nr 55 = k) (count : s.nr 87 = rows.length)
    (pairs : AugmentationCrossingArray s.nm (s.nr 86) rows) (capacity : 2 * rows.length ≤ k)
    (layout : AugmentationInstallLayout k (augmentationCrossingSeed s k))
    (originalMap : ∀ i < k, s.nm (s.nr 57 + i) < k)
    {frame : List MatchingRebaseTask → ArithmeticState → Prop} (queue : MatchingRebaseQueueInterface frame)
    (initialTasks : ∀ prepared, AugmentationPreRebaseReady rows s prepared →
      ∃ jobs, frame jobs (matchingRebaseQueueSnapshot prepared) ∧ matchingRebaseQueueWork jobs ≤ k) :
    ∃ (t : ArithmeticState) (steps : ℕ), BlockRuns applyMatchingAugmentationCrossingsBlock steps s t ∧
      t.halted = false ∧ steps ≤ (35 * k + 12) + (k * (153 * k + 59) + 2) ∧
      t.nr 82 = 0 ∧ frame [] (matchingRebaseQueueSnapshot t) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27,
        28, 29, 43, 44, 46, 47, 49, 81, 82, 87, 95] → t.nr r = s.nr r := by
  obtain ⟨prepared, setupTicks, setup, preparedLive, setupBound, ready⟩ :=
    prepareMatchingAugmentationRebaseBlock_correct rows entry running dimension count pairs capacity layout originalMap
  obtain ⟨jobs, encoded, work⟩ := initialTasks prepared ready
  let start := {prepared with pc := 0}
  have startFrame : frame jobs (matchingRebaseQueueSnapshot start) := by
    simpa only [start, matchingRebaseQueueSnapshot] using encoded
  have startSize : start.nr 55 = k := (ready.fixed 55 (by decide)).trans dimension
  obtain ⟨r, workTicks, workBound, rebase, rLive, done, closed, real, reals, fixed⟩ :=
    rebaseMatchingQueuedNodesBlock_correct queue startFrame (startSize.symm ▸ work)
      rfl preparedLive ready.one ready.zero
  let out := relocateState prepareMatchingAugmentationRebaseBlock.length r
  have ran : BlockRuns applyMatchingAugmentationCrossingsBlock (setupTicks + workTicks) s out := by
    rw [applyMatchingAugmentationCrossingsBlock_split]
    exact setup.append rebase
  refine ⟨out, _, ran, rLive, ?_, done, ?_, real.trans ready.realMemory, reals.trans ready.realRegisters, ?_⟩
  · rw [startSize] at workBound
    omega
  · simpa only [out, relocateState, matchingRebaseQueueSnapshot] using closed
  · intro p allowed
    have a : p ≠ 43 := by simp at allowed; omega
    have b : p ∉ [0, 6, 7, 10, 11, 12, 13, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27, 28,
        29, 46, 47, 49, 82, 87, 95] := by simp at allowed ⊢; omega
    have c : p ∉ [0, 6, 9, 12, 13, 14, 15, 22, 26, 44, 81, 82] := by simp at allowed ⊢; omega
    exact (fixed p a b).trans (ready.fixed p c)

set_option maxRecDepth 16384 in
theorem prepareMatchingAugmentationBlock_preserves {s t : ArithmeticState} {ticks : ℕ}
    (ran : BlockRuns prepareMatchingAugmentationBlock ticks s t) :
    ∀ r, r ∉ [0, 3, 4, 5, 6, 7, 10, 11, 12, 14, 15, 16, 17, 18, 19, 87] → t.nr r = s.nr r := by
  intro r safe
  rw [← ran.run]
  exact arithmeticRun_keeps_from_destination_list _ (by decide) safe s ticks

set_option maxRecDepth 16384 in
/-- Compose crossing emission, the dual sweep, crossing installation, all
recursive rebasing, and stage exit. The final queue is empty. -/
theorem matchingAugmentationHandlerBlock_correct {k : ℕ} {s emitted : ArithmeticState}
    {rows : List (Fin k × Fin k)} {emitSteps : ℕ}
    (emit : BlockRuns writeAugmentationCrossingsBlock emitSteps s emitted)
    (emittedLive : emitted.halted = false) (emittedRows : AugmentationCrossingsReady rows s emitted)
    (emitBound : emitSteps ≤ 17 * k + 21) (dimension : s.nr 55 = k) (one : s.nr 9 = 1)
    (rolesBelow : s.nr 51 + k ≤ s.nr 86) (repsBelow : s.nr 57 + k ≤ s.nr 86)
    (nodesBelow : s.nr 74 + k ≤ s.nr 86) (originalMap : ∀ i < k, s.nm (s.nr 57 + i) < k)
    (layout : AugmentationInstallLayout k (augmentationCrossingSeed s k))
    {frame : List MatchingRebaseTask → ArithmeticState → Prop} (queue : MatchingRebaseQueueInterface frame)
    (initialTasks : ∀ dual ticks prepared, BlockRuns prepareMatchingAugmentationBlock ticks s dual →
      AugmentationPreRebaseReady rows {dual with pc := 0} prepared →
      ∃ jobs, frame jobs (matchingRebaseQueueSnapshot prepared) ∧ matchingRebaseQueueWork jobs ≤ k) :
    ∃ (t rebased : ArithmeticState) (steps : ℕ), BlockRuns matchingAugmentationHandlerBlock steps s t ∧
      t.halted = false ∧ steps + (34 * k + 61) ≤ 512 * (k ^ 2 + 1) ∧
      t.nr 1 = 0 ∧ t.nr 33 = 0 ∧ t.nr 82 = 0 ∧
      frame [] (matchingRebaseQueueSnapshot rebased) ∧ t.nm = rebased.nm ∧ t.rr 15 = s.rr 15 + s.rr 1 ∧
      t.rm = iterateBlossomDuals {s with rm := advancedEffectiveMemory s} k ∧
      ∀ r, r ≥ 100 → t.nr r = s.nr r := by
  obtain ⟨dual, firstTicks, firstBound, first, dualLive, sameMemory, _, dualCount, _, dualSize, dualRows,
    _, time, dualMemory⟩ := prepareMatchingAugmentationBlock_correct emit emittedLive emittedRows emitBound dimension one
      rolesBelow repsBelow nodesBelow originalMap
  let start := {dual with pc := 0}
  have kept (r : ℕ) (safe : r ∉ [0, 3, 4, 5, 6, 7, 10, 11, 12, 14, 15, 16, 17, 18, 19, 87]) :
      start.nr r = s.nr r := prepareMatchingAugmentationBlock_preserves first r safe
  have shape (r : ℕ) (safe : r ∈ [50, 57, 74, 81, 86, 89]) :
      (augmentationCrossingSeed start k).nr r = (augmentationCrossingSeed s k).nr r := by
    by_cases base : r = 81
    · subst r
      simp [augmentationCrossingSeed, kept 80 (by decide)]
    · have n82 : r ≠ 82 := by simp at safe; omega
      have stable : r ∉ [0, 3, 4, 5, 6, 7, 10, 11, 12, 14, 15, 16, 17, 18, 19, 87] := by
        simp at safe ⊢
        omega
      simp [augmentationCrossingSeed, Function.update_of_ne base, Function.update_of_ne n82, kept r stable]
  have nextMap (i : ℕ) (inside : i < k) : start.nm (start.nr 57 + i) < k := by
    change dual.nm (start.nr 57 + i) < k
    rw [sameMemory, kept 57 (by decide), emittedRows.natural _ (.inl (by omega))]
    exact originalMap i inside
  obtain ⟨rebased, nextTicks, installed, rebasedLive, nextBound, done, finalFrame, memory, reals, fixed⟩ :=
    applyMatchingAugmentationCrossingsBlock_correct rows (s := start) rfl dualLive dualSize dualCount dualRows
      emittedRows.capacity (layout.transport shape) nextMap queue
      (fun prepared ready => initialTasks dual firstTicks prepared first ready)
  let close := {rebased with pc := 0}
  have final := finishMatchingAugmentationBlock_correct (s := close) rfl rebasedLive
  have ran := (first.append installed).append final.1
  refine ⟨_, rebased, _, ran, final.2, ?_, ?_, ?_, done, finalFrame, rfl, ?_, memory.trans dualMemory, ?_⟩
  · have square : k ≤ k ^ 2 := by
      by_cases empty : k = 0
      · simp [empty]
      · simpa only [pow_two, Nat.mul_one] using Nat.mul_le_mul_left k (show 1 ≤ k by omega)
    have queueTerm : k * (153 * k + 59) = 153 * k ^ 2 + k * 59 := by ring
    rw [queueTerm] at nextBound
    omega
  · simp [relocateState]
  · simp [relocateState]
  · exact (congrFun reals 15).trans time
  · intro r high
    change Function.update (Function.update rebased.nr 1 0) 33 0 r = s.nr r
    rw [Function.update_of_ne (by omega : r ≠ 33), Function.update_of_ne (by omega : r ≠ 1)]
    exact (fixed r (by simp; omega)).trans (kept r (by simp; omega))

set_option maxRecDepth 16384 in
/-- The augmentation leaves the search-loop and stage counters, the registry
layout, and the caller's saved registers untouched. -/
theorem matchingAugmentationHandlerBlock_preserves {s t : ArithmeticState} {steps : ℕ}
    (ran : BlockRuns matchingAugmentationHandlerBlock steps s t) :
    ∀ r, r ∉ [0, 1, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23, 24, 25,
      26, 27, 28, 29, 33, 43, 44, 46, 47, 49, 81, 82, 87, 95] → t.nr r = s.nr r := by
  intro r safe
  rw [← ran.run]
  exact arithmeticRun_keeps_from_destination_list _ (by decide) safe s steps

end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentComplete

/-! matching/MatchingRebaseQueuePop.lean -/
section RppSource_MatchingRebaseQueuePop
namespace VehicleRoutingSurvey.Routing

/-- Decode the last task of the real work stack and select its unique
immediate child containing the specified exposed original vertex. -/
theorem MatchingRebaseQueueEncoding.nextCycle {s : ArithmeticState}
    {earlier : List MatchingRebaseTask} {task : MatchingRebaseTask}
    (encoded : MatchingRebaseQueueEncoding s (earlier ++ [task]))
    (registered : MatchingMemberRoot {s with nr := Function.update s.nr 22 task.node} task.children)
    (odd : Odd task.children.arity) (selected : task.port ∈ task.children.leaves)
    (distinct : (task.children.rootKeys.map Prod.fst).Nodup) :
    MatchingRebaseQueueEncoding (poppedMatchingRebaseState s) earlier ∧
      ∃ free owner, MatchingRebaseCycleInput (poppedMatchingRebaseState s) task.children free owner := by
  obtain ⟨smaller, node, port⟩ := encoded.pop
  let registeredState := {s with nr := Function.update s.nr 22 task.node}
  let popped := poppedMatchingRebaseState s
  have fixed (r : ℕ) (n22 : r ≠ 22) (n29 : r ≠ 29) (n82 : r ≠ 82) : popped.nr r = registeredState.nr r := by
    simp [popped, poppedMatchingRebaseState, registeredState, Function.update_of_ne n22,
      Function.update_of_ne n29, Function.update_of_ne n82]
  have r55 := fixed 55 (by decide) (by decide) (by decide)
  have r77 := fixed 77 (by decide) (by decide) (by decide)
  have r78 := fixed 78 (by decide) (by decide) (by decide)
  have r79 := fixed 79 (by decide) (by decide) (by decide)
  have r80 := fixed 80 (by decide) (by decide) (by decide)
  have r22 : popped.nr 22 = registeredState.nr 22 := node.trans (by simp [registeredState])
  have bytes : popped.nm = registeredState.nm := rfl
  have scratch : outsideMatchingMemberScratch popped = outsideMatchingMemberScratch registeredState := by
    funext address
    simp only [outsideMatchingMemberScratch, r55, r79, r80]
  have root : MatchingMemberRoot popped task.children := by
    have initial : MatchingMemberRoot registeredState task.children := registered
    refine ⟨?_, ?_, ?_, ?_, initial.unique, ?_, ?_⟩
    · simpa only [r22] using initial.proper
    · simpa only [r22, r77, r78, bytes] using initial.encoded
    · simpa only [r22, r77, r78, bytes, scratch] using initial.readable
    · simpa only [r22, r77, r55, r80, bytes] using initial.above
    · simpa only [r55] using initial.valid
    · simpa only [r55, r79, r80] using initial.separated
  exact ⟨smaller, MatchingRebaseCycleInput.of_memberRoot root odd (port.symm ▸ selected) distinct⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseQueuePop

/-! matching/MatchingRebaseMateCorrect.lean -/
section RppSource_MatchingRebaseMateCorrect
namespace VehicleRoutingSurvey.Routing

theorem matchingRebaseMatePrefix_congr {a b : ℕ → ℕ} (edge : ℕ → ℕ × ℕ) (n v : ℕ)
    (equal : a v = b v) : matchingRebaseMatePrefix a edge n v = matchingRebaseMatePrefix b edge n v := by
  induction n with
  | zero => exact equal
  | succ n ih =>
    by_cases right : v = (edge n).2
    · simp [matchingRebaseMatePrefix, right]
    · by_cases left : v = (edge n).1
      · have unequal : (edge n).1 ≠ (edge n).2 := fun eq => right (left.trans eq)
        simp only [matchingRebaseMatePrefix, left, Function.update_of_ne unequal, Function.update_self]
      · simpa only [matchingRebaseMatePrefix, Function.update_of_ne right, Function.update_of_ne left] using ih

theorem matchingRebaseMatePrefix_edges (mate : ℕ → ℕ) {a b : ℕ → ℕ × ℕ} (n : ℕ)
    (equal : ∀ i < n, a i = b i) : matchingRebaseMatePrefix mate a n = matchingRebaseMatePrefix mate b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [matchingRebaseMatePrefix, ih (fun i hi => equal i (by omega)), equal n (by omega)]

/-- Installing edges prescribed by a final matching preserves every previously
correct cell and makes each visited endpoint correct. -/
theorem matchingRebaseMatePrefix_correct (mate target : ℕ → ℕ) (edge : ℕ → ℕ × ℕ) (n v : ℕ)
    (pairs : ∀ i < n, target (edge i).1 = (edge i).2 ∧ target (edge i).2 = (edge i).1)
    (covered : mate v = target v ∨ ∃ i < n, v = (edge i).1 ∨ v = (edge i).2) :
    matchingRebaseMatePrefix mate edge n v = target v := by
  induction n with
  | zero =>
    rcases covered with yes | ⟨i, no, _⟩
    · exact yes
    · omega
  | succ n ih =>
    have current := pairs n (by omega)
    unfold matchingRebaseMatePrefix
    by_cases right : v = (edge n).2
    · subst v
      simpa using current.2.symm
    · rw [Function.update_of_ne right]
      by_cases left : v = (edge n).1
      · subst v
        simpa using current.1.symm
      · rw [Function.update_of_ne left]
        apply ih (fun i hi => pairs i (by omega))
        rcases covered with yes | ⟨i, hi, atEdge⟩
        · exact .inl yes
        · have different : i ≠ n := by
            rintro rfl
            exact atEdge.elim left right
          exact .inr ⟨i, by omega, atEdge⟩




end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseMateCorrect

/-! matching/MatchingRebaseTaskTransition.lean -/
section RppSource_MatchingRebaseTaskTransition
namespace VehicleRoutingSurvey.Routing



/-- The pure port choices of both children agree with the original edge
installed by the cyclic RAM scan. -/
theorem MatchingRebaseCycleQueueInput.chosenPair {s : ArithmeticState} {c : MatchingMemberTree}
    {free : ℕ} {prior : List MatchingRebaseTask} {choose : MatchingMemberJob → ℕ}
    (cycle : MatchingRebaseCycleQueueInput s c free prior choose) (i : ℕ) (hi : i < (s.nr 19 - 1) / 2) :
    (matchingRebasePortAt c choose (matchingRebaseChildIndex c.arity free i false),
      matchingRebasePortAt c choose (matchingRebaseChildIndex c.arity free i true)) =
        matchingRebaseOriginalPair s free i := by
  have same : c.arity = s.nr 19 := (c.jobs_length none).symm.trans cycle.size.symm
  have inJobs (b : Bool) : matchingRebaseChildIndex (s.nr 19) free i b < (c.jobs none).length := by
    rw [← cycle.size]
    exact Nat.mod_lt _ (Nat.zero_lt_of_lt cycle.inside)
  simpa only [same, matchingRebasePortAt, dif_pos (inJobs false), dif_pos (inJobs true), matchingRebaseOriginalPair]
    using (cycle.ports i hi).symm

/-- Pop a live task, decode all its original edges, and read the descendants
actually pushed by the executable node handler. -/
theorem MatchingRebaseQueueEncoding.runTask {s loaded t : ArithmeticState}
    {earlier : List MatchingRebaseTask} {task : MatchingRebaseTask} {free : ℕ}
    (encoded : MatchingRebaseQueueEncoding s (earlier ++ [task]))
    (root : MatchingMemberRoot {s with nr := Function.update s.nr 22 task.node} task.children)
    (odd : Odd task.children.arity) (selected : task.port ∈ task.children.leaves)
    (distinct : (task.children.rootKeys.map Prod.fst).Nodup)
    (geometry : MatchingRebaseCycleGeometry (poppedMatchingRebaseState s) task.children)
    (capacity : earlier.length + task.children.arity ≤ s.nr 55)
    (matesBeforeMap : s.nr 50 + s.nr 55 ≤ s.nr 79)
    (mapBeforeStack : s.nr 79 + s.nr 55 ≤ s.nr 81)
    (walkBeforeStack : s.nr 80 + 3 * s.nr 55 ≤ s.nr 81)
    (stackBeforeRecord : s.nr 81 + 2 * s.nr 55 ≤ s.nm (s.nr 77 + task.node))
    (view : MatchingRebaseCycleLoaded (poppedMatchingRebaseState s) loaded task.children free)
    (count : t.nr 82 = (rebasedMatchingCycleState loaded free).nr 82)
    (bytes : t.nm = (rebasedMatchingCycleState loaded free).nm)
    (keeps : matchingRebaseNodeKeeps s t) :
    ∃ choosePort : MatchingMemberJob → ℕ,
      let added := matchingRebaseCycleTaskPrefix task.children choosePort free ((loaded.nr 19 - 1) / 2)
      MatchingRebaseCycleQueueInput loaded task.children free earlier choosePort ∧
      MatchingRebaseQueueEncoding (matchingRebaseQueueSnapshot t) (earlier ++ added) ∧
      matchingRebaseQueueWork added = task.children.registeredNodes ∧
      (∃ sources, List.Forall₂ MatchingRebaseTask.fromTopJob added sources ∧
        sources.Subperm (task.children.jobs none)) ∧
      (∀ v < s.nr 55, t.nm (s.nr 50 + v) =
        matchingRebaseMatePrefix (fun x => s.nm (s.nr 50 + x))
          (matchingRebaseOriginalPair loaded free) ((loaded.nr 19 - 1) / 2) v) ∧
      (∀ a, OutsideEarlierCycleWrites loaded free ((loaded.nr 19 - 1) / 2) a → t.nm a = loaded.nm a) ∧
      (∀ i < (loaded.nr 19 - 1) / 2, matchingRebaseOriginalPair loaded free i =
        geometry.edge (matchingRebaseChildIndex task.children.arity free i false)) ∧
      (∃ hi : free < (task.children.jobs none).length,
        task.port ∈ ((task.children.jobs none)[free]'hi).tree.leaves) ∧
      (∀ job ∈ task.children.jobs none, choosePort job ∈ job.tree.leaves) := by
  obtain ⟨prior, asked, owner, input⟩ := encoded.nextCycle root odd selected distinct
  have sameFree := view.free_eq input
  subst asked
  obtain ⟨choosePort, exposed, inChild, ports⟩ := geometry.ports input view distinct
  obtain ⟨_, node, desired⟩ := encoded.pop
  have fixed (r : ℕ) (n22 : r ≠ 22 := by decide) (n29 : r ≠ 29 := by decide)
      (n82 : r ≠ 82 := by decide) : (poppedMatchingRebaseState s).nr r = s.nr r := by
    simp [poppedMatchingRebaseState, Function.update_of_ne n22, Function.update_of_ne n29,
      Function.update_of_ne n82]
  have popMemory : (poppedMatchingRebaseState s).nm = s.nm := rfl
  have cycle := MatchingRebaseCycleQueueInput.of_loaded input view prior
    (by rwa [fixed 55]) (by rwa [fixed 50, fixed 55, fixed 79])
    (by rwa [fixed 79, fixed 55, fixed 81]) (by rwa [fixed 80, fixed 55, fixed 81])
    (by simpa only [fixed 81, fixed 55, fixed 77, node, popMemory] using stackBeforeRecord)
    (geometry.endpoints input.members.valid) exposed ports
  obtain ⟨queue, credit, untouched⟩ := cycle.actualQueueUpdate view count bytes keeps
  have offset := (view.registers 50 (by decide)).trans (fixed 50)
  have dimension := (view.registers 55 (by decide)).trans (fixed 55)
  refine ⟨choosePort, cycle, queue, credit,
    matchingRebaseCycleTaskPrefix_sources _ _ _ _ inChild, ?_, untouched,
    geometry.originalPair input view distinct, ⟨_, desired ▸ input.desired_in_freeChild⟩, inChild⟩
  intro v inside
  rw [bytes, ← offset]
  apply ((rebasedMatchingCycleState_effects cycle).2.2.2 v (dimension.symm ▸ inside)).trans
  apply matchingRebaseMatePrefix_congr
  rw [offset]
  have mapWalk : s.nr 79 + s.nr 55 ≤ s.nr 80 := by
    simpa using root.separated
  have beforeMap : s.nr 50 + v < s.nr 79 := by omega
  have beforeWalk : s.nr 50 + v < s.nr 80 := by omega
  exact view.outside _ ⟨.inl (by simpa only [fixed 79] using beforeMap),
    .inl (by simpa only [fixed 80] using beforeWalk)⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseTaskTransition

/-! matching/MatchingRebaseCoverage.lean -/
section RppSource_MatchingRebaseCoverage
namespace VehicleRoutingSurvey.Routing



theorem matchingRebaseCycleTaskPrefix_all (c : MatchingMemberTree) (choose : MatchingMemberJob → ℕ)
    (free : ℕ) (odd : Odd c.arity) :
    matchingRebaseCycleTaskPrefix c choose free ((c.arity - 1) / 2) =
      ((c.jobs none).rotate free).filterMap (MatchingMemberJob.rebaseTask choose) := by
  obtain ⟨m, hm⟩ := odd
  have length : 2 * ((c.arity - 1) / 2) + 1 = ((c.jobs none).rotate free).length := by
    rw [List.length_rotate, c.jobs_length none]
    omega
  simp only [matchingRebaseCycleTaskPrefix, length, List.take_length]

/-- A vertex released by a node is either already the parent's exposed
port or is one of the chosen ports paired around the new base. -/
theorem MatchingRebaseTask.released_port (task : MatchingRebaseTask) (v : ℕ) (free : ℕ)
    (odd : Odd task.children.arity) (freeIn : free < (task.children.jobs none).length)
    (choose : MatchingMemberJob → ℕ) (exposes : matchingRebasePortAt task.children choose free = task.port)
    (ports : ∀ j ∈ task.children.jobs none, choose j ∈ j.tree.leaves)
    (wasNeeded : task.needs v)
    (released : ∀ t ∈ matchingRebaseCycleTaskPrefix task.children choose free ((task.children.arity - 1) / 2),
      ¬ t.needs v) :
    ∃ i < (task.children.arity - 1) / 2, ∃ side : Bool,
      v = matchingRebasePortAt task.children choose (matchingRebaseChildIndex task.children.arity free i side) := by
  let c := task.children
  let jobs := c.jobs none
  have assigned : v ∈ ((MatchingMemberJob.frontier jobs).map Prod.fst) := by
    rw [c.jobs_frontier_vertices none]
    exact wasNeeded.1
  obtain ⟨p, included, vertex⟩ := List.mem_map.mp assigned
  obtain ⟨j, listed, inj⟩ := List.mem_flatMap.mp included
  have belongs : v ∈ j.tree.leaves := by
    rw [← j.assignments_vertices]
    exact List.mem_map.mpr ⟨p, inj, vertex⟩
  have atPort : v = choose j := by
    cases eq : j.children with
    | none =>
      have resident := ports j listed
      have a : v = j.representative := by simpa [MatchingMemberJob.tree, eq, MatchingMemberTree.leaves] using belongs
      have b : choose j = j.representative := by simpa [MatchingMemberJob.tree, eq, MatchingMemberTree.leaves] using resident
      exact a.trans b.symm
    | some sub =>
      let t : MatchingRebaseTask := ⟨j.node, choose j, sub⟩
      have queued : t ∈ matchingRebaseCycleTaskPrefix c choose free ((c.arity - 1) / 2) := by
        rw [matchingRebaseCycleTaskPrefix_all c choose free odd]
        exact List.mem_filterMap.mpr ⟨j, List.mem_rotate.mpr listed, by simp [MatchingMemberJob.rebaseTask, eq, t]⟩
      have inside : v ∈ t.children.leaves := by
        simpa [MatchingMemberJob.tree, eq, MatchingMemberTree.leaves, t] using belongs
      by_contra diff
      exact released t queued ⟨inside, diff⟩
  obtain ⟨jIndex, inside, seen⟩ := List.mem_iff_getElem.mp listed
  have samePort : v = matchingRebasePortAt c choose jIndex := by
    have valid : jIndex < (c.jobs none).length := inside
    rw [matchingRebasePortAt, dif_pos valid]
    exact atPort.trans (congrArg choose seen.symm)
  have different : jIndex ≠ free := by
    rintro rfl
    exact wasNeeded.2 (samePort.trans exposes)
  have size := c.jobs_length none
  have within : jIndex < c.arity := by rwa [← size]
  have freeOK : free < c.arity := by rwa [← size]
  obtain ⟨i, hi, side, position⟩ := (matchingRebaseChildIndex_complete freeOK odd).2.1 jIndex within different
  exact ⟨i, hi, side, position.symm ▸ samePort⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseCoverage

/-! matching/MatchingRebaseArchiveWrites.lean -/
section RppSource_MatchingRebaseArchiveWrites
namespace VehicleRoutingSurvey.Routing

/-- A completed node operation preserves the entire header area and every
word of all other allocated cycles, measured in the original registry. -/
theorem MatchingRebaseArchive.keepsRegistry {base s loaded t : ArithmeticState} {n free : ℕ}
    {children : MatchingMemberTree} {prior : List MatchingRebaseTask} {choosePort : MatchingMemberJob → ℕ}
    (archive : MatchingRebaseArchive base) (live : archive.live n children)
    (fixed : ∀ r ∈ matchingRebaseLayoutRegisters, s.nr r = base.nr r)
    (headers : ∀ a, matchingRebaseHeaderArea base a → s.nm a = base.nm a)
    (popped : (poppedMatchingRebaseState s).nr 22 = n)
    (view : MatchingRebaseCycleLoaded (poppedMatchingRebaseState s) loaded children free)
    (cycle : MatchingRebaseCycleQueueInput loaded children free prior choosePort)
    (untouched : ∀ a, OutsideEarlierCycleWrites loaded free ((loaded.nr 19 - 1) / 2) a → t.nm a = loaded.nm a) :
    (∀ a, matchingRebaseHeaderArea base a → t.nm a = s.nm a) ∧
      ∀ other, 0 < other → other < base.nr 76 → other ≠ n →
        ∀ a, matchingRebaseRowArea base other a → t.nm a = s.nm a := by
  let pop := poppedMatchingRebaseState s
  have bank (r : ℕ) (listed : r ∈ matchingRebaseLayoutRegisters := by decide)
      (n22 : r ≠ 22 := by decide) (n29 : r ≠ 29 := by decide) (n82 : r ≠ 82 := by decide) :
      pop.nr r = base.nr r := by
    simpa [pop, poppedMatchingRebaseState, Function.update_of_ne n22, Function.update_of_ne n29,
      Function.update_of_ne n82] using fixed r listed
  have stored (r : ℕ) (safe : r ∉ [0, 6, 7, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27, 28, 87] := by decide)
      (listed : r ∈ matchingRebaseLayoutRegisters := by decide)
      (n22 : r ≠ 22 := by decide) (n29 : r ≠ 29 := by decide) (n82 : r ≠ 82 := by decide) :
      loaded.nr r = base.nr r := (view.registers r safe).trans (bank r listed n22 n29 n82)
  have hdr := archive.headers n children live
  have record : loaded.nr 18 = matchingCycleRecordStart base n := by
    rw [view.recordBase, popped]
    change s.nm (pop.nr 77 + n) = _
    rw [bank 77]
    exact headers _ hdr.1
  have arity : base.nm (base.nr 78 + n) = children.arity := by
    simpa [matchingRebaseNodeState] using (archive.record n children live).members.encoded.1
  have count := view.count.trans arity.symm
  have liveN := archive.allocated n children live
  have begins := (archive.order.bounded n liveN.1 liveN.2).1
  have mapWalk := archive.mapWalk
  have jobs := archive.walkJobs
  have stack := archive.jobsRecords
  have mates := archive.mates
  unfold matchingRebaseScratchEnd at begins stack
  have scratch (a : ℕ) (h : outsideMatchingMemberScratch base a) : t.nm a = loaded.nm a → t.nm a = s.nm a := by
    intro stable
    have outside : outsideMatchingMemberScratch pop a := by
      simpa only [outsideMatchingMemberScratch, bank 79, bank 80, bank 55] using h
    exact stable.trans (view.outside _ outside)
  constructor
  · intro a h
    obtain ⟨afterMates, beforeMap⟩ := h
    apply scratch _ ⟨.inl beforeMap, .inl (by omega)⟩
    apply untouched
    rw [OutsideEarlierCycleWrites, OutsideRebaseMateAndStack, stored 50, stored 55, stored 81, record]
    exact ⟨⟨.inr afterMates, .inl (by omega)⟩, by omega, fun _ _ _ => by omega⟩
  · intro other positive valid different a h
    have lower := (archive.order.bounded other positive valid).1.trans h.1
    unfold matchingRebaseScratchEnd at lower
    have separated := archive.order.disjoint ⟨positive, valid⟩ liveN different h.1 h.2
    have away (j : ℕ) (inside : j < loaded.nr 19) : a ≠ loaded.nr 18 + 4 * j := by
      rw [record]
      rw [matchingCycleRecordEnd] at separated
      omega
    apply scratch _ ⟨.inr (by omega), .inr (by omega)⟩
    apply untouched
    refine ⟨?_, away free cycle.inside, fun i _ side => away _ (Nat.mod_lt _ (Nat.zero_lt_of_lt cycle.inside))⟩
    rw [OutsideRebaseMateAndStack, stored 50, stored 55, stored 81]
    exact ⟨.inr (by omega), .inr (by omega)⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseArchiveWrites

/-! matching/MatchingRebaseChildRows.lean -/
section RppSource_MatchingRebaseChildRows
namespace VehicleRoutingSurvey.Routing

private theorem matchingRebaseRepresentativePrefix_target {s : ArithmeticState} {free : ℕ} (target : ℕ → ℕ)
    (exposed : target free = s.nr 29) (n v : ℕ)
    (pairs : ∀ i < n,
      (target (matchingRebaseChildIndex (s.nr 19) free i false),
        target (matchingRebaseChildIndex (s.nr 19) free i true)) = matchingRebaseOriginalPair s free i)
    (covered : v = free ∨ ∃ i < n, ∃ side : Bool, matchingRebaseChildIndex (s.nr 19) free i side = v) :
    matchingRebaseRepresentativePrefix s free n v = target v := by
  induction n with
  | zero =>
    rcases covered with rfl | ⟨i, hi, _⟩
    · simpa [matchingRebaseRepresentativePrefix] using exposed.symm
    · omega
  | succ n ih =>
    have now := pairs n (by omega)
    let l := matchingRebaseChildIndex (s.nr 19) free n false
    let r := matchingRebaseChildIndex (s.nr 19) free n true
    have lhs : target l = (matchingRebaseOriginalPair s free n).1 := congrArg Prod.fst now
    have rhs : target r = (matchingRebaseOriginalPair s free n).2 := congrArg Prod.snd now
    change Function.update (Function.update (matchingRebaseRepresentativePrefix s free n) l
      (matchingRebaseOriginalPair s free n).1) r (matchingRebaseOriginalPair s free n).2 v = _
    by_cases right : v = r
    · subst v
      simpa using rhs.symm
    · rw [Function.update_of_ne right]
      by_cases left : v = l
      · subst v
        simpa using lhs.symm
      · rw [Function.update_of_ne left]
        apply ih (fun i hi => pairs i (by omega))
        rcases covered with yes | ⟨i, hi, side, atSide⟩
        · exact .inl yes
        · have different : i ≠ n := by
            rintro rfl
            cases side
            · exact left atSide.symm
            · exact right atSide.symm
          exact .inr ⟨i, by omega, side, atSide⟩

/-- Every live child row of a rematched blossom contains its newly exposed
original representative and exactly the old child ID and original edge words. -/
theorem MatchingRebaseCycleQueueInput.childRowAfter {s : ArithmeticState} {c : MatchingMemberTree}
    {free : ℕ} {prior : List MatchingRebaseTask} {choose : MatchingMemberJob → ℕ}
    (cycle : MatchingRebaseCycleQueueInput s c free prior choose) (v : ℕ) (inside : v < s.nr 19) :
    let addr := s.nr 18 + 4 * v
    matchingCycleChildAt (rebasedMatchingCycleState s free).nm addr =
      {matchingCycleChildAt s.nm addr with representative := matchingRebasePortAt c choose v} := by
  intro addr
  let target := matchingRebasePortAt c choose
  let pairs := (s.nr 19 - 1) / 2
  have same : c.arity = s.nr 19 := (c.jobs_length none).symm.trans cycle.size.symm
  have atFree : target free = s.nr 29 := by
    simpa [target, matchingRebasePortAt, cycle.size ▸ cycle.inside] using cycle.exposed
  have rows (i : ℕ) (hi : i < pairs) :
      (target (matchingRebaseChildIndex (s.nr 19) free i false),
        target (matchingRebaseChildIndex (s.nr 19) free i true)) = matchingRebaseOriginalPair s free i := by
    simpa only [same, target] using cycle.chosenPair i hi
  have covered : v = free ∨ ∃ i < pairs, ∃ side, matchingRebaseChildIndex (s.nr 19) free i side = v := by
    by_cases eq : v = free
    · exact .inl eq
    · exact .inr ((matchingRebaseChildIndex_complete cycle.inside cycle.odd).2.1 v inside eq)
  have rep := ((rebasedMatchingCycleState_fullEffects cycle).2.2.2.2 v).trans
    (matchingRebaseRepresentativePrefix_target target atFree pairs v rows covered)
  have unchanged (w : ℕ) (positive : 0 < w) (hw : w < 4) :
      (rebasedMatchingCycleState s free).nm (addr + w) = s.nm (addr + w) := by
    have m := cycle.matesBeforeMap
    have q := cycle.mapBeforeStack
    have h := cycle.stackBeforeRecord
    apply (rebasedMatchingCycleState_queue cycle).2.2
    dsimp only [addr]
    refine ⟨⟨.inr (by omega), .inr (by omega)⟩, by omega, fun _ _ _ => by omega⟩
  change (matchingCycleChildAt (rebasedMatchingCycleState s free).nm addr) =
    {matchingCycleChildAt s.nm addr with representative := target v}
  have key : (rebasedMatchingCycleState s free).nm addr = target v := rep
  simp only [matchingCycleChildAt, key, unchanged 1 (by decide) (by decide), unchanged 2 (by decide) (by decide),
    unchanged 3 (by decide) (by decide)]


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseChildRows

/-! matching/MatchingRebaseRowTransition.lean -/
section RppSource_MatchingRebaseRowTransition
namespace VehicleRoutingSurvey.Routing



def matchingRebaseRowsNext (previous : ℕ → ℕ → MatchingCycleChild) (task : MatchingRebaseTask)
    (choose : MatchingMemberJob → ℕ) (n i : ℕ) : MatchingCycleChild :=
  if n = task.node then {previous n i with representative := matchingRebasePortAt task.children choose i} else previous n i

/-- A whole-node update changes precisely the first word of its own
four-word child rows and preserves every word of every other allocated row. -/
theorem MatchingRebaseArchive.rowTransition {base s loaded t : ArithmeticState} {task : MatchingRebaseTask} {free : ℕ}
    {prior : List MatchingRebaseTask} {choose : MatchingMemberJob → ℕ}
    (archive : MatchingRebaseArchive base) (live : archive.live task.node task.children)
    (fixed : ∀ r ∈ matchingRebaseLayoutRegisters, s.nr r = base.nr r)
    (headers : ∀ a, matchingRebaseHeaderArea base a → s.nm a = base.nm a)
    (popped : (poppedMatchingRebaseState s).nr 22 = task.node)
    (view : MatchingRebaseCycleLoaded (poppedMatchingRebaseState s) loaded task.children free)
    (cycle : MatchingRebaseCycleQueueInput loaded task.children free prior choose)
    (bytes : t.nm = (rebasedMatchingCycleState loaded free).nm)
    (others : ∀ n, 0 < n → n < base.nr 76 → n ≠ task.node → ∀ a,
      matchingRebaseRowArea base n a → t.nm a = s.nm a)
    (old : ℕ → ℕ → MatchingCycleChild)
    (table : ∀ n, 0 < n → n < base.nr 76 → ∀ i < base.nm (base.nr 78+n), matchingRebaseRowsAt base s n i = old n i) :
    ∀ n, 0 < n → n < base.nr 76 → ∀ i < base.nm (base.nr 78+n),
      matchingRebaseRowsAt base t n i = matchingRebaseRowsNext old task choose n i := by
  intro n pos small i hi
  let addr := matchingCycleRecordStart base n + 4*i
  have within (w : ℕ) (hw : w < 4) : matchingRebaseRowArea base n (addr+w) := by
    simp only [matchingRebaseRowArea,matchingCycleRecordEnd,addr]
    omega
  by_cases active : n = task.node
  · subst n
    let pop := poppedMatchingRebaseState s
    have bank (r : ℕ) (h : r ∈ matchingRebaseLayoutRegisters := by decide)
        (a : r ≠ 22 := by decide) (b : r ≠ 29 := by decide) (c : r ≠ 82 := by decide) : pop.nr r = base.nr r := by
      simpa [pop,poppedMatchingRebaseState,Function.update_of_ne a,Function.update_of_ne b,Function.update_of_ne c]
        using fixed r h
    have header := archive.headers _ _ live
    have start : loaded.nr 18 = matchingCycleRecordStart base task.node := by
      rw [view.recordBase,popped]
      change s.nm (pop.nr 77+task.node) = _
      rw [bank 77]
      exact headers _ header.1
    have length : base.nm (base.nr 78+task.node) = task.children.arity := by
      simpa [matchingRebaseNodeState] using (archive.record _ _ live).members.encoded.1
    have withinLoaded : i < loaded.nr 19 := view.count.symm ▸ length ▸ hi
    have lower := (archive.order.bounded _ pos small).1
    have mapWalk := archive.mapWalk
    have read (w : ℕ) : loaded.nm (addr+w) = s.nm (addr+w) := by
      have outside : outsideMatchingMemberScratch pop (addr+w) := by
        simp only [outsideMatchingMemberScratch,bank 79,bank 80,bank 55]
        unfold matchingRebaseScratchEnd at lower
        dsimp only [addr]
        exact ⟨.inr (by omega),.inr (by omega)⟩
      exact view.outside _ outside
    have word : loaded.nm addr = s.nm addr := read 0
    have sameCell : matchingCycleChildAt loaded.nm addr = matchingCycleChildAt s.nm addr := by
      simp only [matchingCycleChildAt,word,read 1,read 2,read 3]
    have after := cycle.childRowAfter i withinLoaded
    rw [start] at after
    rw [matchingRebaseRowsAt, matchingRebaseRowsNext, if_pos rfl]
    rw [bytes]
    change matchingCycleChildAt (rebasedMatchingCycleState loaded free).nm addr =
      {matchingCycleChildAt loaded.nm addr with representative := matchingRebasePortAt task.children choose i} at after
    rw [sameCell, show matchingCycleChildAt s.nm addr = _ from table _ pos small _ hi] at after
    exact after
  · have stable (w : ℕ) (hw : w < 4) := others n pos small active (addr+w) (within w hw)
    have first : t.nm addr = s.nm addr := stable 0 (by decide)
    have sameCell : matchingCycleChildAt t.nm addr = matchingCycleChildAt s.nm addr := by
      simp only [matchingCycleChildAt,first,stable 1 (by decide),stable 2 (by decide),stable 3 (by decide)]
    exact sameCell.trans (by simpa [matchingRebaseRowsNext,active] using! table n pos small i hi)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseRowTransition

/-! matching/MatchingRebaseLiveQueue.lean -/
section RppSource_MatchingRebaseLiveQueue
namespace VehicleRoutingSurvey.Routing

/-- A trace on the original vertices. Each contraction cycle supplies its
recorded physical edges in cyclic order after the subtree containing the new
base. The recursive transitions contain no RAM states or instructions. -/
inductive MatchingRebaseRecordHistory {base : ArithmeticState} (archive : MatchingRebaseArchive base)
    (initial : List MatchingRebaseTask) : List MatchingRebaseTask → (ℕ → ℕ) → (ℕ → ℕ → MatchingCycleChild) → Prop
  | start : MatchingRebaseRecordHistory archive initial initial (fun v => base.nm (base.nr 50 + v)) (matchingRebaseRowsAt base base)
  | next {earlier : List MatchingRebaseTask} {task : MatchingRebaseTask} {mate : ℕ → ℕ}
      {rows : ℕ → ℕ → MatchingCycleChild}
      (before : MatchingRebaseRecordHistory archive initial (earlier ++ [task]) mate rows)
      (known : archive.live task.node task.children) (free : ℕ)
      (baseChild : ∃ h : free < (task.children.jobs none).length,
        task.port ∈ ((task.children.jobs none)[free]'h).tree.leaves)
      (choosePort : MatchingMemberJob → ℕ) (ports : ∀ j ∈ task.children.jobs none, choosePort j ∈ j.tree.leaves)
      (exposes : matchingRebasePortAt task.children choosePort free = task.port)
      (pairs : ∀ i < (task.children.arity - 1) / 2,
        (matchingRebasePortAt task.children choosePort (matchingRebaseChildIndex task.children.arity free i false),
          matchingRebasePortAt task.children choosePort (matchingRebaseChildIndex task.children.arity free i true)) =
            (archive.record _ _ known).geometry.edge (matchingRebaseChildIndex task.children.arity free i false)) :
      MatchingRebaseRecordHistory archive initial
        (earlier ++ matchingRebaseCycleTaskPrefix task.children choosePort free ((task.children.arity - 1) / 2))
        (matchingRebaseMatePrefix mate
          (fun i => (archive.record _ _ known).geometry.edge
            (matchingRebaseChildIndex task.children.arity free i false)) ((task.children.arity - 1) / 2))
        (matchingRebaseRowsNext rows task choosePort)

def MatchingRebaseHistory {base : ArithmeticState} (archive : MatchingRebaseArchive base)
    (initial pending : List MatchingRebaseTask) (mate : ℕ → ℕ) : Prop :=
  ∃ rows, MatchingRebaseRecordHistory archive initial pending mate rows

structure MatchingRebaseLiveQueue {base : ArithmeticState} (archive : MatchingRebaseArchive base)
    (initial jobs : List MatchingRebaseTask) (s : ArithmeticState) : Prop where
  fixed : ∀ r ∈ matchingRebaseLayoutRegisters, s.nr r = base.nr r
  queue : MatchingRebaseQueueEncoding s jobs
  tasks : ∀ t ∈ jobs, archive.live t.node t.children ∧ t.port ∈ t.children.leaves
  distinct : (matchingRebaseTaskLeaves jobs).Nodup
  unique : (matchingRebaseQueueIds jobs).Nodup
  allocated : ∀ n ∈ matchingRebaseQueueIds jobs, 0 < n ∧ n < base.nr 76
  below : ∀ a < base.nr 50, s.nm a = base.nm a
  headers : ∀ a, matchingRebaseHeaderArea base a → s.nm a = base.nm a
  rows : ∀ n ∈ matchingRebaseQueueIds jobs, ∀ a, matchingRebaseRowArea base n a → s.nm a = base.nm a
  effects : ∃ f rows, MatchingRebaseRecordHistory archive initial jobs f rows ∧
    (∀ v < base.nr 55, s.nm (base.nr 50 + v) = f v) ∧
    ∀ n, 0 < n → n < base.nr 76 → ∀ i < base.nm (base.nr 78+n), matchingRebaseRowsAt base s n i = rows n i

theorem MatchingRebaseLiveQueue.mate {base s : ArithmeticState} {archive : MatchingRebaseArchive base}
    {initial jobs : List MatchingRebaseTask} (ready : MatchingRebaseLiveQueue archive initial jobs s) :
    ∃ f, MatchingRebaseHistory archive initial jobs f ∧ ∀ v < base.nr 55, s.nm (base.nr 50+v) = f v := by
  obtain ⟨f,rows,history,table,_⟩ := ready.effects
  exact ⟨f,⟨rows,history⟩,table⟩

theorem MatchingRebaseLiveQueue.start {base : ArithmeticState} (archive : MatchingRebaseArchive base)
    (jobs : List MatchingRebaseTask) (queue : MatchingRebaseQueueEncoding base jobs)
    (tasks : ∀ t ∈ jobs, archive.live t.node t.children ∧ t.port ∈ t.children.leaves)
    (distinct : (matchingRebaseTaskLeaves jobs).Nodup) (unique : (matchingRebaseQueueIds jobs).Nodup)
    (allocated : ∀ n ∈ matchingRebaseQueueIds jobs, 0 < n ∧ n < base.nr 76) :
    MatchingRebaseLiveQueue archive jobs jobs base :=
  ⟨fun _ _ => rfl, queue, tasks, distinct, unique, allocated, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl,
    ⟨_, _, .start, fun _ _ => rfl,fun _ _ _ _ _ => rfl⟩⟩

theorem MatchingRebaseLiveQueue.transport {base s t : ArithmeticState} {archive : MatchingRebaseArchive base}
    {initial jobs : List MatchingRebaseTask} (ready : MatchingRebaseLiveQueue archive initial jobs s)
    (fixed : ∀ r ∈ matchingRebaseLayoutRegisters, t.nr r = s.nr r) (count : t.nr 82 = s.nr 82)
    (memory : t.nm = s.nm) : MatchingRebaseLiveQueue archive initial jobs t :=
  ⟨fun r hr => (fixed r hr).trans (ready.fixed r hr),
    ready.queue.transport (fixed 81 (by decide)) count (fun a _ _ => congrFun memory a),
    ready.tasks, ready.distinct, ready.unique, ready.allocated,
    fun a ha => (congrFun memory a).trans (ready.below a ha),
    fun a h => (congrFun memory a).trans (ready.headers a h),
    fun n hn a ha => (congrFun memory a).trans (ready.rows n hn a ha),
    by
      obtain ⟨f,rows,trace,table,records⟩ := ready.effects
      refine ⟨f,rows,trace,fun v hv => (congrFun memory _).trans (table v hv),?_⟩
      intro n lo hi i inside
      simpa only [matchingRebaseRowsAt,memory] using records n lo hi i inside⟩

private theorem matchingRebaseSnapshot_layout (s : ArithmeticState) (r : ℕ) (inside : r ∈ matchingRebaseLayoutRegisters) :
    (matchingRebaseQueueSnapshot s).nr r = s.nr r := by
  have away : r ≠ 43 := by simp [matchingRebaseLayoutRegisters] at inside; omega
  exact Function.update_of_ne away _ _

private def MatchingRebaseLiveQueue.recordAt {base s : ArithmeticState} {archive : MatchingRebaseArchive base}
    {initial jobs : List MatchingRebaseTask} (ready : MatchingRebaseLiveQueue archive initial jobs s)
    {task : MatchingRebaseTask} (pending : task ∈ jobs) :
    MatchingMemberRoot (matchingRebaseNodeState s task.node) task.children ×'
      MatchingRebaseCycleGeometry (matchingRebaseNodeState s task.node) task.children :=
  (archive.record _ _ (ready.tasks _ pending).1).restore ready.fixed (by
    intro a ha
    rcases ha with head | ⟨n, child, row⟩
    · exact ready.headers a head
    · exact ready.rows n (List.mem_flatMap.mpr ⟨task, pending, child⟩) a row)

private def MatchingRebaseCycleGeometry.atPop {s : ArithmeticState} {task : MatchingRebaseTask}
    (geom : MatchingRebaseCycleGeometry (matchingRebaseNodeState s task.node) task.children)
    (id : (poppedMatchingRebaseState s).nr 22 = task.node) :
    MatchingRebaseCycleGeometry (poppedMatchingRebaseState s) task.children where
  edge := geom.edge
  source := geom.source
  target := geom.target
  row := by
    intro i hi
    have changeId := geom.row i hi
    rw [id]
    simpa [matchingRebaseNodeState, poppedMatchingRebaseState] using changeId

private theorem matchingRebaseChildren_live {base : ArithmeticState} {archive : MatchingRebaseArchive base}
    {task : MatchingRebaseTask} {added : List MatchingRebaseTask} {sources : List MatchingMemberJob}
    (known : archive.live task.node task.children) (pair : List.Forall₂ MatchingRebaseTask.fromTopJob added sources)
    (chosen : ∀ j ∈ sources, j ∈ task.children.jobs none) :
    ∀ t ∈ added, archive.live t.node t.children ∧ t.port ∈ t.children.leaves := by
  induction pair with
  | nil => simp
  | @cons t j ts js rel tail ih =>
    intro x hx
    rcases List.mem_cons.mp hx with head | later
    · subst x
      have child := archive.child _ _ known j (chosen j (by simp)) t.children rel.2.1
      exact ⟨rel.1.symm ▸ child, rel.2.2⟩
    · exact ih (fun a ha => chosen a (List.mem_cons_of_mem _ ha)) x later

/-- The actual rebase queue is sound for a live, ordered registry. A completed
queue has an original-vertex mate table given by the archived cyclic edges. -/
theorem MatchingRebaseLiveQueue.interface {base : ArithmeticState} (archive : MatchingRebaseArchive base)
    (initial : List MatchingRebaseTask) : MatchingRebaseQueueInterface (MatchingRebaseLiveQueue archive initial) := by
  have unsnap {jobs : List MatchingRebaseTask} {s : ArithmeticState}
      (ready : MatchingRebaseLiveQueue archive initial jobs (matchingRebaseQueueSnapshot s)) :
      MatchingRebaseLiveQueue archive initial jobs s :=
    ready.transport (fun r listed => (matchingRebaseSnapshot_layout s r listed).symm) (by simp [matchingRebaseQueueSnapshot]) rfl
  constructor
  · intro jobs s hs
    exact (unsnap hs).queue.count
  · intro earlier task s hs
    have ready := unsnap hs
    have pending : task ∈ earlier ++ [task] := by simp
    have typed := ready.tasks task pending
    have archived := archive.record _ _ typed.1
    exact (ready.queue.nextCycle (ready.recordAt pending).1 archived.odd typed.2 archived.distinct).2
  · intro earlier task s loaded t free hs view count bytes _ _ keeps
    have ready := unsnap hs
    have pending : task ∈ earlier ++ [task] := by simp
    have typed := ready.tasks task pending
    let archived := archive.record _ _ typed.1
    let node := ready.recordAt pending
    have pop := ready.queue.pop
    let geom := node.2.atPop pop.2.1
    have fixed (r : ℕ) (listed : r ∈ matchingRebaseLayoutRegisters := by decide) : s.nr r = base.nr r := ready.fixed r listed
    have proper (u : MatchingRebaseTask) (present : u ∈ earlier ++ [task]) :
        (MatchingMemberTree.blossom 0 u.node u.children .nil).proper := by
      simpa [matchingRebaseNodeState] using (ready.recordAt present).1.proper
    have valid (v : ℕ) (present : v ∈ matchingRebaseTaskLeaves (earlier ++ [task])) : v < s.nr 55 := by
      obtain ⟨u, inJobs, belongs⟩ := List.mem_flatMap.mp present
      simpa [matchingRebaseNodeState] using (ready.recordAt inJobs).1.valid v belongs
    have memory := ready.headers _ (archive.headers _ _ typed.1).1
    have boundary : s.nr 81 + 2 * s.nr 55 ≤ s.nm (s.nr 77 + task.node) := by
      rw [fixed 81, fixed 55, fixed 77, memory]
      have bounds := archive.allocated _ _ typed.1
      exact archive.jobsRecords.trans (archive.order.bounded _ bounds.1 bounds.2).1
    obtain ⟨choose, cycle, encoding, work, ⟨sources, related, selected⟩, mateOut, untouched,
      originalEdges, freeChild, portLeaves⟩ := ready.queue.runTask node.1 archived.odd typed.2 archived.distinct geom
      (matchingRebaseQueue_arity_capacity proper ready.distinct valid)
      (by simpa only [fixed 50, fixed 55, fixed 79] using archive.mates)
      (by rw [fixed 79, fixed 55, fixed 81]; have := archive.mapWalk; have := archive.walkJobs; omega)
      (by simpa only [fixed 80, fixed 55, fixed 81] using archive.walkJobs) boundary view count bytes keeps
    let added := matchingRebaseCycleTaskPrefix task.children choose free ((loaded.nr 19 - 1) / 2)
    have frontier := matchingRebaseFrontier_replace related selected ready.distinct ready.unique
    have intact := archive.keepsRegistry typed.1 ready.fixed ready.headers pop.2.1 view cycle untouched
    refine ⟨added, work, ?_⟩
    refine ⟨?_, encoding, ?_, frontier.1, frontier.2.1, ?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      have away : r ∉ [0, 6, 7, 10, 11, 12, 13, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27, 28,
          29, 46, 47, 49, 82, 87, 95] := by simp [matchingRebaseLayoutRegisters] at hr; simp; omega
      exact (matchingRebaseSnapshot_layout t r hr).trans ((keeps r away).trans (fixed r hr))
    · intro u member
      rcases List.mem_append.mp member with old | child
      · exact ready.tasks _ (List.mem_append_left _ old)
      · exact matchingRebaseChildren_live typed.1 related selected.subset _ child
    · intro n hn
      exact ready.allocated n (frontier.2.2.2.1 n hn)
    · intro a ha
      have beforeWalk : s.nr 50 ≤ s.nr 80 := by
        rw [fixed 50, fixed 80]
        have := archive.mates
        have := archive.mapWalk
        omega
      exact (cycle.keepsBeforeMate view bytes beforeWalk a (by rwa [fixed 50])).trans (ready.below a ha)
    · intro a ha
      exact (intact.1 a ha).trans (ready.headers a ha)
    · intro n hn a ha
      have old := frontier.2.2.2.1 n hn
      have range := ready.allocated n old
      have different : n ≠ task.node := fun eq => frontier.2.2.1 (eq ▸ hn)
      exact (intact.2 n range.1 range.2 different a ha).trans (ready.rows n old a ha)
    · obtain ⟨m, oldRows, history, holds, oldTable⟩ := ready.effects
      let originalEdge (i : ℕ) := archived.geometry.edge (matchingRebaseChildIndex task.children.arity free i false)
      let next := matchingRebaseMatePrefix m originalEdge ((task.children.arity - 1) / 2)
      refine ⟨next, matchingRebaseRowsNext oldRows task choose, ?_, ?_, ?_⟩
      · change MatchingRebaseRecordHistory archive initial (earlier ++ matchingRebaseCycleTaskPrefix task.children choose free _) next _
        rw [view.count]
        apply history.next typed.1 free freeChild choose portLeaves
        · have exposed := cycle.exposed.trans ((view.registers 29 (by decide)).trans pop.2.2)
          simpa only [matchingRebasePortAt, dif_pos (cycle.size ▸ cycle.inside)] using exposed
        · intro i within
          have h : i < (loaded.nr 19 - 1) / 2 := by rwa [view.count]
          exact (cycle.chosenPair i h).trans (originalEdges i h)
      · intro v hi
        have same := mateOut v (by rwa [fixed 55])
        change t.nm (base.nr 50 + v) = next v
        rw [← fixed 50, same]
        have oldMate : s.nm (s.nr 50 + v) = m v := by rw [fixed 50]; exact holds v hi
        apply (matchingRebaseMatePrefix_congr _ _ v oldMate).trans
        have edgeEq := matchingRebaseMatePrefix_edges m ((loaded.nr 19 - 1) / 2) (b := originalEdge) originalEdges
        rw [edgeEq, view.count]
      · exact archive.rowTransition typed.1 ready.fixed ready.headers pop.2.1 view cycle bytes intact.2 oldRows oldTable


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseLiveQueue

/-! matching/MatchingRebaseLiftTarget.lean -/
section RppSource_MatchingRebaseLiftTarget
namespace VehicleRoutingSurvey.Routing





theorem matchingRebaseChosen_eq (c : MatchingMemberTree) (odd : Odd c.arity)
    (f g : MatchingMemberJob → ℕ) {free : ℕ} (hf : free < (c.jobs none).length)
    (freeEq : matchingRebasePortAt c f free = matchingRebasePortAt c g free)
    (pairEq : ∀ i < (c.arity - 1) / 2, ∀ b : Bool,
      matchingRebasePortAt c f (matchingRebaseChildIndex c.arity free i b) =
      matchingRebasePortAt c g (matchingRebaseChildIndex c.arity free i b)) : ∀ j ∈ c.jobs none, f j = g j := by
  intro j present
  obtain ⟨p, hp, atJob⟩ := List.mem_iff_getElem.mp present
  have atIndex : matchingRebasePortAt c f p = matchingRebasePortAt c g p := by
    by_cases isFree : p = free
    · exact isFree.symm ▸ freeEq
    · have size := c.jobs_length none
      have bound : p < c.arity := size ▸ hp
      have base : free < c.arity := size ▸ hf
      obtain ⟨i, hi, side, loc⟩ := (matchingRebaseChildIndex_complete base odd).2.1 p bound isFree
      exact loc ▸ pairEq i hi side
  simpa only [matchingRebasePortAt, dif_pos hp, atJob] using atIndex

/-- The original mate table agrees with the mathematical lift on every
vertex outside the interiors of the remaining queued subtrees. -/
theorem MatchingRebaseHistory.realizes {base : ArithmeticState} {archive : MatchingRebaseArchive base}
    {initial pending : List MatchingRebaseTask} {f target : ℕ → ℕ} (trace : MatchingRebaseHistory archive initial pending f)
    (plan : MatchingRebaseLiftTarget archive target) (initialPorts : ∀ t ∈ initial, t.port = plan.port t.node)
    (initialMates : ∀ v < base.nr 55, (∀ t ∈ initial, ¬ t.needs v) → base.nm (base.nr 50 + v) = target v) :
    (∀ t ∈ pending, t.port = plan.port t.node) ∧
      ∀ v < base.nr 55, (∀ t ∈ pending, ¬ t.needs v) → f v = target v := by
  obtain ⟨_,trace⟩ := trace
  induction trace with
  | start => exact ⟨initialPorts, initialMates⟩
  | @next earlier task mate raw before known free baseChild choose ports exposes pairs ih =>
    let c := task.children
    let edge (i : ℕ) := (archive.record _ _ known).geometry.edge (matchingRebaseChildIndex c.arity free i false)
    let added := matchingRebaseCycleTaskPrefix c choose free ((c.arity - 1)/2)
    have oldPort := ih.1 task (by simp)
    obtain ⟨hf, inFree⟩ := baseChild
    have plannedFree : plan.port task.node ∈ ((c.jobs none)[free]'hf).tree.leaves := oldPort ▸ inFree
    have prescribed := plan.pairs _ _ known free hf plannedFree
    have odd := (archive.record _ _ known).odd
    have same (j : MatchingMemberJob) (present : j ∈ c.jobs none) : choose j = j.liftPort plan.port := by
      apply matchingRebaseChosen_eq c odd choose (MatchingMemberJob.liftPort plan.port) hf _ _ j present
      · exact (exposes.trans oldPort).trans (plan.inherits _ _ known free hf plannedFree).symm
      · intro i hi side
        have eq := (pairs i hi).trans (prescribed i hi).1.symm
        cases side
        · exact congrArg Prod.fst eq
        · exact congrArg Prod.snd eq
    constructor
    · intro t present
      rcases List.mem_append.mp present with prior | newTask
      · exact ih.1 _ (List.mem_append_left _ prior)
      · rw [matchingRebaseCycleTaskPrefix_all _ _ _ odd] at newTask
        obtain ⟨j, listed, queued⟩ := List.mem_filterMap.mp newTask
        have atJ := same j (List.mem_rotate.mp listed)
        cases kind : j.children with
        | none => simp [MatchingMemberJob.rebaseTask, kind] at queued
        | some sub =>
          have atTask : (⟨j.node, choose j, sub⟩ : MatchingRebaseTask) = t := by
            simpa [MatchingMemberJob.rebaseTask, kind] using queued
          subst t
          simpa [MatchingMemberJob.liftPort, kind] using atJ
    · intro v inside settled
      apply matchingRebaseMatePrefix_correct _ target edge _ v (fun i hi => (prescribed i hi).2)
      by_cases needs : task.needs v
      · have removed (t : MatchingRebaseTask) (h : t ∈ added) : ¬t.needs v := settled t (List.mem_append_right _ h)
        obtain ⟨i, hi, side, atPort⟩ := task.released_port v free odd hf choose exposes ports needs removed
        refine .inr ⟨i, hi, ?_⟩
        cases side
        · exact .inl (atPort.trans (congrArg Prod.fst (pairs i hi)))
        · exact .inr (atPort.trans (congrArg Prod.snd (pairs i hi)))
      · apply Or.inl (ih.2 v inside ?_)
        intro t present
        rcases List.mem_append.mp present with old | last
        · exact settled _ (List.mem_append_left _ old)
        · have equal : t = task := by simpa using last
          exact equal.symm ▸ needs

/-- Once the work stack empties, every finite mate slot equals the
proposed recursively lifted matching. -/
theorem MatchingRebaseLiveQueue.finalMates {base s : ArithmeticState} {archive : MatchingRebaseArchive base}
    {initial : List MatchingRebaseTask} {target : ℕ → ℕ} (closed : MatchingRebaseLiveQueue archive initial [] s)
    (plan : MatchingRebaseLiftTarget archive target) (ports : ∀ t ∈ initial, t.port = plan.port t.node)
    (boundary : ∀ v < base.nr 55, (∀ t ∈ initial, ¬t.needs v) → base.nm (base.nr 50 + v) = target v) :
    ∀ v < base.nr 55, s.nm (base.nr 50 + v) = target v := by
  obtain ⟨m, history, table⟩ := closed.mate
  intro v hi
  exact (table v hi).trans ((history.realizes plan ports boundary).2 v hi (by simp))


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseLiftTarget

/-! matching/MatchingAugmentLiveQueue.lean -/
section RppSource_MatchingAugmentLiveQueue
namespace VehicleRoutingSurvey.Routing







theorem MatchingPreparedRebase.starts {base : ArithmeticState} {initial : List MatchingRebaseTask}
    (prepared : MatchingPreparedRebase base initial) :
    MatchingRebaseLiveQueue prepared.registry initial initial (matchingRebaseQueueSnapshot base) := by
  have ready := MatchingRebaseLiveQueue.start prepared.registry initial prepared.queue prepared.tasks
    prepared.distinct prepared.unique prepared.allocated
  apply ready.transport (t := matchingRebaseQueueSnapshot base) _ (by simp [matchingRebaseQueueSnapshot]) rfl
  intro r hr
  have away : r ≠ 43 := by simp [matchingRebaseLayoutRegisters] at hr; omega
  exact Function.update_of_ne away _ _




end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentLiveQueue

/-! matching/MatchingRebasePendingIds.lean -/
section RppSource_MatchingRebasePendingIds
namespace VehicleRoutingSurvey.Routing

/-- The rotation pushes every nontrivial child subtree exactly once, so
the only allocated ID disappearing from the pending forest is the one popped. -/
theorem matchingRebaseCycleTaskPrefix_ids (c : MatchingMemberTree) (choose : MatchingMemberJob → ℕ)
    (free : ℕ) (odd : Odd c.arity) :
    (matchingRebaseQueueIds (matchingRebaseCycleTaskPrefix c choose free ((c.arity-1)/2))).Perm c.registryIds := by
  have flatten (js : List MatchingMemberJob) : matchingRebaseQueueIds (js.filterMap (MatchingMemberJob.rebaseTask choose)) =
      js.flatMap (fun j => j.tree.registryIds) := by
    induction js with
    | nil => rfl
    | cons j t ih =>
      cases form : j.children with
      | none => simpa [MatchingMemberJob.rebaseTask, form, MatchingMemberJob.tree, MatchingMemberTree.registryIds] using ih
      | some sub =>
        simp [matchingRebaseQueueIds] at ih
        simp [MatchingMemberJob.rebaseTask,MatchingRebaseTask.registryIds,MatchingMemberJob.tree,
          matchingRebaseQueueIds,form,MatchingMemberTree.registryIds, ih]
  rw [matchingRebaseCycleTaskPrefix_all _ _ _ odd, flatten, ← c.jobs_registryIds none]
  exact (List.rotate_perm (c.jobs none) free).flatMap_right _

theorem matchingRebaseFrontier_keepsId {task : MatchingRebaseTask} (earlier : List MatchingRebaseTask)
    (choose : MatchingMemberJob → ℕ) (free : ℕ) (odd : Odd task.children.arity) (n : ℕ) (diff : n ≠ task.node) :
    let added := matchingRebaseCycleTaskPrefix task.children choose free ((task.children.arity-1)/2)
    n ∈ matchingRebaseQueueIds (earlier ++ added) ↔ n ∈ matchingRebaseQueueIds (earlier ++ [task]) := by
  intro added
  have same := (matchingRebaseCycleTaskPrefix_ids task.children choose free odd).mem_iff (a := n)
  change n ∈ matchingRebaseQueueIds added ↔ n ∈ task.children.registryIds at same
  simp only [matchingRebaseQueueIds,List.flatMap_append,List.mem_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,MatchingRebaseTask.registryIds,List.mem_cons,diff,false_or] at same ⊢
  rw [same]

theorem MatchingRebaseArchive.tree_unique {s : ArithmeticState} (archive : MatchingRebaseArchive s)
    {n : ℕ} {x y : MatchingMemberTree} (hx : archive.live n x) (hy : archive.live n y) : x = y := by
  have left := (archive.record _ _ hx).members
  have right := (archive.record _ _ hy).members
  have same := MatchingMemberTree.eq_of_encoded_rootKeys left.proper right.proper left.encoded right.encoded rfl
  injection same


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebasePendingIds

/-! matching/MatchingRebaseFinishedRows.lean -/
section RppSource_MatchingRebaseFinishedRows
namespace VehicleRoutingSurvey.Routing

private theorem matchingRebaseFrontier_pop {task : MatchingRebaseTask} {earlier : List MatchingRebaseTask}
    (choose : MatchingMemberJob → ℕ) (free : ℕ) (odd : Odd task.children.arity)
    (distinct : (matchingRebaseQueueIds (earlier ++ [task])).Nodup) :
    let added := matchingRebaseCycleTaskPrefix task.children choose free ((task.children.arity-1)/2)
    (matchingRebaseQueueIds (earlier ++ added)).Nodup ∧ task.node ∉ matchingRebaseQueueIds (earlier ++ added) := by
  intro added
  have perm := matchingRebaseCycleTaskPrefix_ids task.children choose free odd
  change (matchingRebaseQueueIds added).Perm task.children.registryIds at perm
  have split : (matchingRebaseQueueIds earlier ++ task.node :: task.children.registryIds).Nodup := by
    simpa only [matchingRebaseQueueIds,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      MatchingRebaseTask.registryIds] using distinct
  obtain ⟨earlierUnique,tail,separate⟩ := List.nodup_append.mp split
  obtain ⟨absent,unique⟩ := List.nodup_cons.mp tail
  change (matchingRebaseQueueIds (earlier ++ added)).Nodup ∧ _
  simp only [matchingRebaseQueueIds,List.flatMap_append]
  refine ⟨List.nodup_append.mpr ⟨earlierUnique,perm.nodup_iff.mpr unique,?_⟩,?_⟩
  · intro i before j child eq
    exact separate i before j (List.mem_cons_of_mem _ (perm.mem_iff.mp child)) eq
  · intro found
    rcases List.mem_append.mp found with was | later
    · exact separate _ was _ (by simp) rfl
    · exact absent (perm.mem_iff.mp later)

/-- With a prescribed mathematical port map, every completed node has
exactly its new immediate child representatives. The other three words of
each physical row and all unprocessed or unselected rows retain their values. -/
theorem MatchingRebaseRecordHistory.realizesRows {base : ArithmeticState} {archive : MatchingRebaseArchive base}
    {initial pending : List MatchingRebaseTask} {mate target : ℕ → ℕ} {rows : ℕ → ℕ → MatchingCycleChild}
    (history : MatchingRebaseRecordHistory archive initial pending mate rows)
    (plan : MatchingRebaseLiftTarget archive target) (unique : (matchingRebaseQueueIds initial).Nodup)
    (ports : ∀ t ∈ initial, t.port = plan.port t.node) :
    (matchingRebaseQueueIds pending).Nodup ∧ (∀ n ∈ matchingRebaseQueueIds pending, n ∈ matchingRebaseQueueIds initial) ∧
      (∀ t ∈ pending, t.port = plan.port t.node) ∧
      (∀ n, n ∉ matchingRebaseQueueIds initial → ∀ i, rows n i = matchingRebaseRowsAt base base n i) ∧
      ∀ n c, archive.live n c → ∀ i < c.arity,
        rows n i = if n ∈ matchingRebaseQueueIds initial ∧ n ∉ matchingRebaseQueueIds pending then
          {matchingRebaseRowsAt base base n i with representative := matchingRebasePortAt c (MatchingMemberJob.liftPort plan.port) i}
        else matchingRebaseRowsAt base base n i := by
  classical
  induction history with
  | start => exact ⟨unique,fun _ h => h,ports,fun _ _ _ => rfl,fun _ _ _ _ _ => by simp⟩
  | @next earlier task earlierMate oldRows previous known free belongs choose members exposes pairs ih =>
    let c := task.children
    let added := matchingRebaseCycleTaskPrefix c choose free ((c.arity-1)/2)
    have old := ih.2.2.1 task (by simp)
    have odd := (archive.record _ _ known).odd
    obtain ⟨hf,leaf⟩ := belongs
    have planned : plan.port task.node ∈ ((c.jobs none)[free]'hf).tree.leaves := old ▸ leaf
    have prescribed := plan.pairs _ _ known free hf planned
    have choices (j : MatchingMemberJob) (hj : j ∈ c.jobs none) : choose j = j.liftPort plan.port := by
      apply matchingRebaseChosen_eq c odd choose (MatchingMemberJob.liftPort plan.port) hf _ _ j hj
      · exact (exposes.trans old).trans (plan.inherits _ _ known free hf planned).symm
      · intro i hi b
        have eq := (pairs i hi).trans (prescribed i hi).1.symm
        cases b
        · exact congrArg Prod.fst eq
        · exact congrArg Prod.snd eq
    have was : task.node ∈ matchingRebaseQueueIds (earlier ++ [task]) :=
      List.mem_flatMap.mpr ⟨task,by simp, List.mem_cons_self ..⟩
    have seen := ih.2.1 _ was
    have pop := matchingRebaseFrontier_pop choose free odd ih.1
    have other (n : ℕ) (diff : n ≠ task.node) := matchingRebaseFrontier_keepsId earlier choose free odd n diff
    refine ⟨pop.1,?_,?_,?_,?_⟩
    · intro n hn
      have ne : n ≠ task.node := fun eq => pop.2 (eq ▸ hn)
      exact ih.2.1 n ((other n ne).mp hn)
    · intro t listed
      rcases List.mem_append.mp listed with first | pushed
      · exact ih.2.2.1 t (List.mem_append_left _ first)
      · rw [matchingRebaseCycleTaskPrefix_all _ _ _ odd] at pushed
        obtain ⟨j,hj,queued⟩ := List.mem_filterMap.mp pushed
        have atJ := choices j (List.mem_rotate.mp hj)
        cases kind : j.children with
        | none => simp [MatchingMemberJob.rebaseTask,kind] at queued
        | some sub =>
          have eq : (⟨j.node,choose j,sub⟩ : MatchingRebaseTask) = t := by simpa [MatchingMemberJob.rebaseTask,kind] using queued
          subst t
          simpa [MatchingMemberJob.liftPort,kind] using atJ
    · intro n out i
      have diff : n ≠ task.node := fun eq => out (eq.symm ▸ seen)
      simpa [matchingRebaseRowsNext,diff] using ih.2.2.2.1 n out i
    · intro n tree live i hi
      by_cases same : n = task.node
      · subst n
        have identical := archive.tree_unique live known
        subst tree
        have done : task.node ∈ matchingRebaseQueueIds initial ∧ task.node ∉ matchingRebaseQueueIds (earlier ++ added) := ⟨seen,pop.2⟩
        have before := ih.2.2.2.2 _ _ known i hi
        have on : i < (c.jobs none).length := (c.jobs_length none).symm ▸ hi
        have eq := choices _ (List.getElem_mem on)
        simp (config := { zetaDelta := true }) only
          [matchingRebaseRowsNext, if_pos done, matchingRebasePortAt, dif_pos on, eq]
        exact congrArg (fun r : MatchingCycleChild => {r with representative := ((c.jobs none)[i]).liftPort plan.port})
          (by simpa only [was, not_true_eq_false, and_false, if_false] using! before)
      · have eq := other n same
        simpa only [matchingRebaseRowsNext,if_neg same,eq] using ih.2.2.2.2 n tree live i hi




theorem MatchingRebaseLiveQueue.finalRows {base s out : ArithmeticState} {archive : MatchingRebaseArchive base}
    {initial : List MatchingRebaseTask} {target : ℕ → ℕ}
    (ready : MatchingRebaseLiveQueue archive initial [] s) (plan : MatchingRebaseLiftTarget archive target)
    (unique : (matchingRebaseQueueIds initial).Nodup)
    (ports : ∀ t ∈ initial, t.port = plan.port t.node) (memory : out.nm = s.nm) :
    MatchingRebaseCompletedRows plan initial out := by
  obtain ⟨mate,rows,history,_,stored⟩ := ready.effects
  have realized := history.realizesRows plan unique ports
  refine ⟨fun a h => (congrFun memory a).trans (ready.below a h),
    fun a h => (congrFun memory a).trans (ready.headers a h), ?_, ?_⟩
  · intro n c live i hi
    have bounds := archive.allocated n c live
    have count : base.nm (base.nr 78+n) = c.arity := by
      simpa [matchingRebaseNodeState] using (archive.record n c live).members.encoded.1
    rw [show matchingRebaseRowsAt base out n i = matchingRebaseRowsAt base s n i from
      by simp only [matchingRebaseRowsAt,memory], stored n bounds.1 bounds.2 i (count.symm ▸ hi)]
    simpa [matchingRebaseQueueIds] using realized.2.2.2.2 n c live i hi
  · intro n lo hi absent i hi'
    rw [show matchingRebaseRowsAt base out n i = matchingRebaseRowsAt base s n i from
      by simp only [matchingRebaseRowsAt,memory], stored n lo hi i hi']
    exact realized.2.2.2.1 n absent i


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseFinishedRows

/-! matching/MatchingAugmentTargetMates.lean -/
section RppSource_MatchingAugmentTargetMates
namespace VehicleRoutingSurvey.Routing



private def matchingLiftQueue (target : ℕ → ℕ) (input : ArithmeticState) (size : ℕ)
    (observed : ∀ base jobs, MatchingPreparedLift base jobs target → Prop)
    (pending : List MatchingRebaseTask) (s : ArithmeticState) : Prop :=
  ∃ base initial, base.nr 50 = input.nr 50 ∧ base.nr 55 = size ∧
    (∀ a < input.nr 50, base.nm a = input.nm a) ∧
    ∃ lift : MatchingPreparedLift base initial target,
      observed base initial lift ∧ MatchingRebaseLiveQueue lift.registry initial pending s

private theorem matchingLiftQueue_interface (target : ℕ → ℕ) (input : ArithmeticState) (size : ℕ)
    (observed : ∀ base jobs, MatchingPreparedLift base jobs target → Prop) :
    MatchingRebaseQueueInterface (matchingLiftQueue target input size observed) := by
  constructor
  · rintro jobs s ⟨base, initial, _, _, _, lift, _, frame⟩
    exact (MatchingRebaseLiveQueue.interface lift.registry initial).size jobs s frame
  · rintro earlier task s ⟨base, initial, _, _, _, lift, _, frame⟩
    exact (MatchingRebaseLiveQueue.interface lift.registry initial).input earlier task s frame
  · rintro earlier task s loaded t free ⟨base, initial, a, k, low, lift, seen, frame⟩ view count bytes real regs keeps
    obtain ⟨added, work, next⟩ := (MatchingRebaseLiveQueue.interface lift.registry initial).update
      earlier task s loaded t free frame view count bytes real regs keeps
    exact ⟨added, work, base, initial, a, k, low, lift, seen, next⟩

/-- The verified augmentation writes the prescribed lifted matching directly
in the original mate slots and advances the saved real duals. -/
theorem matchingAugmentationHandlerBlock_targetMates {k : ℕ} {s emitted : ArithmeticState}
    {rows : List (Fin k × Fin k)} {emitSteps : ℕ} (target : ℕ → ℕ)
    {observed : ∀ base jobs, MatchingPreparedLift base jobs target → Prop}
    (emit : BlockRuns writeAugmentationCrossingsBlock emitSteps s emitted)
    (emittedLive : emitted.halted = false) (emittedRows : AugmentationCrossingsReady rows s emitted)
    (emitBound : emitSteps ≤ 17 * k + 21) (dimension : s.nr 55 = k) (one : s.nr 9 = 1)
    (rolesBelow : s.nr 51 + k ≤ s.nr 86) (repsBelow : s.nr 57 + k ≤ s.nr 86)
    (nodesBelow : s.nr 74 + k ≤ s.nr 86) (originalMap : ∀ i < k, s.nm (s.nr 57 + i) < k)
    (layout : AugmentationInstallLayout k (augmentationCrossingSeed s k))
    (initial : ∀ dual ticks base, BlockRuns prepareMatchingAugmentationBlock ticks s dual →
      AugmentationPreRebaseReady rows {dual with pc := 0} base →
      ∃ (jobs : List MatchingRebaseTask) (lift : MatchingPreparedLift base jobs target),
        observed base jobs lift ∧ matchingRebaseQueueWork jobs ≤ k) :
    ∃ t steps, BlockRuns matchingAugmentationHandlerBlock steps s t ∧
      t.halted = false ∧ steps + (34 * k + 61) ≤ 512 * (k ^ 2 + 1) ∧
      t.nr 1 = 0 ∧ t.nr 33 = 0 ∧ t.nr 82 = 0 ∧
      t.rr 15 = s.rr 15 + s.rr 1 ∧ t.rm = iterateBlossomDuals {s with rm := advancedEffectiveMemory s} k ∧
      (∀ v < k, t.nm (s.nr 50 + v) = target v) ∧ (∀ a < s.nr 50, t.nm a = s.nm a) ∧
      ∃ (base : ArithmeticState) (jobs : List MatchingRebaseTask) (lift : MatchingPreparedLift base jobs target),
        observed base jobs lift ∧ MatchingRebaseCompletedRows lift.lift jobs t := by
  obtain ⟨prepared, ticks, _, checked, _, sameByte, _, _, _, dim, _⟩ :=
    prepareMatchingAugmentationBlock_correct emit emittedLive emittedRows emitBound dimension one rolesBelow
      repsBelow nodesBelow originalMap
  have prefixRegisters (r : ℕ) (safe : r ∉ [0, 3, 4, 5, 6, 7, 10, 11, 12, 14, 15, 16, 17, 18, 19, 87] := by decide) :
      prepared.nr r = s.nr r :=
    prepareMatchingAugmentationBlock_preserves checked r safe
  have mates : s.nr 50 + k ≤ s.nr 57 := by simpa [augmentationCrossingSeed] using layout.matesBeforeMap
  obtain ⟨t, rebased, steps, run, running, budget, stopped, stage, empty,
    ⟨base, jobs, address, size, low, lift, seen, closed⟩, memory, time, real, _⟩ :=
    matchingAugmentationHandlerBlock_correct emit emittedLive emittedRows emitBound dimension one
      rolesBelow repsBelow nodesBelow originalMap layout (matchingLiftQueue_interface target s k observed) (by
        intro dual ticks base ran ready
        obtain ⟨jobs, lift, seen, work⟩ := initial dual ticks base ran ready
        have sameState : dual = prepared := (ran.same_exit checked).2
        have address := (ready.fixed 50 (by decide)).trans
          ((congrArg (fun m : ArithmeticState => m.nr 50) sameState).trans (prefixRegisters 50))
        have size := (ready.fixed 55 (by decide)).trans
          ((congrArg (fun m : ArithmeticState => m.nr 55) sameState).trans dim)
        have low (a : ℕ) (ha : a < s.nr 50) : base.nm a = s.nm a := by
          have bound : a < dual.nr 50 := by rwa [sameState, prefixRegisters 50]
          have byte : dual.nm a = emitted.nm a := (congrArg (fun m : ArithmeticState => m.nm a) sameState).trans
            (congrFun sameByte a)
          exact (ready.preservedPrefix a bound).trans (byte.trans (emittedRows.natural a (.inl (by omega))))
        exact ⟨jobs, ⟨base, jobs, address, size, low, lift, seen, lift.toMatchingPreparedRebase.starts⟩, work⟩)
  refine ⟨t, steps, run, running, budget, stopped, stage, empty, time, real, ?_, ?_, ?_⟩
  · intro v hi
    rw [memory, ← address]
    exact closed.finalMates lift.lift lift.ports lift.boundary v (size.symm ▸ hi)
  · intro a ha
    exact (congrFun memory a).trans ((closed.below a (by rwa [address])).trans (low a ha))
  · exact ⟨base, jobs, lift, seen, closed.finalRows lift.lift lift.unique lift.ports memory⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentTargetMates

/-! matching/MatchingAugmentPrimalOutput.lean -/
section RppSource_MatchingAugmentPrimalOutput
namespace VehicleRoutingSurvey.Routing







/-- Transfer the archived lift of the new primal matching into the exact
RAM state consumed by the next weighted-matching stage. -/
theorem matchingAugmentationHandlerBlock_primal {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {caller s emitted : ArithmeticState}
    {rows : List (Fin k × Fin k)} {emitSteps : ℕ}
    {observed : ∀ base jobs, MatchingPreparedLift base jobs (compactPrimalMateWord next) → Prop}
    (oldMemory : CompactMatchingPrimalDualMemory old caller s)
    (emit : BlockRuns writeAugmentationCrossingsBlock emitSteps s emitted)
    (emittedLive : emitted.halted = false) (emittedRows : AugmentationCrossingsReady rows s emitted)
    (emitBound : emitSteps ≤ 17 * k + 21) (one : s.nr 9 = 1)
    (rolesBelow : s.nr 51 + k ≤ s.nr 86) (repsBelow : s.nr 57 + k ≤ s.nr 86)
    (nodesBelow : s.nr 74 + k ≤ s.nr 86) (originalMap : ∀ i < k, s.nm (s.nr 57 + i) < k)
    (layout : AugmentationInstallLayout k (augmentationCrossingSeed s k))
    (effective : caller.nr 64 ≤ s.nr 62) (blossom : caller.nr 64 ≤ s.nr 75)
    (initial : ∀ dual ticks base, BlockRuns prepareMatchingAugmentationBlock ticks s dual →
      AugmentationPreRebaseReady rows {dual with pc := 0} base →
      ∃ (jobs : List MatchingRebaseTask) (lift : MatchingPreparedLift base jobs (compactPrimalMateWord next)),
        observed base jobs lift ∧ matchingRebaseQueueWork jobs ≤ k) :
    ∃ t steps, BlockRuns matchingAugmentationHandlerBlock steps s t ∧ t.halted = false ∧
      steps + (34 * k + 61) ≤ 512 * (k ^ 2 + 1) ∧ t.nr 1 = 0 ∧ t.nr 33 = 0 ∧ t.nr 82 = 0 ∧
      t.rr 15 = s.rr 15 + s.rr 1 ∧ t.rm = iterateBlossomDuals {s with rm := advancedEffectiveMemory s} k ∧
      CompactMatchingPrimalDualMemory next caller t ∧
      ∃ (base : ArithmeticState) (jobs : List MatchingRebaseTask) (lift : MatchingPreparedLift base jobs (compactPrimalMateWord next)),
        observed base jobs lift ∧ MatchingRebaseCompletedRows lift.lift jobs t := by
  obtain ⟨t, ticks, ran, live, costBound, flag, done, empty, time, real, mates, natural, records⟩ :=
    matchingAugmentationHandlerBlock_targetMates (compactPrimalMateWord next) emit emittedLive emittedRows emitBound
      oldMemory.dimension one rolesBelow repsBelow nodesBelow originalMap layout initial
  have stable := matchingAugmentationHandlerBlock_preserves ran
  refine ⟨t, ticks, ran, live, costBound, flag, done, empty, time, real,
    ⟨(stable 55 (by decide)).trans oldMemory.dimension, (stable 56 (by decide)).trans oldMemory.oddMap,
      (stable 50 (by decide)).symm ▸ oldMemory.mateAbove, ?_, ?_, ?_, ?_⟩, records⟩
  · intro v
    rw [stable 50 (by decide), mates v.val v.isLt]
    simp [compactPrimalMateWord, v.isLt]
  · intro r large
    exact (stable r (by simp; omega)).trans (oldMemory.saved r large)
  · intro a below
    exact (natural a (below.trans_le oldMemory.mateAbove)).trans (oldMemory.natural a below)
  · intro a below
    rw [real, ← oldMemory.dimension]
    exact (matchingEventDualMemory_keeps_prefix s _ a below effective blossom).trans (oldMemory.real a below)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentPrimalOutput

open VehicleRoutingSurvey.Routing SupplyChainTheory in
theorem solution : (fun {P : Prop} (_ : P) => P) (@VehicleRoutingSurvey.Routing.matchingAugmentationHandlerBlock_primal) :=
  @VehicleRoutingSurvey.Routing.matchingAugmentationHandlerBlock_primal
