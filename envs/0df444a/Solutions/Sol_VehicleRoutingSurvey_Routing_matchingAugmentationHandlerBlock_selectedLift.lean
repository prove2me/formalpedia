-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.matchingAugmentationHandlerBlock_selectedLift
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T16:03:25.783537+00:00
-- url     : https://prove2.me/submissions/b10e0de9-d11b-45fc-bef2-15113775b2f7

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces
import Theorems.Thm_VehicleRoutingSurvey_Routing_matchingAugmentationHandlerBlock_primal
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

/-! matching/WeightedCertificate.lean -/
section RppSource_WeightedCertificate
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

theorem perfectMatching_sum_vertices {n : ℕ} {O : Finset (Fin n)}
    {M : Finset (Sym2 (Fin n))} (perfect : IsPerfectMatchingOn O M)
    {R : Type*} [AddCommMonoid R] (f : Fin n → R) :
    (∑ e ∈ M, ∑ v ∈ e.toFinset, f v) = ∑ v ∈ O, f v := by
  have cover : M.biUnion Sym2.toFinset = O := Finset.ext fun v =>
    ⟨fun hv =>
        let ⟨e, memM, endpoint⟩ := Finset.mem_biUnion.mp hv
        (perfect.1 e memM).2 v (Sym2.mem_toFinset.mp endpoint),
      fun hv =>
        let ⟨e, incidence, _⟩ := perfect.2 v hv
        Finset.mem_biUnion.mpr ⟨e, incidence.1, Sym2.mem_toFinset.mpr incidence.2⟩⟩
  have disjoint : (M : Set (Sym2 (Fin n))).PairwiseDisjoint Sym2.toFinset := by
    intro e he f hf distinct
    apply Finset.disjoint_left.mpr
    intro v ev fv
    have ev' := Sym2.mem_toFinset.mp ev
    have fv' := Sym2.mem_toFinset.mp fv
    obtain ⟨g, _, unique⟩ := perfect.2 v ((perfect.1 e he).2 v ev')
    exact distinct ((unique e ⟨he, ev'⟩).trans (unique f ⟨hf, fv'⟩).symm)
  calc
    _ = ∑ v ∈ M.biUnion Sym2.toFinset, f v := (Finset.sum_biUnion disjoint).symm
    _ = _ := congrArg (fun vs => ∑ v ∈ vs, f v) cover















end VehicleRoutingSurvey.Routing
end RppSource_WeightedCertificate

/-! matching/WeightedRootEvent.lean -/
section RppSource_WeightedRootEvent
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



theorem perfectMatching_card_twice {n : ℕ} {O : Finset (Fin n)}
    {M : Finset (Sym2 (Fin n))} (perfect : IsPerfectMatchingOn O M) :
    O.card = 2 * M.card := by
  calc
    O.card = ∑ v ∈ O, (1 : ℕ) := by simp
    _ = ∑ e ∈ M, ∑ v ∈ e.toFinset, (1 : ℕ) := (perfectMatching_sum_vertices perfect _).symm
    _ = ∑ _e ∈ M, (2 : ℕ) := Finset.sum_congr rfl fun e he => by
      simpa using Sym2.card_toFinset_of_not_isDiag e (perfect.1 e he).1
    _ = _ := by simp [Nat.mul_comm]





end VehicleRoutingSurvey.Routing
end RppSource_WeightedRootEvent

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





theorem firstSharedAncestor_eq_none_iff {α : Type*} [DecidableEq α] {left right : List α} :
    firstSharedAncestor left right = none ↔ ∀ v ∈ right, v ∉ left := by
  simp only [firstSharedAncestor, List.find?_eq_none, markForestTrace_true]





end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestAncestor

/-! matching/MatchingWarmPrimal.lean -/
section RppSource_MatchingWarmPrimal
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory











theorem CompactMatchingPartition.mem_activeRepresentatives {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (v : Fin k) :
    v ∈ part.activeRepresentatives ↔ part.representative v = v := by
  simp [CompactMatchingPartition.activeRepresentatives]

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

/-! matching/MatchingMemberTree.lean -/
section RppSource_MatchingMemberTree
namespace VehicleRoutingSurvey.Routing



namespace MatchingMemberTree

















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







theorem jobs_frontier_vertices (tree : MatchingMemberTree) (owner : Option ℕ) :
    (MatchingMemberJob.frontier (tree.jobs owner)).map Prod.fst = tree.leaves := by
  induction tree with
  | nil => rfl
  | leaf v siblings ih =>
    simpa [jobs, leaves, MatchingMemberJob.frontier, MatchingMemberJob.assignments] using congrArg (v :: ·) ih
  | blossom r node children siblings _ ih =>
    simpa [jobs, leaves, MatchingMemberJob.frontier, MatchingMemberJob.assignments, List.map_map, Function.comp_def] using
      congrArg (children.leaves ++ ·) ih



end MatchingMemberTree

namespace MatchingMemberJob























end MatchingMemberJob

end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberStack

/-! matching/MatchingMemberWalkRAM.lean -/
section RppSource_MatchingMemberWalkRAM
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096













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







end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberWalkRAM

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

/-! matching/TightBlossomRematch.lean -/
section RppSource_TightBlossomRematch
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

theorem alternatingEdges_tight {n : ℕ} (tight : Sym2 (Fin n) → Prop)
    (vertices : List (Fin n)) (chain : vertices.IsChain (fun u v => tight s(u, v))) :
    ∀ e ∈ alternatingEdges vertices, tight e := by
  induction vertices using List.twoStepInduction with
  | nil => simp [alternatingEdges]
  | singleton => simp [alternatingEdges]
  | cons_cons u v rest ih _ =>
    intro e he
    rcases List.mem_cons.mp he with rfl | inRest
    · exact (List.isChain_cons_cons.mp chain).1
    · exact ih (List.isChain_cons_cons.mp chain).2.tail e inRest

/-- A simple cycle is tight if its edges are tight, including the wraparound edge. -/
def CycleEdgesTight {n : ℕ} (vertices : List (Fin n)) (tight : Sym2 (Fin n) → Prop) : Prop :=
  ∀ i (hi : i < vertices.length),
    tight s(vertices[i], vertices[(i + 1) % vertices.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi)))

private theorem rotate_chain_of_cycle_tight {n : ℕ} {vertices : List (Fin n)}
    {tight : Sym2 (Fin n) → Prop} (cycleTight : CycleEdgesTight vertices tight)
    (positive : 0 < vertices.length) (base : ℕ) :
    (vertices.rotate base).IsChain (fun u v => tight s(u, v)) := by
  apply List.isChain_iff_getElem.mpr
  intro j _
  simp only [List.getElem_rotate]
  have stepEq : ((j + base) % vertices.length + 1) % vertices.length =
      (j + 1 + base) % vertices.length := by
    rw [Nat.mod_add_mod, Nat.add_right_comm j base 1]
  have successor : vertices[((j + base) % vertices.length + 1) % vertices.length]'(Nat.mod_lt _ positive) =
      vertices[(j + 1 + base) % vertices.length]'(Nat.mod_lt _ positive) := getElem_congr_idx stepEq
  simpa only [successor] using cycleTight ((j + base) % vertices.length) (Nat.mod_lt _ positive)



theorem rematchBlossomCycle_spec {n : ℕ} {vertices : List (Fin n)} {base : ℕ}
    (baseIndex : base < vertices.length) (distinct : vertices.Nodup) (odd : Odd vertices.length)
    (tight : Sym2 (Fin n) → Prop) (cycleTight : CycleEdgesTight vertices tight) :
    IsPerfectMatchingOn (vertices.toFinset.erase vertices[base]) (rematchBlossomCycle vertices base) ∧
      ∀ e ∈ rematchBlossomCycle vertices base, tight e := by
  have positive := Nat.zero_lt_of_lt baseIndex
  have rotatedDistinct := (List.nodup_rotate (n := base)).mpr distinct
  have rotatedLength := List.length_rotate vertices base
  have chosenHead := List.head?_rotate baseIndex
  rw [List.getElem?_eq_getElem baseIndex] at chosenHead
  have setSame : (vertices.rotate base).toFinset = vertices.toFinset := Finset.ext fun _ => by
    simp only [List.mem_toFinset, List.mem_rotate]
  have chain := (rotate_chain_of_cycle_tight cycleTight positive base).tail
  refine ⟨?_, fun e he => alternatingEdges_tight tight _ chain e (List.mem_toFinset.mp he)⟩
  cases rotation : vertices.rotate base with
  | nil => simp [rotation] at chosenHead
  | cons first rest =>
    have headEq : first = vertices[base] := by simpa only [rotation, List.head?_cons, Option.some.injEq] using chosenHead
    have restEven : rest.length % 2 = 0 := by
      rw [rotation, List.length_cons] at rotatedLength
      have oddCard := Nat.odd_iff.mp odd
      omega
    have restDistinct : rest.Nodup := by
      rw [rotation] at rotatedDistinct
      exact rotatedDistinct.of_cons
    have firstFresh : first ∉ rest := by
      rw [rotation] at rotatedDistinct
      exact (List.nodup_cons.mp rotatedDistinct).1
    have remainder : rest.toFinset = vertices.toFinset.erase vertices[base] := Finset.ext fun v => by
      simp only [← setSame, rotation, ← headEq, Finset.mem_erase, List.mem_toFinset, List.mem_cons]
      exact ⟨fun inside => ⟨fun h => firstFresh (h ▸ inside), Or.inr inside⟩,
        fun ⟨outside, inside⟩ => inside.resolve_left outside⟩
    simpa only [rematchBlossomCycle, rotation, List.tail_cons, ← remainder] using
      (alternatingEdges_perfect rest restDistinct restEven).2

end VehicleRoutingSurvey.Routing
end RppSource_TightBlossomRematch

/-! matching/TightBlossomExpansion.lean -/
section RppSource_TightBlossomExpansion
namespace VehicleRoutingSurvey.Routing







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





end VehicleRoutingSurvey.Routing
end RppSource_TightBlossomExpansion

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















end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowHandler

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

theorem parent_step_alternates {α : Type*} {state : AlternatingForestState α}
    {mate : α → Option α} {tight : α → α → Prop} (valid : state.valid mate tight)
    {child parent : α} (link : (state.role child).parent = some parent) :
    (state.role child).outerTag ≠ (state.role parent).outerTag := by
  rcases parent_step_roles valid link with ⟨_, a, b, _⟩ | ⟨_, a, b⟩ <;>
    simp [a, b, AlternatingForestRole.outerTag]







theorem alternating_chain_parity {α : Type*} (tag : α → Bool) (last : α)
    (before : List α) (chain : (before ++ [last]).IsChain (fun a b => tag a ≠ tag b)) :
    before.length % 2 = 0 ↔ ((before ++ [last]).head?.map tag = some (tag last)) := by
  induction before with
  | nil => simp
  | cons first rest ih =>
    have nonempty : rest ++ [last] ≠ [] := by simp
    let next := (rest ++ [last]).head nonempty
    have restHead : (rest ++ [last]).head? = some next := List.head?_eq_some_head nonempty
    have pieces : (∀ y ∈ (rest ++ [last]).head?, tag first ≠ tag y) ∧
        (rest ++ [last]).IsChain (fun a b => tag a ≠ tag b) := List.isChain_cons.mp chain
    have flips := pieces.1 next (by simp [restHead])
    have steps := ih pieces.2
    simp only [restHead, Option.map_some, Option.some.injEq] at steps
    simp only [List.length_cons, List.cons_append, List.head?_cons, Option.map_some, Option.some.injEq]
    cases a : tag first <;> cases b : tag next <;> cases c : tag last <;>
      simp [a, b, c] at flips steps ⊢ <;> omega















end VehicleRoutingSurvey.Routing
end RppSource_AlternatingContractionParity

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

/-! matching/MatchingAugmentCrossingCell.lean -/
section RppSource_MatchingAugmentCrossingCell
namespace VehicleRoutingSurvey.Routing





def augmentationCrossingCursor (s : ArithmeticState) : ℕ := s.nr 86 + (s.nr 87 + s.nr 87)

def appendAugmentationCrossingMemory (s : ArithmeticState) (first second : ℕ) : ℕ → ℕ :=
  Function.update (Function.update s.nm (augmentationCrossingCursor s) first)
    (augmentationCrossingCursor s + 1) second

theorem appendAugmentationCrossingPair_correct (first second : ℕ) {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1)
    (firstAway : first ≠ 5) (secondAway : second ≠ 5) :
    ∃ t, BlockRuns (appendAugmentationCrossingPair first second) 6 s t ∧ t.halted = false ∧
      t.nr 87 = s.nr 87 + 1 ∧ t.nm = appendAugmentationCrossingMemory s (s.nr first) (s.nr second) ∧
      (∀ r, r ≠ 5 → r ≠ 87 → t.nr r = s.nr r) ∧ t.rr = s.rr ∧ t.rm = s.rm := by
  let t := (arithmeticStep (appendAugmentationCrossingPair first second))^[6] s
  have ready : t.halted = false := by
    simp [t, appendAugmentationCrossingPair, arithmeticStep, Function.iterate_succ_apply', entry, running]
  have exit : t.pc = (appendAugmentationCrossingPair first second).length := by
    simp [t, appendAugmentationCrossingPair, arithmeticStep, Function.iterate_succ_apply', entry, running]
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_, ?_⟩
  · simp [t, appendAugmentationCrossingPair, arithmeticStep, Function.iterate_succ_apply', entry, running, one]
  · simp [t, appendAugmentationCrossingPair, arithmeticStep, Function.iterate_succ_apply', entry, running,
      one, appendAugmentationCrossingMemory, augmentationCrossingCursor, Function.update_of_ne firstAway,
      Function.update_of_ne secondAway]
  · intro r address count
    simp [t, appendAugmentationCrossingPair, arithmeticStep, Function.iterate_succ_apply', entry, running,
      Function.update_of_ne address, Function.update_of_ne count]
  · simp [t, appendAugmentationCrossingPair, arithmeticStep, Function.iterate_succ_apply', entry, running]
  · simp [t, appendAugmentationCrossingPair, arithmeticStep, Function.iterate_succ_apply', entry, running]

theorem appendAugmentationCrossingMemory_first (s : ArithmeticState) (a b : ℕ) :
    appendAugmentationCrossingMemory s a b (augmentationCrossingCursor s) = a := by
  simp [appendAugmentationCrossingMemory]

theorem appendAugmentationCrossingMemory_second (s : ArithmeticState) (a b : ℕ) :
    appendAugmentationCrossingMemory s a b (augmentationCrossingCursor s + 1) = b := by
  simp [appendAugmentationCrossingMemory]

theorem appendAugmentationCrossingMemory_outside (s : ArithmeticState) (a b address : ℕ)
    (outside : address < augmentationCrossingCursor s ∨ augmentationCrossingCursor s + 2 ≤ address) :
    appendAugmentationCrossingMemory s a b address = s.nm address := by
  have first : address ≠ augmentationCrossingCursor s := by omega
  have second : address ≠ augmentationCrossingCursor s + 1 := by omega
  simp [appendAugmentationCrossingMemory, Function.update_of_ne first, Function.update_of_ne second]



private theorem readAugmentationTraceWitness_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1) :
    ∃ t, BlockRuns readAugmentationTraceWitness 7 s t ∧ t.halted = false ∧
      (t.nr 16, t.nr 17) = matchingForestWitnessAt s.nm (s.nr 90) (s.nm (s.nr 3 + s.nr 7)) ∧
      (∀ r, r ∉ [5, 15, 16, 17] → t.nr r = s.nr r) ∧
      t.nm = s.nm ∧ t.rr = s.rr ∧ t.rm = s.rm := by
  let t := (arithmeticStep readAugmentationTraceWitness)^[7] s
  have ready : t.halted = false := by
    simp [t, readAugmentationTraceWitness, arithmeticStep, Function.iterate_succ_apply', entry, running]
  have exit : t.pc = readAugmentationTraceWitness.length := by
    simp [t, readAugmentationTraceWitness, arithmeticStep, Function.iterate_succ_apply', entry, running]
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_, ?_⟩
  · simp [t, readAugmentationTraceWitness, matchingForestWitnessAt, forestWitnessAddress,
      arithmeticStep, Function.iterate_succ_apply', entry, running, one]
  · intro r away
    rw [show t.nr r = ((arithmeticStep readAugmentationTraceWitness)^[7] s).nr r from rfl]
    apply arithmeticRun_keeps_register
    simp [readAugmentationTraceWitness, naturalDestination] at away ⊢ <;> omega
  · simp [t, readAugmentationTraceWitness, arithmeticStep, Function.iterate_succ_apply', entry, running]
  · simp [t, readAugmentationTraceWitness, arithmeticStep, Function.iterate_succ_apply', entry, running]
  · simp [t, readAugmentationTraceWitness, arithmeticStep, Function.iterate_succ_apply', entry, running]

def orientAugmentationWitness {α : Type*} (flip : Bool) (edge : α × α) : α × α :=
  if flip then edge.swap else edge



theorem appendAugmentationTraceWitness_correct {k : ℕ} (flip : Bool) {s : ArithmeticState}
    {child : Fin k} {edge : Fin k × Fin k}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1)
    (chosen : s.nm (s.nr 3 + s.nr 7) = child.val)
    (witness : matchingForestWitnessAt s.nm (s.nr 90) child.val = (edge.1.val, edge.2.val)) :
    let ports := orientAugmentationWitness flip edge
    ∃ t, BlockRuns (appendAugmentationTraceWitness flip) 13 s t ∧ t.halted = false ∧
      t.nr 87 = s.nr 87 + 1 ∧ t.nm = appendAugmentationCrossingMemory s ports.1.val ports.2.val ∧
      (∀ r, r ∉ [5, 15, 16, 17, 87] → t.nr r = s.nr r) ∧ t.rr = s.rr ∧ t.rm = s.rm := by
  intro ports
  obtain ⟨m, reads, mReady, endpoints, fixed, mMem, mRR, mRM⟩ :=
    readAugmentationTraceWitness_correct entry running one
  let a := {m with pc := 0}
  have got : (a.nr 16, a.nr 17) = (edge.1.val, edge.2.val) := by
    change (m.nr 16, m.nr 17) = _
    rw [endpoints, chosen, witness]
  have writtenAt : augmentationCrossingCursor a = augmentationCrossingCursor s := by
    change m.nr 86 + (m.nr 87 + m.nr 87) = _
    simp only [fixed 86 (by decide), fixed 87 (by decide), augmentationCrossingCursor]
  have aOne : a.nr 6 = 1 := (fixed 6 (by decide)).trans one
  have firstAway : (if flip then 17 else 16) ≠ 5 := by cases flip <;> decide
  have secondAway : (if flip then 16 else 17) ≠ 5 := by cases flip <;> decide
  obtain ⟨b, writes, ready, count, memory, bFixed, bRR, bRM⟩ :=
    appendAugmentationCrossingPair_correct _ _ (s := a) rfl mReady aOne firstAway secondAway
  have out : b.nm = appendAugmentationCrossingMemory s ports.1.val ports.2.val := by
    rw [memory]
    have aMemory : a.nm = s.nm := mMem
    have firstPort : a.nr 16 = edge.1.val := congrArg Prod.fst got
    have secondPort : a.nr 17 = edge.2.val := congrArg Prod.snd got
    cases flip <;> simp [appendAugmentationCrossingMemory, writtenAt, aMemory, ports,
      orientAugmentationWitness, Prod.swap, firstPort, secondPort]
  refine ⟨_, reads.append writes, ready, count.trans ?_, out, ?_, bRR.trans mRR, bRM.trans mRM⟩
  · exact congrArg (· + 1) (fixed 87 (by decide))
  · intro r away
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at away
    obtain ⟨a5, a15, a16, a17, a87⟩ := away
    exact (bFixed r a5 a87).trans (fixed r (by simp [a5, a15, a16, a17]))

end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentCrossingCell

/-! matching/MatchingAugmentCrossingLoop.lean -/
section RppSource_MatchingAugmentCrossingLoop
open private scanAugmentationTraceTail VehicleRoutingSurvey.Routing.scanAugmentationTraceTail from Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface
namespace VehicleRoutingSurvey.Routing



private theorem augmentationTraceIndex_zero (forward : Bool) (start : ℕ) :
    augmentationTraceIndex forward start 0 = start := by
  cases forward <;> simp [augmentationTraceIndex]

private theorem augmentationTraceIndex_succ (forward : Bool) (start i : ℕ) :
    augmentationTraceIndex forward (if forward then start + 2 else start - 2) i =
      augmentationTraceIndex forward start (i + 1) := by
  cases forward <;> simp [augmentationTraceIndex, Nat.sub_sub] <;> omega





private theorem appendAugmentationTraceWitness_length (forward : Bool) :
    (appendAugmentationTraceWitness forward).length = 13 := rfl



private def afterAugmentationTracePair (forward : Bool) (t : ArithmeticState) : ArithmeticState :=
  {t with
    pc := 0
    nr := Function.update (Function.update t.nr 4 (t.nr 4 - t.nr 18)) 7
      (if forward then t.nr 7 + t.nr 18 else t.nr 7 - t.nr 18)}

private theorem scanAugmentationTraceCycle {s t : ArithmeticState} (forward : Bool)
    (entry : s.pc = 0) (running : s.halted = false) (remaining : s.nr 6 < s.nr 4)
    (ran : BlockRuns (appendAugmentationTraceWitness forward) 13 s t) (ready : t.halted = false) :
    (arithmeticStep (scanAugmentationTraceBlock forward))^[17] s = afterAugmentationTracePair forward t := by
  let code := scanAugmentationTraceBlock forward
  have start : arithmeticStep code s = relocateState 1 s := by
    simp [code, scanAugmentationTraceBlock, arithmeticStep, entry, running, not_le.mpr remaining,
      relocateState]
  have body : (arithmeticStep code)^[13] (relocateState 1 s) = relocateState 1 t := by
    have ranRelocated := arithmeticIterate_relocate [.natBranch 4 6 17 1]
      (appendAugmentationTraceWitness forward) (scanAugmentationTraceTail forward) s 13 ran.inside
    simpa [code, scanAugmentationTraceBlock, ran.run] using ranRelocated
  have pc : t.pc = 13 := ran.exit.trans (appendAugmentationTraceWitness_length forward)
  have tail : (arithmeticStep code)^[3] (relocateState 1 t) = afterAugmentationTracePair forward t := by
    cases forward <;> simp [code, scanAugmentationTraceBlock, scanAugmentationTraceTail,
      appendAugmentationTraceWitness, readAugmentationTraceWitness, appendAugmentationCrossingPair,
      appendBlock, relocateState, arithmeticStep, pc, ready, Function.iterate_succ_apply',
      afterAugmentationTracePair]
  change (arithmeticStep code)^[3 + (13 + 1)] s = _
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one, start, body, tail]

/-- Follow a preselected sequence of alternating path children. Every read
remains below the output buffer. The loop writes one pair per selected child
and stops after exactly `17 * children.length + 1` instructions. -/
theorem scanAugmentationTraceBlock_correct {k : ℕ} (forward : Bool) (children : List (Fin k))
    (witness : Fin k → Fin k × Fin k) {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1) (two : s.nr 18 = 2)
    (remaining : s.nr 4 = 2 * children.length + 1)
    (selected : ∀ i, ∀ within : i < children.length,
      s.nm (s.nr 3 + augmentationTraceIndex forward (s.nr 7) i) = children[i].val)
    (selectedBelow : ∀ i < children.length, s.nr 3 + augmentationTraceIndex forward (s.nr 7) i < s.nr 86)
    (encoded : ∀ v ∈ children,
      matchingForestWitnessAt s.nm (s.nr 90) v.val = ((witness v).1.val, (witness v).2.val))
    (witnessBelow : s.nr 90 + 2 * k ≤ s.nr 86) :
    ∃ t, BlockRuns (scanAugmentationTraceBlock forward) (17 * children.length + 1) s t ∧
      t.halted = false ∧ t.nr 87 = s.nr 87 + children.length ∧
      AugmentationCrossingArray t.nm (augmentationCrossingCursor s)
        (children.map fun v => orientAugmentationWitness forward (witness v)) ∧
      (∀ address, address < augmentationCrossingCursor s ∨
        augmentationCrossingCursor s + 2 * children.length ≤ address → t.nm address = s.nm address) ∧
      (∀ r, r ∉ [4, 5, 7, 15, 16, 17, 87] → t.nr r = s.nr r) ∧ t.rr = s.rr ∧ t.rm = s.rm := by
  induction children generalizing s with
  | nil =>
    let t := {s with pc := 17}
    have stop : s.nr 4 ≤ s.nr 6 := by simp [remaining, one]
    have ran : BlockRuns (scanAugmentationTraceBlock forward) 1 s t := by
      apply BlockRuns.of_running_exit
      · simp [t, scanAugmentationTraceBlock, arithmeticStep, entry, running, stop]
      · exact running
      · rfl
    refine ⟨t, ran, running, by simp [t], ?_, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
    intro _ impossible
    simp at impossible
  | cons child rest ih =>
    let ports := orientAugmentationWitness forward (witness child)
    have headRead : s.nm (s.nr 3 + s.nr 7) = child.val := by
      have stored := selected 0 (by simp)
      rw [augmentationTraceIndex_zero] at stored
      exact stored
    obtain ⟨t, cell, ready, count, memory, fixed, rRegs, rMem⟩ :=
      appendAugmentationTraceWitness_correct forward entry running one headRead (encoded child (by simp))
    let u := afterAugmentationTracePair forward t
    have progressed : (arithmeticStep (scanAugmentationTraceBlock forward))^[17] s = u :=
      scanAugmentationTraceCycle forward entry running (by simp only [List.length_cons] at remaining; omega) cell ready
    have keeps (r : ℕ) (away : r ∉ [4, 5, 7, 15, 16, 17, 87]) : u.nr r = s.nr r := by
      have n4 : r ≠ 4 := by intro same; exact away (by simp [same])
      have n7 : r ≠ 7 := by intro same; exact away (by simp [same])
      have old : r ∉ [5, 15, 16, 17, 87] := by
        intro inOld
        apply away
        simp only [List.mem_cons, List.not_mem_nil, or_false] at inOld ⊢
        tauto
      simpa only [u, afterAugmentationTracePair, Function.update_of_ne n4, Function.update_of_ne n7] using fixed r old
    have atOne : u.nr 6 = 1 := (keeps 6 (by decide)).trans one
    have atTwo : u.nr 18 = 2 := (keeps 18 (by decide)).trans two
    have remainingNext : u.nr 4 = 2 * rest.length + 1 := by
      simp only [u, afterAugmentationTracePair, Function.update_of_ne (by decide : (4 : ℕ) ≠ 7),
        Function.update_self, fixed 4 (by decide), fixed 18 (by decide), two, remaining, List.length_cons]
      omega
    have nextIndex : u.nr 7 = if forward then s.nr 7 + 2 else s.nr 7 - 2 := by
      simp [u, afterAugmentationTracePair, fixed 7 (by decide), fixed 18 (by decide), two]
    have nextCount : u.nr 87 = s.nr 87 + 1 := by
      simpa [u, afterAugmentationTracePair] using count
    have cursor : augmentationCrossingCursor u = augmentationCrossingCursor s + 2 := by
      simp only [augmentationCrossingCursor, keeps 86 (by decide), nextCount]
      omega
    have changed : u.nm = appendAugmentationCrossingMemory s ports.1.val ports.2.val := memory
    have below (address : ℕ) (prior : address < s.nr 86) : u.nm address = s.nm address := by
      rw [changed]
      apply appendAugmentationCrossingMemory_outside
      exact .inl (by unfold augmentationCrossingCursor; omega)
    have indexShift (i : ℕ) : u.nr 3 + augmentationTraceIndex forward (u.nr 7) i =
        s.nr 3 + augmentationTraceIndex forward (s.nr 7) (i + 1) := by
      rw [keeps 3 (by decide), nextIndex, augmentationTraceIndex_succ]
    have nextSelected (i : ℕ) (within : i < rest.length) :
        u.nm (u.nr 3 + augmentationTraceIndex forward (u.nr 7) i) = rest[i].val := by
      have later : i + 1 < (child :: rest).length := by simpa using within
      rw [indexShift, below _ (selectedBelow _ later)]
      exact selected _ later
    have nextSelectedBelow (i : ℕ) (within : i < rest.length) :
        u.nr 3 + augmentationTraceIndex forward (u.nr 7) i < u.nr 86 := by
      rw [indexShift, keeps 86 (by decide)]
      exact selectedBelow _ (by simpa using within)
    have nextWitness (v : Fin k) (selected : v ∈ rest) : matchingForestWitnessAt u.nm (u.nr 90) v.val =
        ((witness v).1.val, (witness v).2.val) := by
      have finite := v.isLt
      rw [keeps 90 (by decide)]
      let address := s.nr 90 + (v.val + v.val)
      change (u.nm address, u.nm (address + 1)) = _
      rw [below address (by dsimp [address]; omega),
        below (address + 1) (by dsimp [address]; omega)]
      exact encoded v (List.mem_cons_of_mem _ selected)
    obtain ⟨f, tailRun, live, finalCount, array, footprint, regs, reals, rMemory⟩ :=
      ih (s := u) rfl ready atOne atTwo remainingNext nextSelected nextSelectedBelow nextWitness
        (by rwa [keeps 90 (by decide), keeps 86 (by decide)])
    have all : BlockRuns (scanAugmentationTraceBlock forward) (17 * (child :: rest).length + 1) s f := by
      apply BlockRuns.of_running_exit
      · rw [show 17 * (child :: rest).length + 1 = (17 * rest.length + 1) + 17 by
          simp only [List.length_cons, Nat.mul_add, Nat.mul_one] <;> omega]
        rw [Function.iterate_add_apply, progressed]
        exact tailRun.run
      · exact live
      · exact tailRun.exit
    refine ⟨f, all, live, by rw [finalCount, nextCount, List.length_cons]; omega,
      ?_, ?_, fun r away => (regs r away).trans (keeps r away), reals.trans rRegs, rMemory.trans rMem⟩
    · intro i inside
      cases i with
      | zero =>
        have first := (footprint (augmentationCrossingCursor s) (.inl (by omega))).trans
          ((congrFun changed _).trans (appendAugmentationCrossingMemory_first _ _ _))
        have second := (footprint (augmentationCrossingCursor s + 1) (.inl (by omega))).trans
          ((congrFun changed _).trans (appendAugmentationCrossingMemory_second _ _ _))
        exact ⟨first, second⟩
      | succ i =>
        have inTail : i < (rest.map fun v => orientAugmentationWitness forward (witness v)).length := by
          simpa using inside
        have addr : augmentationCrossingCursor s + ((i + 1) + (i + 1)) =
            augmentationCrossingCursor u + (i + i) := by omega
        simpa only [List.map_cons, List.getElem_cons_succ, addr] using array i inTail
    · intro address outside
      have tailOutside : address < augmentationCrossingCursor u ∨
          augmentationCrossingCursor u + 2 * rest.length ≤ address := by
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at outside
        omega
      have firstOutside : address < augmentationCrossingCursor s ∨
          augmentationCrossingCursor s + 2 ≤ address := by
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at outside
        omega
      exact (footprint address tailOutside).trans ((congrFun changed address).trans
        (appendAugmentationCrossingMemory_outside _ _ _ _ firstOutside))

end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentCrossingLoop

/-! matching/TightPathAugmentation.lean -/
section RppSource_TightPathAugmentation
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

private theorem perfectMatching_remove_submatching {n : ℕ} {O U : Finset (Fin n)}
    {M A : Finset (Sym2 (Fin n))} (perfect : IsPerfectMatchingOn O M)
    (submatching : IsPerfectMatchingOn U A) (included : A ⊆ M) :
    IsPerfectMatchingOn (O \ U) (M \ A) := by
  constructor
  · intro e he
    obtain ⟨inM, outside⟩ := Finset.mem_sdiff.mp he
    refine ⟨(perfect.1 e inM).1, fun v hv => ?_⟩
    have inO := (perfect.1 e inM).2 v hv
    refine Finset.mem_sdiff.mpr ⟨inO, fun inside => ?_⟩
    obtain ⟨f, covers, _⟩ := submatching.2 v inside
    have equal := (perfect.2 v inO).unique ⟨inM, hv⟩ ⟨included covers.1, covers.2⟩
    exact outside (equal.symm ▸ covers.1)
  · intro v hv
    obtain ⟨inO, outside⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨e, covers, unique⟩ := perfect.2 v inO
    have notIn : e ∉ A := fun he => outside ((submatching.1 e he).2 v covers.2)
    exact ⟨e, ⟨Finset.mem_sdiff.mpr ⟨covers.1, notIn⟩, covers.2⟩, fun f hf =>
      unique f ⟨(Finset.mem_sdiff.mp hf.1).1, hf.2⟩⟩

private theorem perfectMatching_union_unique_left {n : ℕ} {U V : Finset (Fin n)}
    {M N : Finset (Sym2 (Fin n))} (left : IsPerfectMatchingOn U M)
    (right : IsPerfectMatchingOn V N) (disjoint : Disjoint U V) {v : Fin n} (hv : v ∈ U) :
    ∃! e, e ∈ M ∪ N ∧ v ∈ e := by
  obtain ⟨e, covers, unique⟩ := left.2 v hv
  refine ⟨e, ⟨Finset.mem_union_left _ covers.1, covers.2⟩, fun f hf => ?_⟩
  obtain ⟨edges, incident⟩ := hf
  rcases Finset.mem_union.mp edges with inM | inN
  · exact unique f ⟨inM, incident⟩
  · exact (Finset.disjoint_left.mp disjoint hv ((right.1 f inN).2 v incident)).elim

theorem perfectMatching_union_disjoint {n : ℕ} {U V : Finset (Fin n)}
    {M N : Finset (Sym2 (Fin n))} (left : IsPerfectMatchingOn U M)
    (right : IsPerfectMatchingOn V N) (disjoint : Disjoint U V) :
    IsPerfectMatchingOn (U ∪ V) (M ∪ N) := by
  constructor
  · intro e he
    rcases Finset.mem_union.mp he with inM | inN
    · exact ⟨(left.1 e inM).1, fun v hv => Finset.mem_union_left _ ((left.1 e inM).2 v hv)⟩
    · exact ⟨(right.1 e inN).1, fun v hv => Finset.mem_union_right _ ((right.1 e inN).2 v hv)⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with inU | inV
    · exact perfectMatching_union_unique_left left right disjoint inU
    · rw [Finset.union_comm]
      exact perfectMatching_union_unique_left right left disjoint.symm inV

/-- Flip an alternating path from one exposed vertex to another. Its interior is paired
by the old matching. After the flip, the full path is paired from its first vertex onward. -/
def augmentMatchingAlong {n : ℕ} (M : Finset (Sym2 (Fin n))) (start finish : Fin n)
    (interior : List (Fin n)) : Finset (Sym2 (Fin n)) :=
  (M \ (alternatingEdges interior).toFinset) ∪
    (alternatingEdges (start :: (interior ++ [finish]))).toFinset

theorem augmentMatchingAlong_spec {n : ℕ} {covered : Finset (Fin n)}
    {M : Finset (Sym2 (Fin n))} (matched : IsPerfectMatchingOn covered M)
    {start finish : Fin n} {interior : List (Fin n)}
    (startFree : start ∉ covered) (finishFree : finish ∉ covered)
    (distinct : (start :: (interior ++ [finish])).Nodup) (even : interior.length % 2 = 0)
    (oldEdges : (alternatingEdges interior).toFinset ⊆ M)
    (tight : Sym2 (Fin n) → Prop) (oldTight : ∀ e ∈ M, tight e)
    (pathTight : ∀ e ∈ (alternatingEdges (start :: (interior ++ [finish]))).toFinset, tight e) :
    let result := augmentMatchingAlong M start finish interior
    IsPerfectMatchingOn (insert start (insert finish covered)) result ∧
      result.card = M.card + 1 ∧ ∀ e ∈ result, tight e := by
  let path := start :: (interior ++ [finish])
  let old := (alternatingEdges interior).toFinset
  let added := (alternatingEdges path).toFinset
  let result := augmentMatchingAlong M start finish interior
  have interiorDistinct : interior.Nodup :=
    List.Nodup.sublist (List.sublist_append_left interior [finish]) distinct.of_cons
  have pathEven : path.length % 2 = 0 := by
    simp only [path, List.length_cons, List.length_append, List.length_nil]
    omega
  have oldPerfect : IsPerfectMatchingOn interior.toFinset old :=
    (alternatingEdges_perfect interior interiorDistinct even).2
  have newPerfect : IsPerfectMatchingOn path.toFinset added :=
    (alternatingEdges_perfect path distinct pathEven).2
  have disjoint : Disjoint (covered \ interior.toFinset) path.toFinset := by
    apply Finset.disjoint_left.mpr
    intro v rest used
    obtain ⟨inCovered, notInside⟩ := Finset.mem_sdiff.mp rest
    simp only [path, List.mem_toFinset, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at used
    rcases used with first | inside | last
    · exact startFree (first ▸ inCovered)
    · exact notInside (List.mem_toFinset.mpr inside)
    · exact finishFree (last ▸ inCovered)
  have insideCovered : interior.toFinset ⊆ covered := by
    intro v hv
    obtain ⟨e, covers, _⟩ := oldPerfect.2 v hv
    exact (matched.1 e (oldEdges covers.1)).2 v covers.2
  have support : (covered \ interior.toFinset) ∪ path.toFinset = insert start (insert finish covered) := by
    ext v
    have implication : v ∈ interior → v ∈ covered := fun h => insideCovered (List.mem_toFinset.mpr h)
    simp only [path, Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset, List.mem_cons,
      List.mem_append, List.not_mem_nil, or_false, Finset.mem_insert]
    tauto
  have perfect : IsPerfectMatchingOn (insert start (insert finish covered)) result :=
    support ▸ perfectMatching_union_disjoint (perfectMatching_remove_submatching matched oldPerfect oldEdges)
      newPerfect disjoint
  change IsPerfectMatchingOn (insert start (insert finish covered)) result ∧
    result.card = M.card + 1 ∧ ∀ e ∈ result, tight e
  refine ⟨perfect, ?_, ?_⟩
  · have different : start ≠ finish := by
      intro same
      exact (List.nodup_cons.mp distinct).1 (List.mem_append_right interior (by simp [same]))
    have startAbsent : start ∉ insert finish covered := by simp [different, startFree]
    have card := perfectMatching_card_twice perfect
    rw [Finset.card_insert_of_notMem startAbsent, Finset.card_insert_of_notMem finishFree,
      perfectMatching_card_twice matched] at card
    omega
  · intro e he
    change e ∈ (M \ old) ∪ added at he
    rcases Finset.mem_union.mp he with previous | inserted
    · exact oldTight e (Finset.mem_sdiff.mp previous).1
    · exact pathTight e inserted

end VehicleRoutingSurvey.Routing
end RppSource_TightPathAugmentation

/-! matching/AlternatingForestAugment.lean -/
section RppSource_AlternatingForestAugment
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

private theorem outer_parent_is_mate {α : Type*} {state : AlternatingForestState α}
    {mate : α → Option α} {tight : α → α → Prop} (valid : state.valid mate tight)
    {v p : α} {previous : Option α} (outer : state.role v = .outer previous)
    (link : (state.role v).parent = some p) : (∃ next, state.role p = .inner next) ∧ mate v = some p := by
  cases previous with
  | none => simp [outer, AlternatingForestRole.parent] at link
  | some q =>
    have same : q = p := Option.some.inj (by simpa only [outer, AlternatingForestRole.parent] using link)
    subst q
    have step := valid v
    rw [outer] at step
    exact ⟨step.1, step.2.1⟩

theorem trace_pairs_in_matching {n : ℕ} {state : AlternatingForestState (Fin n)}
    {mate : Fin n → Option (Fin n)} {tight : Fin n → Fin n → Prop} (valid : state.valid mate tight)
    {M : Finset (Sym2 (Fin n))} (mateIn : ∀ u v, mate u = some v → s(u, v) ∈ M)
    (trace : List (Fin n)) (starts : ∀ v ∈ trace.head?, ∃ q, state.role v = .outer q)
    (chain : trace.IsChain (fun child p => (state.role child).parent = some p)) :
    ∀ e ∈ alternatingEdges trace, e ∈ M := by
  induction trace using List.twoStepInduction with
  | nil => simp [alternatingEdges]
  | singleton v => simp [alternatingEdges]
  | cons_cons a b rest ih _ =>
    obtain ⟨previous, aOuter⟩ := starts a (by simp)
    have old := List.isChain_cons_cons.mp chain
    obtain ⟨⟨next, bInner⟩, aMate⟩ := outer_parent_is_mate valid aOuter old.1
    have newStart : ∀ v ∈ rest.head?, ∃ q, state.role v = .outer q := by
      cases rest with
      | nil => simp
      | cons c xs =>
        intro v hv
        have same : c = v := by simpa only [List.head?_cons, Option.mem_some_iff] using hv
        subst v
        have link := (List.isChain_cons_cons.mp old.2).1
        rcases parent_step_roles valid link with ⟨_, impossible, _, _⟩ | ⟨q, _, cOuter⟩
        · have conflict := bInner.symm.trans impossible
          cases conflict
        · exact ⟨q, cOuter⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | remaining
    · exact mateIn a b aMate
    · exact ih newStart old.2.tail e remaining

private theorem trace_prefix_even {α : Type*} {state : AlternatingForestState α}
    {mate : α → Option α} {tight : α → α → Prop} (valid : state.valid mate tight)
    {trace before : List α} {first last : α} {root : Option α}
    (shape : trace = before ++ [last]) (head : trace.head? = some first)
    (firstOuter : state.role first = .outer root) (lastOuter : state.role last = .outer none)
    (chain : trace.IsChain (fun child p => (state.role child).parent = some p)) : before.length % 2 = 0 := by
  have original : (before ++ [last]).IsChain (fun child p => (state.role child).parent = some p) :=
    shape ▸ chain
  have labelled : (before ++ [last]).IsChain (fun u v => (state.role u).outerTag ≠ (state.role v).outerTag) :=
    original.imp fun _ _ link => parent_step_alternates valid link
  apply (alternating_chain_parity (fun v => (state.role v).outerTag) last before labelled).mpr
  rw [← shape, head]
  simp [firstOuter, lastOuter, AlternatingForestRole.outerTag]

/-- Flip the augmenting path obtained by joining the two exposed roots through the triggering
edge. Parent traces are ordered from each endpoint back to its root. -/
def augmentFromOuterForests {n : ℕ} (state : AlternatingForestState (Fin n))
    (M : Finset (Sym2 (Fin n))) (a b : Fin n) : Finset (Sym2 (Fin n)) :=
  let left := state.traceToRoot a
  let right := state.traceToRoot b
  match left.getLast?, right.getLast? with
  | some start, some finish => augmentMatchingAlong M start finish (left.reverse.tail ++ right.dropLast)
  | _, _ => M

theorem augmentFromOuterForests_roots {n : ℕ} {state : AlternatingForestState (Fin n)} {mate : Fin n → Option (Fin n)}
    {M : Finset (Sym2 (Fin n))} {covered : Finset (Fin n)} {tight : Sym2 (Fin n) → Prop}
    (matched : IsPerfectMatchingOn covered M) (valid : state.valid mate (fun a b => tight s(a, b)))
    (mateIn : ∀ u v, mate u = some v → s(u, v) ∈ M) (exposed : ∀ v, mate v = none → v ∉ covered)
    (oldTight : ∀ e ∈ M, tight e) {a b : Fin n} {aParent bParent : Option (Fin n)}
    (aOuter : state.role a = .outer aParent) (bOuter : state.role b = .outer bParent)
    (separate : state.commonAncestor a b = none) (trigger : tight s(a, b)) :
    let result := augmentFromOuterForests state M a b
    ∃ start finish, (state.traceToRoot a).getLast? = some start ∧ (state.traceToRoot b).getLast? = some finish ∧
      state.role start = .outer none ∧ state.role finish = .outer none ∧
      start ∉ covered ∧ finish ∉ covered ∧ start ≠ finish ∧
      IsPerfectMatchingOn (insert start (insert finish covered)) result ∧ result.card = M.card + 1 ∧
      ∀ e ∈ result, tight e := by
  obtain ⟨aHead, aDistinct, _, aPath, start, startLast, startOuter, startFree⟩ :=
    AlternatingForestState.traceToRoot_spec valid (x := a) (by simp [aOuter])
  obtain ⟨bHead, bDistinct, _, bPath, finish, finishLast, finishOuter, finishFree⟩ :=
    AlternatingForestState.traceToRoot_spec valid (x := b) (by simp [bOuter])
  obtain ⟨aBefore, aForm⟩ := List.getLast?_eq_some_iff.mp startLast
  obtain ⟨bBefore, bForm⟩ := List.getLast?_eq_some_iff.mp finishLast
  have allSeparate := firstSharedAncestor_eq_none_iff.mp separate
  have rootDiff : start ≠ finish := by
    intro same
    exact allSeparate finish (List.mem_of_getLast? finishLast) (same ▸ List.mem_of_getLast? startLast)
  have aChain := aPath.imp (fun _ _ link => link.1)
  have bChain := bPath.imp (fun _ _ link => link.1)
  have aEven := trace_prefix_even valid aForm aHead aOuter startOuter aChain
  have bEven := trace_prefix_even valid bForm bHead bOuter finishOuter bChain
  have aRevEven : aBefore.reverse.length % 2 = 0 := by simpa only [List.length_reverse] using aEven
  have aPairRest := trace_pairs_in_matching valid mateIn (state.traceToRoot a)
    (fun x hx => ⟨aParent, (show a = x from by simpa only [aHead, Option.mem_some_iff] using hx) ▸ aOuter⟩) aChain
  have bPairRest := trace_pairs_in_matching valid mateIn (state.traceToRoot b)
    (fun x hx => ⟨bParent, (show b = x from by simpa only [bHead, Option.mem_some_iff] using hx) ▸ bOuter⟩) bChain
  have aReverse : (state.traceToRoot a).reverse = start :: aBefore.reverse := by simp [aForm]
  have removeFinish : (state.traceToRoot b).dropLast = bBefore := by simp [bForm]
  let interior := aBefore.reverse ++ bBefore
  have shape : start :: (interior ++ [finish]) = (state.traceToRoot a).reverse ++ state.traceToRoot b := by
    simp [interior, aReverse, bForm, List.append_assoc]
  have joinedDistinct : (start :: (interior ++ [finish])).Nodup := by
    rw [shape]
    refine List.nodup_append.mpr ⟨List.nodup_reverse.mpr aDistinct, bDistinct, ?_⟩
    intro x hx y hy same
    exact allSeparate y hy (same ▸ List.mem_reverse.mp hx)
  have joinedTight : (start :: (interior ++ [finish])).IsChain (fun u v => tight s(u, v)) := by
    rw [shape]
    refine (List.isChain_reverse.mpr (aPath.imp fun _ _ h => h.2)).append
      (bPath.imp fun _ _ h => Sym2.eq_swap ▸ h.2) ?_
    intro u hu v hv
    have uEq : a = u := by simpa only [List.getLast?_reverse, aHead, Option.mem_some_iff] using hu
    have vEq : b = v := by simpa only [bHead, Option.mem_some_iff] using hv
    exact vEq ▸ uEq ▸ trigger
  have parity : interior.length % 2 = 0 := by
    simp only [interior, List.length_append]
    rw [Nat.add_mod, aRevEven, bEven]
  have oldPairs : (alternatingEdges interior).toFinset ⊆ M := by
    intro e he
    have member := List.mem_toFinset.mp he
    change e ∈ alternatingEdges (aBefore.reverse ++ bBefore) at member
    rw [alternatingEdges_append_even _ _ aRevEven] at member
    rcases List.mem_append.mp member with left | right
    · apply aPairRest e
      rw [aForm, alternatingEdges_append_even _ _ aEven]
      rw [alternatingEdges_reverse_even aBefore aEven] at left
      exact List.mem_append_left _ (List.mem_reverse.mp left)
    · apply bPairRest e
      rw [bForm, alternatingEdges_append_even _ _ bEven]
      exact List.mem_append_left _ right
  have flip := augmentMatchingAlong_spec matched (exposed start startFree) (exposed finish finishFree)
    joinedDistinct parity oldPairs tight oldTight
    (fun e he => alternatingEdges_tight tight _ joinedTight e (List.mem_toFinset.mp he))
  refine ⟨start, finish, startLast, finishLast, startOuter, finishOuter, exposed start startFree,
    exposed finish finishFree, rootDiff, ?_⟩
  simpa only [augmentFromOuterForests, startLast, finishLast, aReverse, List.tail_cons, removeFinish, interior] using flip



end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestAugment

/-! matching/MatchingAugmentTraceModel.lean -/
section RppSource_MatchingAugmentTraceModel
namespace VehicleRoutingSurvey.Routing

theorem AlternatingForestState.outerTrace_length_odd {k : ℕ} {forest : AlternatingForestState (Fin k)}
    {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop}
    (valid : forest.valid mate tight) {v : Fin k} {parent : Option (Fin k)}
    (outer : forest.role v = .outer parent) : (forest.traceToRoot v).length % 2 = 1 := by
  obtain ⟨head, _, _, chain, root, ends, rootOuter, _⟩ :=
    AlternatingForestState.traceToRoot_spec valid (x := v) (by simp [outer])
  obtain ⟨before, shape⟩ := List.getLast?_eq_some_iff.mp ends
  have labelled : (before ++ [root]).IsChain (fun a b => (forest.role a).outerTag ≠ (forest.role b).outerTag) :=
    shape ▸ chain.imp (fun _ _ step => parent_step_alternates valid step.1)
  have parity : before.length % 2 = 0 := by
    apply (alternating_chain_parity (fun w => (forest.role w).outerTag) root before labelled).mpr
    rw [← shape, head]
    simp [outer, rootOuter, AlternatingForestRole.outerTag]
  rw [shape, List.length_append]
  simp only [List.length_singleton]
  omega

theorem AlternatingForestState.disjointOuterTraces_length_le {k : ℕ}
    {forest : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)}
    {tight : Fin k → Fin k → Prop} (valid : forest.valid mate tight) {u v : Fin k}
    (uMarked : forest.role u ≠ .unlabelled) (vMarked : forest.role v ≠ .unlabelled)
    (separate : forest.commonAncestor u v = none) :
    (forest.traceToRoot u).length + (forest.traceToRoot v).length ≤ k := by
  obtain ⟨_, leftDistinct, _, _, _⟩ := AlternatingForestState.traceToRoot_spec valid uMarked
  obtain ⟨_, rightDistinct, _, _, _⟩ := AlternatingForestState.traceToRoot_spec valid vMarked
  have apart := firstSharedAncestor_eq_none_iff.mp separate
  have allDistinct : (forest.traceToRoot u ++ forest.traceToRoot v).Nodup := by
    refine List.nodup_append.mpr ⟨leftDistinct, rightDistinct, ?_⟩
    intro x onLeft y onRight equal
    exact apart y onRight (equal ▸ onLeft)
  simpa using allDistinct.length_le_card





theorem augmentationWitnessIndex_parent_inBounds (forward : Bool) {length i : ℕ}
    (odd : length % 2 = 1) (inside : i < length / 2) :
    augmentationTraceIndex forward (augmentationWitnessStart forward length) i + 1 < length := by
  cases forward <;> simp [augmentationWitnessStart, augmentationTraceIndex] <;> omega



@[simp] theorem augmentationWitnessChildren_length {k : ℕ} (forward : Bool) (trail : List (Fin k)) :
    (augmentationWitnessChildren forward trail).length = trail.length / 2 := by
  simp [augmentationWitnessChildren]

theorem augmentationWitnessChildren_get {k : ℕ} (forward : Bool) (trail : List (Fin k))
    (i : ℕ) (inside : i < (augmentationWitnessChildren forward trail).length) :
    (augmentationWitnessChildren forward trail)[i] =
      trail[augmentationTraceIndex forward (augmentationWitnessStart forward trail.length) i]'(
        augmentationWitnessIndex_inBounds forward (by simpa using inside)) := by
  simp [augmentationWitnessChildren]



theorem forestAugmentationCrossings_count {k : ℕ} (witness : Fin k → Fin k × Fin k)
    (trigger : Fin k × Fin k) (left right : List (Fin k))
    (lOdd : left.length % 2 = 1) (rOdd : right.length % 2 = 1) :
    2 * (forestAugmentationCrossings witness trigger left right).length = left.length + right.length := by
  simp [forestAugmentationCrossings]
  omega

/-- Every recorded witness connects precisely the two consecutive trace
representatives at its selected parent edge. -/
theorem augmentationWitness_matches_parent {k : ℕ} {forest : AlternatingForestState (Fin k)}
    (forward : Bool) (trail : List (Fin k)) (odd : trail.length % 2 = 1)
    (chain : trail.IsChain fun a b => (forest.role a).parent = some b)
    (witness : Fin k → Fin k × Fin k) (rep : Fin k → Fin k)
    (sound : ∀ (child parent : Fin k), (forest.role child).parent = some parent →
      (rep (witness child).1, rep (witness child).2) = (parent, child))
    (i : ℕ) (inside : i < (augmentationWitnessChildren forward trail).length) :
    let slot := augmentationTraceIndex forward (augmentationWitnessStart forward trail.length) i
    let child := (augmentationWitnessChildren forward trail)[i]
    let parent := trail[slot + 1]'(augmentationWitnessIndex_parent_inBounds forward odd (by simpa using inside))
    let ports := orientAugmentationWitness forward (witness child)
    (rep ports.1, rep ports.2) = orientAugmentationWitness forward (parent, child) := by
  intro slot child parent ports
  have bounded : slot + 1 < trail.length :=
    augmentationWitnessIndex_parent_inBounds forward odd (by simpa using inside)
  have joined : (forest.role child).parent = some parent := by
    have childAt := augmentationWitnessChildren_get forward trail i inside
    have parentAt := List.isChain_iff_getElem.mp chain slot bounded
    change (forest.role ((augmentationWitnessChildren forward trail)[i])).parent = some parent
    rw [childAt]
    exact parentAt
  have mapped := sound child parent joined
  cases forward
  · simpa [ports, orientAugmentationWitness] using mapped
  · simpa [ports, orientAugmentationWitness, Prod.swap] using congrArg Prod.swap mapped

end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentTraceModel

/-! matching/MatchingAugmentTraceLeg.lean -/
section RppSource_MatchingAugmentTraceLeg
namespace VehicleRoutingSurvey.Routing



private structure AugmentationTraceLegReady (forward : Bool) (s t : ArithmeticState) : Prop where
  base : t.nr 3 = s.nr (if forward then 84 else 83)
  length : t.nr 4 = s.nr (if forward then 11 else 10)
  index : t.nr 7 = augmentationWitnessStart forward (t.nr 4)
  one : t.nr 6 = 1
  two : t.nr 18 = 2
  natural : t.nm = s.nm
  realRegisters : t.rr = s.rr
  realMemory : t.rm = s.rm
  fixed : ∀ r, r ∉ [3, 4, 6, 7, 18, 19] → t.nr r = s.nr r

private theorem prepareAugmentationTraceLeg_correct (forward : Bool) {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns (prepareAugmentationTraceLeg forward) 6 s t ∧ t.halted = false ∧
      AugmentationTraceLegReady forward s t := by
  let t := (arithmeticStep (prepareAugmentationTraceLeg forward))^[6] s
  have ready : t.halted = false := by
    cases forward <;> simp [t, prepareAugmentationTraceLeg, arithmeticStep, Function.iterate_succ_apply', entry, running]
  have exit : t.pc = (prepareAugmentationTraceLeg forward).length := by
    cases forward <;> simp [t, prepareAugmentationTraceLeg, arithmeticStep, Function.iterate_succ_apply', entry, running]
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_⟩
  constructor
  case fixed =>
    intro r away
    apply arithmeticRun_keeps_register _ s 6
    cases forward <;> simp [prepareAugmentationTraceLeg, naturalDestination] at away ⊢ <;> omega
  all_goals
    cases forward <;>
      simp [t, prepareAugmentationTraceLeg, augmentationWitnessStart, arithmeticStep,
        Function.iterate_succ_apply', entry, running]



theorem writeAugmentationTraceLeg_correct {k : ℕ} (forward : Bool) (trace : List (Fin k))
    (witness : Fin k → Fin k × Fin k) {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (odd : trace.length % 2 = 1)
    (length : s.nr (if forward then 11 else 10) = trace.length)
    (array : ForestTraceArray s.nm (s.nr (if forward then 84 else 83)) trace)
    (traceBelow : s.nr (if forward then 84 else 83) + trace.length ≤ s.nr 86)
    (witnesses : ∀ v ∈ augmentationWitnessChildren forward trace,
      matchingForestWitnessAt s.nm (s.nr 90) v.val = ((witness v).1.val, (witness v).2.val))
    (witnessBelow : s.nr 90 + 2 * k ≤ s.nr 86) :
    let rows := (augmentationWitnessChildren forward trace).map
      fun v => orientAugmentationWitness forward (witness v)
    ∃ t, BlockRuns (writeAugmentationTraceLeg forward) (6 + (17 * rows.length + 1)) s t ∧
      t.halted = false ∧ t.nr 87 = s.nr 87 + rows.length ∧ t.nr 6 = 1 ∧
      AugmentationCrossingArray t.nm (augmentationCrossingCursor s) rows ∧
      (∀ address, address < augmentationCrossingCursor s ∨ augmentationCrossingCursor s + 2 * rows.length ≤ address →
        t.nm address = s.nm address) ∧
      (∀ r, r ∉ [3, 4, 5, 6, 7, 15, 16, 17, 18, 19, 87] → t.nr r = s.nr r) ∧
      t.rr = s.rr ∧ t.rm = s.rm := by
  intro rows
  let children := augmentationWitnessChildren forward trace
  obtain ⟨a, config, live, args⟩ := prepareAugmentationTraceLeg_correct forward entry running
  let before := {a with pc := 0}
  have aLength : a.nr 4 = trace.length := args.length.trans length
  have aStart : a.nr 7 = augmentationWitnessStart forward trace.length := by rw [args.index, aLength]
  have childCount : children.length = trace.length / 2 := augmentationWitnessChildren_length forward trace
  have remaining : before.nr 4 = 2 * children.length + 1 := by
    change a.nr 4 = _
    rw [aLength, childCount]
    omega
  have kids (i : ℕ) (hi : i < children.length) :
      before.nm (before.nr 3 + augmentationTraceIndex forward (before.nr 7) i) = children[i].val := by
    change a.nm (a.nr 3 + augmentationTraceIndex forward (a.nr 7) i) = children[i].val
    rw [args.natural, args.base, aStart]
    have idx := augmentationWitnessIndex_inBounds forward (show i < trace.length / 2 from hi.trans_eq childCount)
    exact (array _ idx).trans (congrArg Fin.val (augmentationWitnessChildren_get forward trace i hi)).symm
  have kidsBelow (i : ℕ) (hi : i < children.length) :
      before.nr 3 + augmentationTraceIndex forward (before.nr 7) i < before.nr 86 := by
    change a.nr 3 + augmentationTraceIndex forward (a.nr 7) i < a.nr 86
    rw [args.base, aStart, args.fixed 86 (by decide)]
    have idx := augmentationWitnessIndex_inBounds forward (show i < trace.length / 2 from hi.trans_eq childCount)
    omega
  have aWitness (v : Fin k) (selected : v ∈ children) : matchingForestWitnessAt before.nm (before.nr 90) v.val =
      ((witness v).1.val, (witness v).2.val) := by
    change matchingForestWitnessAt a.nm (a.nr 90) v.val = _
    rw [args.natural, args.fixed 90 (by decide)]
    exact witnesses v selected
  have aSeparate : before.nr 90 + 2 * k ≤ before.nr 86 := by
    change a.nr 90 + 2 * k ≤ a.nr 86
    rwa [args.fixed 90 (by decide), args.fixed 86 (by decide)]
  obtain ⟨f, scanned, ready, count, written, footprint, fixed, rr, rm⟩ :=
    scanAugmentationTraceBlock_correct forward children witness (s := before) rfl live args.one args.two
      remaining kids kidsBelow aWitness aSeparate
  have outCursor : augmentationCrossingCursor before = augmentationCrossingCursor s := by
    change a.nr 86 + (a.nr 87 + a.nr 87) = _
    simp only [augmentationCrossingCursor, args.fixed 86 (by decide), args.fixed 87 (by decide)]
  have rowCount : rows.length = children.length := by simp [rows, children]
  have allSteps : BlockRuns (writeAugmentationTraceLeg forward) (6 + (17 * rows.length + 1)) s
      (relocateState (prepareAugmentationTraceLeg forward).length f) := by
    rw [rowCount]
    exact config.append scanned
  refine ⟨_, allSteps, ready, ?_, (fixed 6 (by decide)).trans args.one,
    ?_, ?_, ?_, rr.trans args.realRegisters, rm.trans args.realMemory⟩
  · change f.nr 87 = _
    rw [rowCount, count]
    exact congrArg (· + children.length) (args.fixed 87 (by decide))
  · change AugmentationCrossingArray f.nm _ rows
    simpa only [outCursor] using written
  · intro address outside
    exact (footprint address (by simpa only [outCursor, ← rowCount] using outside)).trans
      (congrFun args.natural address)
  · intro r away
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at away
    obtain ⟨n3, n4, n5, n6, n7, n15, n16, n17, n18, n19, n87⟩ := away
    exact (fixed r (by simp [n4, n5, n7, n15, n16, n17, n87])).trans
      (args.fixed r (by simp [n3, n4, n6, n7, n18, n19]))

end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentTraceLeg

/-! matching/MatchingAugmentCrossings.lean -/
section RppSource_MatchingAugmentCrossings
namespace VehicleRoutingSurvey.Routing

private theorem AugmentationCrossingArray.append {k : ℕ} {memory : ℕ → ℕ} {base : ℕ}
    {left right : List (Fin k × Fin k)} (l : AugmentationCrossingArray memory base left)
    (r : AugmentationCrossingArray memory (base + 2 * left.length) right) :
    AugmentationCrossingArray memory base (left ++ right) := by
  intro i within
  by_cases onLeft : i < left.length
  · simpa only [List.getElem_append_left onLeft] using l i onLeft
  · have onRight : i - left.length < right.length := by simp only [List.length_append] at within; omega
    have address : base + 2 * left.length + (i - left.length + (i - left.length)) = base + (i + i) := by omega
    simpa only [address, List.getElem_append_right (Nat.le_of_not_gt onLeft)] using r _ onRight





private theorem preservedAugmentationWitness {k : ℕ} {s t : ArithmeticState}
    (table : t.nr 90 = s.nr 90) (space : s.nr 90 + 2 * k ≤ s.nr 86)
    (below : ∀ address < s.nr 86, t.nm address = s.nm address) (v : Fin k) :
    matchingForestWitnessAt t.nm (t.nr 90) v.val = matchingForestWitnessAt s.nm (s.nr 90) v.val := by
  have bounded := v.isLt
  simp only [matchingForestWitnessAt, forestWitnessAddress, table]
  rw [below (s.nr 90 + (v.val + v.val)) (by omega), below (s.nr 90 + (v.val + v.val) + 1) (by omega)]

/-- From two distinct-root trace arrays and the saved original edge, write
the ordered list of new top-level crossing matches in one linear pass per leg. -/
theorem writeAugmentationCrossingsBlock_correct {k : ℕ} {s : ArithmeticState}
    (left right : List (Fin k)) (witness : Fin k → Fin k × Fin k) (trigger : Fin k × Fin k)
    (entry : s.pc = 0) (running : s.halted = false)
    (lOdd : left.length % 2 = 1) (rOdd : right.length % 2 = 1) (fits : left.length + right.length ≤ k)
    (lLength : s.nr 10 = left.length) (rLength : s.nr 11 = right.length)
    (lArray : ForestTraceArray s.nm (s.nr 83) left) (rArray : ForestTraceArray s.nm (s.nr 84) right)
    (lSpace : s.nr 83 + left.length ≤ s.nr 86) (rSpace : s.nr 84 + right.length ≤ s.nr 86)
    (records : ∀ v ∈ augmentationWitnessChildren false left ++ augmentationWitnessChildren true right,
      matchingForestWitnessAt s.nm (s.nr 90) v.val = ((witness v).1.val, (witness v).2.val))
    (wSpace : s.nr 90 + 2 * k ≤ s.nr 86) (triggerRegs : (s.nr 92, s.nr 93) = (trigger.1.val, trigger.2.val)) :
    let rows := forestAugmentationCrossings witness trigger left right
    ∃ (t : ArithmeticState) (steps : ℕ), BlockRuns writeAugmentationCrossingsBlock steps s t ∧
      t.halted = false ∧ steps ≤ 17 * k + 21 ∧ AugmentationCrossingsReady rows s t := by
  intro rows
  let lRows := (augmentationWitnessChildren false left).map witness
  let rRows := (augmentationWitnessChildren true right).map (fun v => (witness v).swap)
  have shape : rows = (lRows ++ [trigger]) ++ rRows := rfl
  let seed := {s with pc := 0, nr := Function.update s.nr 87 0}
  have seedReg (r : ℕ) (away : r ≠ 87) : seed.nr r = s.nr r := by simp [seed, Function.update_of_ne away]
  have seedZero : seed.nr 87 = 0 := by simp [seed]
  have seedCursor : augmentationCrossingCursor seed = s.nr 86 := by
    simp [augmentationCrossingCursor, seedReg 86 (by decide), seedZero]
  have seedWitness (v : Fin k) (inLeft : v ∈ augmentationWitnessChildren false left) :
      matchingForestWitnessAt seed.nm (seed.nr 90) v.val = ((witness v).1.val, (witness v).2.val) := by
    rw [seedReg 90 (by decide)]
    exact records v (List.mem_append_left _ inLeft)
  have seedArray : ForestTraceArray seed.nm (seed.nr 83) left := by
    change ForestTraceArray s.nm (seed.nr 83) left
    rw [seedReg 83 (by decide)]
    exact lArray
  have seedSpace : seed.nr 83 + left.length ≤ seed.nr 86 := by
    rwa [seedReg 83 (by decide), seedReg 86 (by decide)]
  obtain ⟨l, ranL, lReady, lCount, lOne, lPairs, lKeep, lFixed, lRR, lRM⟩ :=
    writeAugmentationTraceLeg_correct false left witness (s := seed) rfl running lOdd
      ((seedReg 10 (by decide)).trans lLength) seedArray seedSpace
      seedWitness (by simpa only [seedReg 90 (by decide), seedReg 86 (by decide)] using wSpace)
  have lExact : l.nr 87 = lRows.length := by simpa [seedZero, lRows, orientAugmentationWitness] using lCount
  have lBase : l.nr 86 = s.nr 86 := (lFixed 86 (by decide)).trans (seedReg 86 (by decide))
  let edgeEntry := {l with pc := 0}
  have edgeCursor : augmentationCrossingCursor edgeEntry = s.nr 86 + 2 * lRows.length := by
    change l.nr 86 + (l.nr 87 + l.nr 87) = _
    rw [lBase, lExact, Nat.two_mul]
  obtain ⟨m, join, mReady, mCount, mWritten, mFixed, mRR, mRM⟩ :=
    appendAugmentationCrossingPair_correct 92 93 (s := edgeEntry) rfl lReady lOne (by decide) (by decide)
  have firstPort : edgeEntry.nr 92 = trigger.1.val :=
    (lFixed 92 (by decide)).trans ((seedReg 92 (by decide)).trans (congrArg Prod.fst triggerRegs))
  have secondPort : edgeEntry.nr 93 = trigger.2.val :=
    (lFixed 93 (by decide)).trans ((seedReg 93 (by decide)).trans (congrArg Prod.snd triggerRegs))
  have mMemory : m.nm = appendAugmentationCrossingMemory edgeEntry trigger.1.val trigger.2.val := by
    rw [mWritten, firstPort, secondPort]
  have mKeeps (address : ℕ) (outside : address < s.nr 86 + 2 * lRows.length ∨
      s.nr 86 + 2 * lRows.length + 2 ≤ address) : m.nm address = l.nm address := by
    rw [mMemory]
    exact appendAugmentationCrossingMemory_outside _ _ _ _ (by rwa [edgeCursor])
  have mBase : m.nr 86 = s.nr 86 := (mFixed 86 (by decide) (by decide)).trans lBase
  have mReg (r : ℕ) (away : r ∉ [3, 4, 5, 6, 7, 15, 16, 17, 18, 19, 87]) : m.nr r = s.nr r := by
    have n5 : r ≠ 5 := by intro h; exact away (by simp [h])
    have n87 : r ≠ 87 := by intro h; exact away (by simp [h])
    exact (mFixed r n5 n87).trans ((lFixed r away).trans (seedReg r n87))
  have mBelow (address : ℕ) (within : address < s.nr 86) : m.nm address = s.nm address := by
    exact (mKeeps address (.inl (by omega))).trans (lKeep address (.inl (by rwa [seedCursor])))
  have enlargedLeft : AugmentationCrossingArray m.nm (s.nr 86) (lRows ++ [trigger]) := by
    apply AugmentationCrossingArray.append
    · intro i inside
      have stored : m.nm (s.nr 86 + (i + i)) = l.nm (s.nr 86 + (i + i)) :=
        mKeeps _ (.inl (by omega))
      have storedNext : m.nm (s.nr 86 + (i + i) + 1) = l.nm (s.nr 86 + (i + i) + 1) :=
        mKeeps _ (.inl (by omega))
      rw [stored, storedNext]
      have previous := lPairs i (show i < lRows.length from inside)
      simpa only [seedCursor, lRows, orientAugmentationWitness, Bool.false_eq_true, if_false] using previous
    · intro i onSingle
      have zero : i = 0 := by simp at onSingle; omega
      subst i
      change m.nm (s.nr 86 + 2 * lRows.length) = trigger.1.val ∧
        m.nm (s.nr 86 + 2 * lRows.length + 1) = trigger.2.val
      rw [mMemory, ← edgeCursor]
      exact ⟨appendAugmentationCrossingMemory_first edgeEntry trigger.1.val trigger.2.val,
        appendAugmentationCrossingMemory_second edgeEntry trigger.1.val trigger.2.val⟩
  let rightEntry := {m with pc := 0}
  have rightEncoded : ForestTraceArray rightEntry.nm (rightEntry.nr 84) right := by
    intro i within
    change m.nm (m.nr 84 + i) = right[i].val
    rw [mReg 84 (by decide), mBelow _ (by omega)]
    exact rArray i within
  have rightWitness (v : Fin k) (inRight : v ∈ augmentationWitnessChildren true right) :
      matchingForestWitnessAt rightEntry.nm (rightEntry.nr 90) v.val = ((witness v).1.val, (witness v).2.val) := by
    exact (preservedAugmentationWitness (t := rightEntry) (mReg 90 (by decide)) wSpace mBelow v).trans
      (records v (List.mem_append_right _ inRight))
  obtain ⟨q, ranR, ready, qCount, _, qPairs, qKeep, qFixed, qRR, qRM⟩ :=
    writeAugmentationTraceLeg_correct true right witness (s := rightEntry) rfl mReady rOdd
      ((mReg 11 (by decide)).trans rLength) rightEncoded
      (by change m.nr 84 + _ ≤ m.nr 86; rwa [mReg 84 (by decide), mBase])
      rightWitness (by change m.nr 90 + 2 * k ≤ m.nr 86; rwa [mReg 90 (by decide), mBase])
  have afterTriggerCount : m.nr 87 = (lRows ++ [trigger]).length := by
    rw [mCount]
    change l.nr 87 + 1 = _
    rw [lExact, List.length_append, List.length_singleton]
  have rightCursor : augmentationCrossingCursor rightEntry = s.nr 86 + 2 * (lRows ++ [trigger]).length := by
    change m.nr 86 + (m.nr 87 + m.nr 87) = _
    rw [mBase, afterTriggerCount, Nat.two_mul]
  have rightPairs : AugmentationCrossingArray q.nm (s.nr 86 + 2 * (lRows ++ [trigger]).length) rRows := by
    simpa [rightCursor, orientAugmentationWitness, rRows] using qPairs
  have prefixPairs : AugmentationCrossingArray q.nm (s.nr 86) (lRows ++ [trigger]) := by
    intro i inside
    exact ⟨(qKeep _ (.inl (by rw [rightCursor]; omega))).trans (enlargedLeft i inside).1,
      (qKeep _ (.inl (by rw [rightCursor]; omega))).trans (enlargedLeft i inside).2⟩
  have both := prefixPairs.append rightPairs
  have all := (((zeroRegister_runs 87 s entry running).append ranL).append join).append ranR
  have words : 2 * rows.length = left.length + right.length :=
    forestAugmentationCrossings_count witness trigger left right lOdd rOdd
  refine ⟨_, _, all, ready, ?_, ?_⟩
  · have halfLeft : lRows.length = left.length / 2 := by simp [lRows]
    have halfRight : rRows.length = right.length / 2 := by simp [rRows]
    change 1 + (6 + (17 * lRows.length + 1)) + 6 + (6 + (17 * rRows.length + 1)) ≤ _
    omega
  · refine ⟨?_, (qFixed 86 (by decide)).trans mBase, shape.symm ▸ both, words.le.trans fits,
      ?_, qRR.trans (mRR.trans lRR), qRM.trans (mRM.trans lRM), ?_⟩
    · change q.nr 87 = rows.length
      rw [qCount]
      change m.nr 87 + rRows.length = _
      simp only [afterTriggerCount, shape, List.length_append]
    · intro address outside
      have indices : rows.length = lRows.length + 1 + rRows.length := by
        simp only [shape, List.length_append, List.length_singleton]
      have afterTrigger : (lRows ++ [trigger]).length = lRows.length + 1 := by simp
      have rightOutside : address < augmentationCrossingCursor rightEntry ∨
          augmentationCrossingCursor rightEntry + 2 * rRows.length ≤ address := by
        rw [rightCursor, afterTrigger]
        omega
      have edgeOutside : address < s.nr 86 + 2 * lRows.length ∨ s.nr 86 + 2 * lRows.length + 2 ≤ address := by omega
      have leftOutside : address < augmentationCrossingCursor seed ∨
          augmentationCrossingCursor seed + 2 * lRows.length ≤ address := by rw [seedCursor]; omega
      exact (qKeep address rightOutside).trans ((mKeeps address edgeOutside).trans (lKeep address leftOutside))
    · intro r away
      exact (qFixed r away).trans (mReg r away)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentCrossings

/-! matching/MatchingAugmentRAM.lean -/
section RppSource_MatchingAugmentRAM
namespace VehicleRoutingSurvey.Routing



def installMatePair {n : ℕ} (base : ℕ) (memory : ℕ → ℕ) (p : Fin n × Fin n) : ℕ → ℕ :=
  Function.update (Function.update memory (base + p.1.val) p.2.val) (base + p.2.val) p.1.val













end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentRAM

/-! matching/MatchingAugmentInstallCell.lean -/
section RppSource_MatchingAugmentInstallCell
namespace VehicleRoutingSurvey.Routing





theorem installedAugmentationMateMemory_fin {k : ℕ} (s : ArithmeticState) (ports : Fin k × Fin k) :
    installedAugmentationMateMemory s (ports.1.val, ports.2.val) = installMatePair (s.nr 50) s.nm ports := rfl



















theorem rebaseAugmentationEndpoint_keeps {s : ArithmeticState} (port r : ℕ) (away : r ≠ 82) :
    (rebaseAugmentationEndpoint s port).nr r = s.nr r := by
  simp only [rebaseAugmentationEndpoint, queuedMatchingRebaseJob]
  split <;> simp [augmentationRepresentativeUpdate, Function.update_of_ne away]



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





theorem installedAugmentationMateMemory_keeps {k : ℕ} {s : ArithmeticState} {ports : ℕ × ℕ}
    (left : ports.1 < k) (right : ports.2 < k) {address : ℕ}
    (away : address < s.nr 50 ∨ s.nr 50 + k ≤ address) :
    installedAugmentationMateMemory s ports address = s.nm address := by
  have first : address ≠ s.nr 50 + ports.1 := by omega
  have second : address ≠ s.nr 50 + ports.2 := by omega
  simp [installedAugmentationMateMemory, Function.update_of_ne first, Function.update_of_ne second]





theorem installAugmentationCrossingState_keeps {s : ArithmeticState} (ports : ℕ × ℕ)
    (r : ℕ) (away : r ≠ 82) : (installAugmentationCrossingState s ports).nr r = s.nr r := by
  let m := {s with nm := installedAugmentationMateMemory s ports}
  exact (rebaseAugmentationEndpoint_keeps (s := rebaseAugmentationEndpoint m ports.1) ports.2 r away).trans
    (rebaseAugmentationEndpoint_keeps (s := m) ports.1 r away)





end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentInstallMemory

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

/-! matching/MatchingRebaseNodeProof.lean -/
section RppSource_MatchingRebaseNodeProof
namespace VehicleRoutingSurvey.Routing





















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
















end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseNodeProof

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




























end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseQueue

/-! matching/MatchingRebaseTaskBounds.lean -/
section RppSource_MatchingRebaseTaskBounds
namespace VehicleRoutingSurvey.Routing











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



















end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseTaskBounds

/-! matching/MatchingRebaseTaskOwner.lean -/
section RppSource_MatchingRebaseTaskOwner
namespace VehicleRoutingSurvey.Routing

theorem MatchingMemberJob.assignments_vertices (job : MatchingMemberJob) :
    job.assignments.map Prod.fst = job.tree.leaves := by
  cases kind : job.children <;>
    simp [MatchingMemberJob.assignments, MatchingMemberJob.tree, MatchingMemberTree.leaves,
      kind, List.map_map, Function.comp_def]













end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseTaskOwner

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




end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebasePortLabels

/-! matching/MatchingCycleRecordOrder.lean -/
section RppSource_MatchingCycleRecordOrder
namespace VehicleRoutingSurvey.Routing













theorem MatchingCycleRecordOrder.transport {s t : ArithmeticState} (order : MatchingCycleRecordOrder s)
    (scratch : matchingRebaseScratchEnd t = matchingRebaseScratchEnd s)
    (cursor : t.nr 76 = s.nr 76) (free : t.nr 68 = s.nr 68)
    (starts : ∀ i, 0 < i → i < s.nr 76 → matchingCycleRecordStart t i = matchingCycleRecordStart s i)
    (ends : ∀ i, 0 < i → i < s.nr 76 → matchingCycleRecordEnd t i = matchingCycleRecordEnd s i) :
    MatchingCycleRecordOrder t := by
  refine ⟨by rw [scratch, free]; exact order.scratch, by rw [cursor]; exact order.cursor, ?_, ?_⟩
  · intro i positive before
    rw [cursor] at before
    rw [scratch, free, starts i positive before, ends i positive before]
    exact order.bounded i positive before
  · intro i j positive earlier before
    rw [cursor] at before
    rw [ends i positive (earlier.trans before), starts j (positive.trans earlier) before]
    exact order.ordered i j positive earlier before




end VehicleRoutingSurvey.Routing
end RppSource_MatchingCycleRecordOrder

/-! matching/MatchingRebaseArchiveFootprint.lean -/
section RppSource_MatchingRebaseArchiveFootprint
namespace VehicleRoutingSurvey.Routing

/-- A properly allocated tree reads the fixed headers and its own record
intervals. This certifies the archive footprint directly from allocation order. -/
theorem MatchingMemberTree.readable_archive {s : ArithmeticState} (tree : MatchingMemberTree)
    (order : MatchingCycleRecordOrder s)
    (mapWalk : s.nr 79 + s.nr 55 ≤ s.nr 80)
    (encoded : tree.encoded s.nm (s.nr 77) (s.nr 78))
    (bounds : ∀ n ∈ tree.registryIds, 0 < n ∧ n < s.nr 76)
    (headers : ∀ n ∈ tree.registryIds, matchingRebaseHeaderArea s (s.nr 77 + n) ∧
      matchingRebaseHeaderArea s (s.nr 78 + n)) :
    tree.readable s.nm (s.nr 77) (s.nr 78)
      (fun a => matchingRebaseRecordArea s tree.registryIds a ∧ outsideMatchingMemberScratch s a) := by
  let all := tree.registryIds
  have traverse (sub : MatchingMemberTree) (enc : sub.encoded s.nm (s.nr 77) (s.nr 78))
      (subset : ∀ n ∈ sub.registryIds, n ∈ all) :
      sub.readable s.nm (s.nr 77) (s.nr 78)
        (fun a => matchingRebaseRecordArea s all a ∧ outsideMatchingMemberScratch s a) := by
    induction sub with
    | nil => trivial
    | leaf v rest ih => exact ih enc subset
    | blossom r n child rest ih tail =>
      have here := subset n (by simp [MatchingMemberTree.registryIds])
      have valid := bounds n here
      have begin := (order.bounded n valid.1 valid.2).1
      have header (a : ℕ) (h : matchingRebaseHeaderArea s a) :
          matchingRebaseRecordArea s all a ∧ outsideMatchingMemberScratch s a :=
        ⟨.inl h, .inl h.2, .inl (by have low := h.2; omega)⟩
      refine ⟨header _ (headers n here).1, header _ (headers n here).2, ?_,
        ih enc.2.2.1 (fun id h => subset id (by simp [MatchingMemberTree.registryIds, h])),
        tail enc.2.2.2 (fun id h => subset id (by simp [MatchingMemberTree.registryIds, h]))⟩
      intro i hi w width
      have row : matchingRebaseRowArea s n (s.nm (s.nr 77 + n) + 4 * i + w) := by
        have count := enc.1
        change s.nm (s.nr 78 + n) = child.arity at count
        simp only [matchingRebaseRowArea, matchingCycleRecordStart, matchingCycleRecordEnd, count]
        omega
      refine ⟨.inr ⟨n, here, row⟩, .inr ?_, .inr ?_⟩ <;>
        unfold matchingRebaseScratchEnd matchingCycleRecordStart at begin <;> omega
  exact traverse tree encoded (fun _ h => h)

def MatchingArchivedCycle.of_geometry {s : ArithmeticState} {n : ℕ} {children : MatchingMemberTree}
    (root : MatchingMemberRoot (matchingRebaseNodeState s n) children)
    (odd : Odd children.arity) (distinct : (children.rootKeys.map Prod.fst).Nodup)
    (geometry : MatchingRebaseCycleGeometry (matchingRebaseNodeState s n) children)
    (order : MatchingCycleRecordOrder s)
    (bounds : ∀ id ∈ n :: children.registryIds, 0 < id ∧ id < s.nr 76)
    (headers : ∀ id ∈ n :: children.registryIds, matchingRebaseHeaderArea s (s.nr 77 + id) ∧
      matchingRebaseHeaderArea s (s.nr 78 + id)) : MatchingArchivedCycle s n children := by
  let tree := MatchingMemberTree.blossom 0 n children .nil
  have ids : tree.registryIds = n :: children.registryIds := by simp [tree, MatchingMemberTree.registryIds]
  have encoded : tree.encoded s.nm (s.nr 77) (s.nr 78) := by simpa [tree, matchingRebaseNodeState] using root.encoded
  have mapWalk : s.nr 79 + s.nr 55 ≤ s.nr 80 := by simpa [matchingRebaseNodeState] using root.separated
  refine ⟨root, odd, distinct, geometry, ?_⟩
  simpa only [ids] using tree.readable_archive order mapWalk encoded (by rwa [ids]) (by rwa [ids])


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseArchiveFootprint

/-! matching/MatchingStageStorage.lean -/
section RppSource_MatchingStageStorage
namespace VehicleRoutingSurvey.Routing



def matchingFixedStorageRegisters : List ℕ :=
  [20,21,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,74,75,77,78,79,80,83,84,85,86,88,89,90]

theorem MatchingStageStorage.keeps {k : ℕ} {original s t : ArithmeticState}
    (layout : MatchingStageStorage k original s)
    (ports : ∀ r ∈ matchingFixedStorageRegisters, t.nr r = s.nr r) : MatchingStageStorage k original t := by
  have keep (r : ℕ) (inside : r ∈ matchingFixedStorageRegisters := by decide) := ports r inside
  have warm := layout.warm
  have nextWarm : MatchingWarmLayout t k := by
    obtain ⟨dim, count, parent, depth, mate, rep, ids, dict, pairs, rates, keys, offs⟩ := warm
    constructor <;> simp only [keep 21, keep 50, keep 51, keep 52, keep 53, keep 54, keep 55, keep 57,
      keep 58, keep 59, keep 60, keep 61, keep 65, keep 66] <;> assumption
  obtain ⟨_, floor, nodes, duals, starts, lengths, traces, right, marks, words, rows, promoted, mask, leaf, stack, metric⟩ := layout
  constructor <;> first | exact nextWarm | simp only [keep 20, keep 62, keep 65, keep 66, keep 74, keep 75, keep 77, keep 78,
    keep 79, keep 80, keep 83, keep 84, keep 85, keep 86, keep 88, keep 89, keep 90] <;> assumption




end VehicleRoutingSurvey.Routing
end RppSource_MatchingStageStorage

/-! matching/MatchingLiveCycleHighFrame.lean -/
section RppSource_MatchingLiveCycleHighFrame
namespace VehicleRoutingSurvey.Routing



theorem MatchingMemberTree.readableAnd {tree : MatchingMemberTree} {mem : ℕ → ℕ} {starts sizes : ℕ}
    {p q : ℕ → Prop} (left : tree.readable mem starts sizes p) (right : tree.readable mem starts sizes q) :
    tree.readable mem starts sizes (fun a => p a ∧ q a) := by
  induction tree with
  | nil => trivial
  | leaf v rest ih => exact ih left right
  | blossom r n c rest ci ri =>
    obtain ⟨a,b,d,e,f⟩ := left
    obtain ⟨x,y,z,w,h⟩ := right
    exact ⟨⟨a,x⟩, ⟨b,y⟩, fun i hi j hj => ⟨d i hi j hj,z i hi j hj⟩, ci e w, ri f h⟩




end VehicleRoutingSurvey.Routing
end RppSource_MatchingLiveCycleHighFrame

/-! matching/MatchingLiveCycleRebase.lean -/
section RppSource_MatchingLiveCycleRebase
namespace VehicleRoutingSurvey.Routing

/-- Rebase reads the same physical forward witnesses as expansion. The
endpoints lie in the two adjacent DFS jobs, including the wraparound row. -/
def MatchingLiveCycleMemory.rebaseGeometry {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    {e : MatchingLiveCycle state node B} {s : ArithmeticState} (memory : MatchingLiveCycleMemory e s) :
    MatchingRebaseCycleGeometry (matchingRebaseNodeState s (node B)) e.tree := by
  let g := e.geometry
  let jobs := e.tree.jobs none
  let cell (i : ℕ) := matchingCycleChildAt s.nm (matchingCycleRecordStart s (node B) + 4*i)
  let edge (i : ℕ) : ℕ × ℕ :=
    if h : i < g.cycle.length then ((g.edges ⟨i,h⟩).1.val,(g.edges ⟨i,h⟩).2.val) else (0,0)
  have jobsLength : jobs.length = g.cycle.length := (e.tree.jobs_length none).trans e.arity
  have row (i : Fin g.cycle.length) :
      (cell i.val).representative = (g.cycle.get i).val ∧
      ((cell i.val).endpointA,(cell i.val).endpointB) = ((g.edges i).1.val,(g.edges i).2.val) := memory.rows.records i
  have location (i : ℕ) (hi : i < jobs.length) :
      jobs[i].representative = (g.cycle.get ⟨i,jobsLength ▸ hi⟩).val := by
    have keys := matchingMemberJobRows (owner := none) memory.members.encoded.2.1 i hi
    have physical : (cell i).representative = jobs[i].representative := congrArg Prod.fst keys.1
    exact physical.symm.trans (row ⟨i,jobsLength ▸ hi⟩).1
  refine ⟨edge, ?_, ?_, ?_⟩
  · intro i hi
    have within : i < g.cycle.length := jobsLength ▸ hi
    have belongs := (e.owner jobs[i] (List.getElem_mem hi) _ (location i hi)).2 (g.edges ⟨i,within⟩).1
    simpa only [edge,dif_pos within] using belongs.mpr (g.source ⟨i,within⟩)
  · intro i hi
    have within : i < g.cycle.length := jobsLength ▸ hi
    let j := (i+1) % jobs.length
    have hj : j < jobs.length := Nat.mod_lt _ (Nat.zero_lt_of_lt hi)
    have belongs := (e.owner jobs[j] (List.getElem_mem hj) _ (location j hj)).2 (g.edges ⟨i,within⟩).2
    have reaches := g.target ⟨i,within⟩
    have index : (⟨j,jobsLength ▸ hj⟩ : Fin g.cycle.length) =
        ⟨(i+1) % g.cycle.length,Nat.mod_lt _ (Nat.zero_lt_of_lt within)⟩ := by
      apply Fin.ext
      exact congrArg ((i+1) % ·) jobsLength
    rw [index] at belongs
    simpa only [edge,dif_pos within] using belongs.mpr reaches
  · intro i hi
    have within : i < g.cycle.length := e.arity ▸ hi
    exact .inl (by simpa [edge,within,cell,matchingRebaseNodeState,matchingCycleRecordStart] using (row ⟨i,within⟩).2)

def MatchingLiveCycleMemory.archived {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    {e : MatchingLiveCycle state node B} {s : ArithmeticState} (memory : MatchingLiveCycleMemory e s)
    (order : MatchingCycleRecordOrder s)
    (bounds : ∀ id ∈ node B :: e.tree.registryIds, 0 < id ∧ id < s.nr 76)
    (headers : ∀ id ∈ node B :: e.tree.registryIds, matchingRebaseHeaderArea s (s.nr 77 + id) ∧
      matchingRebaseHeaderArea s (s.nr 78 + id)) : MatchingArchivedCycle s (node B) e.tree := by
  apply MatchingArchivedCycle.of_geometry memory.members (e.arity.symm ▸ e.geometry.odd) _
    memory.rebaseGeometry order bounds headers
  rw [e.keys]
  exact e.geometry.distinct.map Fin.val_injective

end VehicleRoutingSurvey.Routing
end RppSource_MatchingLiveCycleRebase

/-! matching/MatchingAugmentArchiveFrame.lean -/
section RppSource_MatchingAugmentArchiveFrame
namespace VehicleRoutingSurvey.Routing



theorem MatchingAugmentArchiveFrame.recordOrder {s t : ArithmeticState} (frame : MatchingAugmentArchiveFrame s t)
    (order : MatchingCycleRecordOrder s) : MatchingCycleRecordOrder t := by
  have keep (r : ℕ) (h : r ∈ ([50,55,68,76,77,78,79,80] : List ℕ) := by decide) := frame.fixed r h
  have start (n : ℕ) (lo : 0 < n) (hi : n < s.nr 76) : matchingCycleRecordStart t n = matchingCycleRecordStart s n := by
    simp only [matchingCycleRecordStart,keep 77,(frame.headers n lo hi).1]
  exact order.transport (by simp only [matchingRebaseScratchEnd,keep 80,keep 55]) (keep 76) (keep 68)
    start (fun n lo hi => by simp only [matchingCycleRecordEnd,start n lo hi,keep 78,(frame.headers n lo hi).2])

/-- Transfer the old recursive encoding and each oriented row, even when
the prefix overwrites other arrays above the mate table. -/
def MatchingAugmentArchiveFrame.cycle {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    {e : MatchingLiveCycle old node B} {s t : ArithmeticState}
    (frame : MatchingAugmentArchiveFrame s t) (memory : MatchingLiveCycleMemory e s)
    (bounds : ∀ n ∈ node B :: e.tree.registryIds, 0 < n ∧ n < s.nr 76) : MatchingLiveCycleMemory e t := by
  let a := matchingRebaseNodeState s (node B)
  let b := matchingRebaseNodeState t (node B)
  let root := MatchingMemberTree.blossom 0 (node B) e.tree .nil
  let safe (x : ℕ) := ∃ n, 0 < n ∧ n < s.nr 76 ∧
    (x = s.nr 77+n ∨ x = s.nr 78+n ∨ matchingRebaseRowArea s n x)
  have keep (r : ℕ) (h : r ∈ ([50,55,68,76,77,78,79,80] : List ℕ) := by decide) := frame.fixed r h
  have fixed (r : ℕ) (h : r ∈ ([50,55,68,76,77,78,79,80] : List ℕ) := by decide) : b.nr r = a.nr r := by
    have away : r ≠ 22 := by simp at h; omega
    simpa [a,b,matchingRebaseNodeState,Function.update_of_ne away] using keep r h
  have available (x : ℕ) (good : safe x) : t.nm x = s.nm x := by
    obtain ⟨n,l,h,hx⟩ := good
    rcases hx with rfl | rfl | inside
    · exact (frame.headers _ l h).1
    · exact (frame.headers _ l h).2
    · exact frame.rows _ l h _ inside
  have reads (tree : MatchingMemberTree) (enc : tree.encoded s.nm (s.nr 77) (s.nr 78))
      (ids : ∀ n ∈ tree.registryIds, 0 < n ∧ n < s.nr 76) :
      tree.readable s.nm (s.nr 77) (s.nr 78) safe := by
    induction tree with
    | nil => trivial
    | leaf _ tail ih => exact ih enc ids
    | blossom r n child tail ci ti =>
      have h := ids n (by simp [MatchingMemberTree.registryIds])
      refine ⟨⟨n,h.1,h.2,.inl rfl⟩,⟨n,h.1,h.2,.inr (.inl rfl)⟩,?_,
        ci enc.2.2.1 (fun j hj => ids j (by simp [MatchingMemberTree.registryIds,hj])),
        ti enc.2.2.2 (fun j hj => ids j (by simp [MatchingMemberTree.registryIds,hj]))⟩
      intro i hi w hw
      have count : s.nm (s.nr 78+n) = child.arity := enc.1
      refine ⟨n,h.1,h.2,.inr (.inr ?_)⟩
      simp only [matchingRebaseRowArea,matchingCycleRecordStart,matchingCycleRecordEnd,count]
      omega
  have before : MatchingMemberRoot a e.tree := memory.members
  have encoded : root.encoded s.nm (s.nr 77) (s.nr 78) := by simpa [a,root,matchingRebaseNodeState] using before.encoded
  have oldRead : root.readable s.nm (s.nr 77) (s.nr 78) (outsideMatchingMemberScratch a) := by
    simpa [a,root,matchingRebaseNodeState] using before.readable
  have oldHigh : root.recordsAbove s.nm (s.nr 77) (s.nr 80+3*s.nr 55) := by
    simpa [a,root,matchingRebaseNodeState] using before.above
  have region := reads root encoded (by simpa [root,MatchingMemberTree.registryIds] using bounds)
  have scratch : outsideMatchingMemberScratch b = outsideMatchingMemberScratch a := by
    funext x
    simp only [outsideMatchingMemberScratch,fixed 79,fixed 80,fixed 55]
  have rootAt : MatchingMemberRoot b e.tree := by
    have id : b.nr 22 = a.nr 22 := by simp [a,b,matchingRebaseNodeState]
    refine ⟨id.symm ▸ before.proper,?_,?_,?_,before.unique,by rw [fixed 55]; exact before.valid,
      by rw [fixed 79,fixed 55,fixed 80]; exact before.separated⟩
    · simpa [root,b,matchingRebaseNodeState,keep 77,keep 78] using MatchingMemberTree.encoded_congr encoded region available
    · rw [scratch]
      simpa only [root,b,matchingRebaseNodeState,Function.update_self,Function.update_of_ne (by decide : 77 ≠ 22),
        Function.update_of_ne (by decide : 78 ≠ 22),keep 77,keep 78] using
        MatchingMemberTree.readable_after_move (tree := root)
          (MatchingMemberTree.readableAnd (tree := root) region oldRead) available
    · simpa [root,b,matchingRebaseNodeState,keep 77,keep 80,keep 55] using
        MatchingMemberTree.recordsAbove_after_move region oldHigh available
  have range := bounds (node B) (by simp)
  have start : matchingCycleRecordStart t (node B) = matchingCycleRecordStart s (node B) := by
    simp [matchingCycleRecordStart,keep 77,(frame.headers _ range.1 range.2).1]
  refine ⟨rootAt,⟨?_,?_⟩⟩
  · rw [keep 78,(frame.headers _ range.1 range.2).2]
    exact memory.rows.length
  · intro i
    let addr := matchingCycleRecordStart s (node B) + 4*i.val
    have read (w : ℕ) (hw : w < 4) : t.nm (addr+w) = s.nm (addr+w) := by
      apply frame.rows _ range.1 range.2
      simp only [addr,matchingRebaseRowArea,matchingCycleRecordEnd,memory.rows.length]
      have := i.isLt
      omega
    have word : t.nm addr = s.nm addr := read 0 (by decide)
    have cell : matchingCycleChildAt t.nm addr = matchingCycleChildAt s.nm addr := by
      simp only [matchingCycleChildAt,word,read 1 (by decide),read 2 (by decide),read 3 (by decide)]
    simpa only [start, show matchingCycleChildAt t.nm (matchingCycleRecordStart s (node B) + 4*i.val) = _ from cell]
      using memory.rows.records i


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentArchiveFrame

/-! matching/MatchingAugmentFromTrace.lean -/
section RppSource_MatchingAugmentFromTrace
namespace VehicleRoutingSurvey.Routing

/-- Decode the two disjoint alternating-forest chains as new original
crossing edges. The parent-witness invariant is needed only at nonroots. -/
theorem writeAugmentationCrossings_fromTrace {k : ℕ} {forest : AlternatingForestState (Fin k)}
    {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop}
    {u v : Fin k} {uParent vParent : Option (Fin k)} {base : ℕ} {initial s : ArithmeticState}
    (valid : forest.valid mate tight) (outerU : forest.role u = .outer uParent)
    (outerV : forest.role v = .outer vParent) (traced : MatchingForestTraceResult forest u v base initial s)
    (differentTrees : forest.commonAncestor u v = none)
    (witness : Fin k → Fin k × Fin k) (trigger : Fin k × Fin k)
    (entry : s.pc = 0) (running : s.halted = false)
    (leftBelow : s.nr 83 + (forest.traceToRoot u).length ≤ s.nr 86)
    (rightBelow : s.nr 84 + (forest.traceToRoot v).length ≤ s.nr 86)
    (saved : ∀ child parent : Fin k, (forest.role child).parent = some parent →
      matchingForestWitnessAt s.nm (s.nr 90) child.val = ((witness child).1.val, (witness child).2.val))
    (witnessBelow : s.nr 90 + 2 * k ≤ s.nr 86)
    (original : (s.nr 92, s.nr 93) = (trigger.1.val, trigger.2.val)) :
    let rows := forestAugmentationCrossings witness trigger (forest.traceToRoot u) (forest.traceToRoot v)
    ∃ (t : ArithmeticState) (steps : ℕ), BlockRuns writeAugmentationCrossingsBlock steps s t ∧
      t.halted = false ∧ steps ≤ 17 * k + 21 ∧ AugmentationCrossingsReady rows s t := by
  intro rows
  have uMarked : forest.role u ≠ .unlabelled := by simp [outerU]
  have vMarked : forest.role v ≠ .unlabelled := by simp [outerV]
  have lOdd := AlternatingForestState.outerTrace_length_odd valid outerU
  have rOdd := AlternatingForestState.outerTrace_length_odd valid outerV
  have fits := AlternatingForestState.disjointOuterTraces_length_le valid uMarked vMarked differentTrees
  have lArr : ForestTraceArray s.nm (s.nr 83) (forest.traceToRoot u) := by
    rw [traced.registers 83 (by decide)]
    exact traced.left
  have rArr : ForestTraceArray s.nm (s.nr 84) (forest.traceToRoot v) := by
    rw [traced.registers 84 (by decide)]
    exact traced.right
  have records {x : Fin k} (marked : forest.role x ≠ .unlabelled) (forward : Bool)
      (odd : (forest.traceToRoot x).length % 2 = 1) (child : Fin k)
      (used : child ∈ augmentationWitnessChildren forward (forest.traceToRoot x)) :
      matchingForestWitnessAt s.nm (s.nr 90) child.val = ((witness child).1.val, (witness child).2.val) := by
    obtain ⟨_, _, _, chain, _⟩ := AlternatingForestState.traceToRoot_spec valid marked
    obtain ⟨i, within, childAt⟩ := List.mem_iff_getElem.mp used
    let trail := forest.traceToRoot x
    let slot := augmentationTraceIndex forward (augmentationWitnessStart forward trail.length) i
    have enough : i < trail.length / 2 := by simpa [trail] using within
    have bound : slot + 1 < trail.length := augmentationWitnessIndex_parent_inBounds forward odd enough
    let parent := trail[slot + 1]
    have found : trail[slot]'(by omega) = child :=
      (augmentationWitnessChildren_get forward trail i within).symm.trans childAt
    have link : (forest.role child).parent = some parent := by
      rw [← found]
      exact (List.isChain_iff_getElem.mp chain slot bound).1
    exact saved child parent link
  apply writeAugmentationCrossingsBlock_correct _ _ witness trigger entry running lOdd rOdd fits
    traced.leftCount traced.rightCount lArr rArr leftBelow rightBelow _ witnessBelow original
  intro w visited
  rcases List.mem_append.mp visited with l | r
  · exact records uMarked false lOdd w l
  · exact records vMarked true rOdd w r

end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentFromTrace

/-! matching/MatchingAugmentHandler.lean -/
section RppSource_MatchingAugmentHandler
namespace VehicleRoutingSurvey.Routing



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

/-! matching/MatchingAugmentInstallRefinement.lean -/
section RppSource_MatchingAugmentInstallRefinement
namespace VehicleRoutingSurvey.Routing

def augmentationRebaseJobAt (s : ArithmeticState) (i : ℕ) : ℕ × ℕ :=
  let address := matchingRebaseJobAddress s i
  (s.nm address, s.nm (address + 1))

private theorem queuedMatchingRebaseJob_below {s : ArithmeticState} {node port address : ℕ}
    (below : address < s.nr 81) : (queuedMatchingRebaseJob s node port).nm address = s.nm address := by
  have left : address ≠ matchingRebaseJobAddress s (s.nr 82) := by unfold matchingRebaseJobAddress; omega
  have right : address ≠ matchingRebaseJobAddress s (s.nr 82) + 1 := by unfold matchingRebaseJobAddress; omega
  by_cases vacant : node = 0 <;> simp [queuedMatchingRebaseJob, vacant, pushedMatchingRebaseJob,
    Function.update_of_ne left, Function.update_of_ne right]

private theorem queuedMatchingRebaseJob_prior {s : ArithmeticState} {node port i : ℕ}
    (earlier : i < s.nr 82) : augmentationRebaseJobAt (queuedMatchingRebaseJob s node port) i =
      augmentationRebaseJobAt s i := by
  by_cases vacant : node = 0
  · simp [queuedMatchingRebaseJob, vacant]
  · have atLeft : matchingRebaseJobAddress s i ≠ matchingRebaseJobAddress s (s.nr 82) := by
      unfold matchingRebaseJobAddress; omega
    have atRight : matchingRebaseJobAddress s i ≠ matchingRebaseJobAddress s (s.nr 82) + 1 := by
      unfold matchingRebaseJobAddress; omega
    have nextLeft : matchingRebaseJobAddress s i + 1 ≠ matchingRebaseJobAddress s (s.nr 82) := by
      unfold matchingRebaseJobAddress; omega
    have nextRight : matchingRebaseJobAddress s i + 1 ≠ matchingRebaseJobAddress s (s.nr 82) + 1 := by
      unfold matchingRebaseJobAddress; omega
    have base : (queuedMatchingRebaseJob s node port).nr 81 = s.nr 81 := by
      simp [queuedMatchingRebaseJob, vacant]
    simp only [augmentationRebaseJobAt, matchingRebaseJobAddress, base]
    change ((queuedMatchingRebaseJob s node port).nm (matchingRebaseJobAddress s i),
      (queuedMatchingRebaseJob s node port).nm (matchingRebaseJobAddress s i + 1)) = _
    simp [queuedMatchingRebaseJob, vacant, pushedMatchingRebaseJob,
      Function.update_of_ne atLeft, Function.update_of_ne atRight,
      Function.update_of_ne nextLeft, Function.update_of_ne nextRight] <;> simp [matchingRebaseJobAddress]

private theorem queuedMatchingRebaseJob_latest {s : ArithmeticState} {node port : ℕ}
    (present : node ≠ 0) : augmentationRebaseJobAt (queuedMatchingRebaseJob s node port) (s.nr 82) =
      (node, port) := by
  have base : (queuedMatchingRebaseJob s node port).nr 81 = s.nr 81 := by
    simp [queuedMatchingRebaseJob, present]
  simp only [augmentationRebaseJobAt, matchingRebaseJobAddress, base]
  change ((queuedMatchingRebaseJob s node port).nm (matchingRebaseJobAddress s (s.nr 82)),
    (queuedMatchingRebaseJob s node port).nm (matchingRebaseJobAddress s (s.nr 82) + 1)) = _
  simp [queuedMatchingRebaseJob, present, pushedMatchingRebaseJob]

/-- Moving a top-level representative preserves the original mate and representative
tables. A nontrivial moved node is queued with exactly its new exposed original. -/
structure AugmentationEndpointProjection {k : ℕ} (s t : ArithmeticState) (old port : Fin k) : Prop where
  mates : ∀ v : Fin k, t.nm (s.nr 50 + v.val) = s.nm (s.nr 50 + v.val)
  originalMap : ∀ v : Fin k, t.nm (s.nr 57 + v.val) = s.nm (s.nr 57 + v.val)
  nodes : ∀ v : Fin k, t.nm (s.nr 74 + v.val) =
    if v = port then s.nm (s.nr 74 + old.val) else if v = old then 0 else s.nm (s.nr 74 + v.val)
  replacements : ∀ v : Fin k, t.nm (s.nr 89 + v.val) =
    if v = old then port.val else s.nm (s.nr 89 + v.val)
  jobs : t.nr 82 = s.nr 82 + (if s.nm (s.nr 74 + old.val) = 0 then 0 else 1)
  priorJobs : ∀ i < s.nr 82, augmentationRebaseJobAt t i = augmentationRebaseJobAt s i
  lastJob : s.nm (s.nr 74 + old.val) ≠ 0 →
    augmentationRebaseJobAt t (s.nr 82) = (s.nm (s.nr 74 + old.val), port.val)

theorem rebaseAugmentationEndpoint_projection {k : ℕ} {s : ArithmeticState} {old port : Fin k}
    (layout : AugmentationInstallLayout k s) (original : s.nm (s.nr 57 + port.val) = old.val) :
    AugmentationEndpointProjection s (rebaseAugmentationEndpoint s port.val) old port := by
  let node := s.nm (s.nr 74 + old.val)
  let moved := augmentationRepresentativeUpdate s port.val
  let t := rebaseAugmentationEndpoint s port.val
  have shape : t = queuedMatchingRebaseJob moved node port.val := by
    simp [t, rebaseAugmentationEndpoint, moved, node, original]
  have changes : moved.nm = Function.update (Function.update (Function.update
      s.nm (s.nr 89 + old.val) port.val) (s.nr 74 + old.val) 0) (s.nr 74 + port.val) node := by
    simp [moved, augmentationRepresentativeUpdate, node, original]
  have oldFinite := old.isLt
  have portFinite := port.isLt
  obtain ⟨mates, map, nodes, pairs, work⟩ := layout
  have kept (address : ℕ) (below : address < s.nr 81) : t.nm address = moved.nm address := by
    rw [shape]
    exact queuedMatchingRebaseJob_below (s := moved) below
  have untouched (address : ℕ) (one : address ≠ s.nr 89 + old.val)
      (two : address ≠ s.nr 74 + old.val) (three : address ≠ s.nr 74 + port.val) :
      moved.nm address = s.nm address := by
    rw [changes]
    simp [Function.update_of_ne one, Function.update_of_ne two, Function.update_of_ne three]
  have movedJob (i : ℕ) : augmentationRebaseJobAt moved i = augmentationRebaseJobAt s i := by
    have start : s.nr 81 ≤ matchingRebaseJobAddress s i := by unfold matchingRebaseJobAddress; omega
    change (moved.nm (matchingRebaseJobAddress s i), moved.nm (matchingRebaseJobAddress s i + 1)) = _
    rw [untouched (matchingRebaseJobAddress s i) (by omega) (by omega) (by omega),
      untouched (matchingRebaseJobAddress s i + 1) (by omega) (by omega) (by omega)]
    rfl
  constructor
  · intro v
    have bound := v.isLt
    exact (kept _ (by omega)).trans (untouched _ (by omega) (by omega) (by omega))
  · intro v
    have bound := v.isLt
    exact (kept _ (by omega)).trans (untouched _ (by omega) (by omega) (by omega))
  · intro v
    have bound := v.isLt
    rw [kept (s.nr 74 + v.val) (by omega), changes]
    have workSeparate : s.nr 74 + v.val ≠ s.nr 89 + old.val := by omega
    by_cases atPort : v = port
    · subst v
      simp [node]
    · have portSeparate : s.nr 74 + v.val ≠ s.nr 74 + port.val := by
        intro impossible
        exact atPort (Fin.ext (by omega))
      rw [Function.update_of_ne portSeparate, if_neg atPort]
      by_cases atOld : v = old
      · subst v
        simp
      · have oldSeparate : s.nr 74 + v.val ≠ s.nr 74 + old.val := by
          intro impossible
          exact atOld (Fin.ext (by omega))
        simp [atOld, Function.update_of_ne oldSeparate, Function.update_of_ne workSeparate]
  · intro v
    have bound := v.isLt
    rw [kept (s.nr 89 + v.val) (by omega), changes]
    have oldSeparate : s.nr 89 + v.val ≠ s.nr 74 + old.val := by omega
    have portSeparate : s.nr 89 + v.val ≠ s.nr 74 + port.val := by omega
    rw [Function.update_of_ne portSeparate, Function.update_of_ne oldSeparate]
    by_cases atOld : v = old
    · subst v
      simp
    · have workSeparate : s.nr 89 + v.val ≠ s.nr 89 + old.val := by
        intro impossible
        exact atOld (Fin.ext (by omega))
      simp [atOld, Function.update_of_ne workSeparate]
  · change t.nr 82 = s.nr 82 + (if node = 0 then 0 else 1)
    rw [shape]
    by_cases vacant : node = 0 <;>
      simp [queuedMatchingRebaseJob, moved, augmentationRepresentativeUpdate, vacant]
  · intro i previous
    change augmentationRebaseJobAt t i = augmentationRebaseJobAt s i
    rw [shape]
    exact (queuedMatchingRebaseJob_prior (s := moved) previous).trans (movedJob i)
  · intro present
    change augmentationRebaseJobAt t (s.nr 82) = (node, port.val)
    rw [shape]
    exact queuedMatchingRebaseJob_latest (s := moved) present

end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentInstallRefinement

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



/-- Table observations used to connect installation to recursive rebasing. -/
structure AugmentationCrossingTables {k : ℕ} (s : ArithmeticState) (mates : ℕ → ℕ)
    (original replacements : Fin k → Fin k) : Prop where
  mates : ∀ v : Fin k, s.nm (s.nr 50 + v.val) = mates (s.nr 50 + v.val)
  original : ∀ v : Fin k, s.nm (s.nr 57 + v.val) = (original v).val
  replacement : ∀ v : Fin k, s.nm (s.nr 89 + v.val) = (replacements v).val

private theorem installMatePair_same {k : ℕ} {m n : ℕ → ℕ} {base : ℕ}
    (same : ∀ v : Fin k, m (base + v.val) = n (base + v.val))
    (ports : Fin k × Fin k) (v : Fin k) :
    installMatePair base m ports (base + v.val) = installMatePair base n ports (base + v.val) := by
  simp only [installMatePair, Function.update_apply]
  split <;> rename_i atRight
  · rfl
  · split
    · rfl
    · exact same v

theorem installAugmentationCrossingState_tables {k : ℕ} {s : ArithmeticState}
    {mates : ℕ → ℕ} {original replacements : Fin k → Fin k}
    (layout : AugmentationInstallLayout k s) (before : AugmentationCrossingTables s mates original replacements)
    (ports : Fin k × Fin k) :
    let t := installAugmentationCrossingState s (ports.1.val, ports.2.val)
    AugmentationInstallLayout k t ∧
      AugmentationCrossingTables t (installMatePair (s.nr 50) mates ports) original
        (chooseAugmentationRepresentatives original replacements ports) := by
  intro t
  let m := {s with nm := installedAugmentationMateMemory s (ports.1.val, ports.2.val)}
  let l := rebaseAugmentationEndpoint m ports.1.val
  have mLayout : AugmentationInstallLayout k m := layout.transport (fun _ _ => rfl)
  have lLayout : AugmentationInstallLayout k l := mLayout.transport fun r used =>
    rebaseAugmentationEndpoint_keeps _ r (by intro equal; simp [equal] at used)
  have tLayout : AugmentationInstallLayout k t := lLayout.transport fun r used =>
    rebaseAugmentationEndpoint_keeps _ r (by intro equal; simp [equal] at used)
  have origM (v : Fin k) : m.nm (m.nr 57 + v.val) = (original v).val :=
    (installedAugmentationMateMemory_keeps ports.1.isLt ports.2.isLt (layout.map_unwritten v.isLt).1).trans
      (before.original v)
  have leftMove := rebaseAugmentationEndpoint_projection mLayout (origM ports.1)
  have l57 : l.nr 57 = m.nr 57 := rebaseAugmentationEndpoint_keeps _ 57 (by decide)
  have l89 : l.nr 89 = m.nr 89 := rebaseAugmentationEndpoint_keeps _ 89 (by decide)
  have l50 : l.nr 50 = m.nr 50 := rebaseAugmentationEndpoint_keeps _ 50 (by decide)
  have origL (v : Fin k) : l.nm (l.nr 57 + v.val) = (original v).val := by
    rw [l57]
    exact (leftMove.originalMap v).trans (origM v)
  have rightMove := rebaseAugmentationEndpoint_projection lLayout (origL ports.2)
  have t57 : t.nr 57 = l.nr 57 := rebaseAugmentationEndpoint_keeps _ 57 (by decide)
  have t50 : t.nr 50 = l.nr 50 := rebaseAugmentationEndpoint_keeps _ 50 (by decide)
  have t89 : t.nr 89 = l.nr 89 := rebaseAugmentationEndpoint_keeps _ 89 (by decide)
  have workM (v : Fin k) : m.nm (m.nr 89 + v.val) = (replacements v).val := by
    have mateMap := layout.matesBeforeMap
    have mapNodes := layout.mapBeforeNodes
    have nodesPairs := layout.nodesBeforePairs
    have pairsWork := layout.pairsBeforeRepresentativeWork
    have pastMates : s.nr 50 + k ≤ s.nr 89 + v.val := by omega
    exact (installedAugmentationMateMemory_keeps ports.1.isLt ports.2.isLt (.inr pastMates)).trans
      (before.replacement v)
  refine ⟨tLayout, ?_, ?_, ?_⟩
  · intro v
    change t.nm (t.nr 50 + v.val) = _
    rw [t50]
    change (rebaseAugmentationEndpoint l ports.2.val).nm (l.nr 50 + v.val) = _
    rw [rightMove.mates v, l50]
    change (rebaseAugmentationEndpoint m ports.1.val).nm (m.nr 50 + v.val) = _
    rw [leftMove.mates v]
    change installedAugmentationMateMemory s (ports.1.val, ports.2.val) (s.nr 50 + v.val) = _
    rw [installedAugmentationMateMemory_fin]
    exact installMatePair_same before.mates ports v
  · intro v
    change t.nm (t.nr 57 + v.val) = _
    rw [t57]
    change (rebaseAugmentationEndpoint l ports.2.val).nm (l.nr 57 + v.val) = _
    rw [rightMove.originalMap v]
    exact origL v
  · intro v
    change t.nm (t.nr 89 + v.val) = _
    rw [t89]
    change (rebaseAugmentationEndpoint l ports.2.val).nm (l.nr 89 + v.val) = _
    rw [rightMove.replacements v]
    by_cases onRight : v = original ports.2
    · simp [chooseAugmentationRepresentatives, onRight]
    · rw [if_neg onRight, l89]
      change (rebaseAugmentationEndpoint m ports.1.val).nm (m.nr 89 + v.val) = _
      rw [leftMove.replacements v, workM v]
      rw [chooseAugmentationRepresentatives, Function.update_of_ne onRight]
      by_cases onLeft : v = original ports.1 <;>
        simp [Function.update_apply, onLeft]

/-- Chart the mate and representative tables after all crossing records.
The old-to-new map is the fold of the exact exposed-port choices. -/
theorem installAugmentationCrossingRows_tables {k : ℕ} {s : ArithmeticState}
    {mates : ℕ → ℕ} {original replacements : Fin k → Fin k}
    (layout : AugmentationInstallLayout k s) (before : AugmentationCrossingTables s mates original replacements)
    (rows : List (Fin k × Fin k)) :
    let t := installAugmentationCrossingRows s rows
    AugmentationInstallLayout k t ∧
      AugmentationCrossingTables t (rows.foldl (installMatePair (s.nr 50)) mates) original
        (rows.foldl (chooseAugmentationRepresentatives original) replacements) := by
  induction rows generalizing s mates replacements with
  | nil => exact ⟨layout, before⟩
  | cons pair rest ih =>
    let next := installAugmentationCrossingState s (pair.1.val, pair.2.val)
    have fixed : (installAugmentationCrossingState s (pair.1.val, pair.2.val)).nr 50 = s.nr 50 :=
      installAugmentationCrossingState_keeps _ 50 (by decide)
    obtain ⟨nextLayout, nextTables⟩ := installAugmentationCrossingState_tables layout before pair
    have remains := ih nextLayout nextTables
    change AugmentationInstallLayout k (installAugmentationCrossingRows next rest) ∧
      AugmentationCrossingTables (installAugmentationCrossingRows next rest)
        (rest.foldl (installMatePair (s.nr 50)) (installMatePair (s.nr 50) mates pair)) original
        (rest.foldl (chooseAugmentationRepresentatives original)
          (chooseAugmentationRepresentatives original replacements pair))
    simpa only [fixed] using remains

end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentCrossingSemantics

/-! matching/MatchingAugmentPreRebaseSemantics.lean -/
section RppSource_MatchingAugmentPreRebaseSemantics
namespace VehicleRoutingSurvey.Routing

theorem installAugmentationCrossingRows_keeps {k : ℕ} {s : ArithmeticState}
    (rows : List (Fin k × Fin k)) (r : ℕ) (away : r ≠ 82) :
    (installAugmentationCrossingRows s rows).nr r = s.nr r := by
  induction rows generalizing s with
  | nil => rfl
  | cons ports rows ih =>
    exact (ih (s := installAugmentationCrossingState s (ports.1.val, ports.2.val))).trans
      (installAugmentationCrossingState_keeps _ r away)

/-- Before the recursive lift, each original crossing endpoint already has its
new mate. The representative table names exactly the selected new ports. -/
theorem AugmentationPreRebaseReady.typedTables {k : ℕ} {s t : ArithmeticState}
    {rows : List (Fin k × Fin k)} (ready : AugmentationPreRebaseReady rows s t)
    (layout : AugmentationInstallLayout k (augmentationCrossingSeed s k))
    (representatives : Fin k → Fin k)
    (original : ∀ v : Fin k, s.nm (s.nr 57 + v.val) = (representatives v).val) :
    let nextRep := rows.foldl (chooseAugmentationRepresentatives representatives) id
    (∀ v : Fin k, t.nm (s.nr 50 + v.val) =
      (rows.foldl (installMatePair (s.nr 50)) s.nm) (s.nr 50 + v.val)) ∧
    ∀ v : Fin k, t.nm (s.nr 57 + v.val) = (nextRep (representatives v)).val := by
  intro nextRep
  let seed := augmentationCrossingSeed s k
  let model := installAugmentationCrossingRows seed rows
  change AugmentationInstallLayout k seed at layout
  have seed50 : seed.nr 50 = s.nr 50 := by simp [seed, augmentationCrossingSeed]
  have seed57 : seed.nr 57 = s.nr 57 := by simp [seed, augmentationCrossingSeed]
  have seed74 : seed.nr 74 = s.nr 74 := by simp [seed, augmentationCrossingSeed]
  have seed86 : seed.nr 86 = s.nr 86 := by simp [seed, augmentationCrossingSeed]
  have seed89 : seed.nr 89 = s.nr 89 := by simp [seed, augmentationCrossingSeed]
  have beforeMap : s.nr 50 + k ≤ s.nr 57 := by simpa only [seed50, seed57] using layout.matesBeforeMap
  have mapThenNode : s.nr 57 + k ≤ s.nr 74 := by simpa only [seed57, seed74] using layout.mapBeforeNodes
  have nodeThenPair : s.nr 74 + k ≤ s.nr 86 := by simpa only [seed74, seed86] using layout.nodesBeforePairs
  have pairThenWork : s.nr 86 + k ≤ s.nr 89 := by simpa only [seed86, seed89] using layout.pairsBeforeRepresentativeWork
  have restored : AugmentationCrossingTables seed s.nm representatives id := by
    constructor
    · intro v
      have within := v.isLt
      have elsewhere : s.nr 50 + v.val < s.nr 89 := by omega
      rw [seed50]
      simp [seed, augmentationCrossingSeed, not_le.mpr elsewhere]
    · intro v
      have within := v.isLt
      have elsewhere : s.nr 57 + v.val < s.nr 89 := by omega
      rw [seed57]
      simpa [seed, augmentationCrossingSeed, not_le.mpr elsewhere] using original v
    · intro v
      have within := v.isLt
      rw [seed89]
      simp [seed, augmentationCrossingSeed, within]
  have observed := (installAugmentationCrossingRows_tables layout restored rows).2
  have model50 : model.nr 50 = s.nr 50 :=
    (installAugmentationCrossingRows_keeps rows 50 (by decide)).trans seed50
  have model57 : model.nr 57 = s.nr 57 :=
    (installAugmentationCrossingRows_keeps rows 57 (by decide)).trans seed57
  have model89 : model.nr 89 = s.nr 89 :=
    (installAugmentationCrossingRows_keeps rows 89 (by decide)).trans seed89
  constructor
  · intro v
    have finite := v.isLt
    have stays : ¬(s.nr 57 ≤ s.nr 50 + v.val ∧ s.nr 50 + v.val < s.nr 57 + k) := by omega
    rw [ready.memory, remappedAugmentationMemory, if_neg stays]
    have slot := observed.mates v
    change model.nm (model.nr 50 + v.val) = (rows.foldl (installMatePair (seed.nr 50)) s.nm) (model.nr 50 + v.val) at slot
    rwa [model50, seed50] at slot
  · intro v
    have finite := v.isLt
    have touched : s.nr 57 ≤ s.nr 57 + v.val ∧ s.nr 57 + v.val < s.nr 57 + k := by omega
    have source := observed.original v
    change model.nm (model.nr 57 + v.val) = (representatives v).val at source
    rw [model57] at source
    have chosen := observed.replacement (representatives v)
    change model.nm (model.nr 89 + (representatives v).val) = (nextRep (representatives v)).val at chosen
    rw [model89] at chosen
    rw [ready.memory, remappedAugmentationMemory, if_pos touched]
    change model.nm (s.nr 89 + model.nm (s.nr 57 + v.val)) = _
    rw [source, chosen]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentPreRebaseSemantics

/-! matching/MatchingAugmentRebaseJobs.lean -/
section RppSource_MatchingAugmentRebaseJobs
namespace VehicleRoutingSurvey.Routing







structure AugmentationRebaseEncoding {k : ℕ} (s : ArithmeticState) (model : AugmentationRebaseModel k) : Prop where
  nodes : ∀ v : Fin k, s.nm (s.nr 74 + v.val) = model.nodes v
  count : s.nr 82 = model.jobs.length
  jobs : ∀ i, ∀ within : i < model.jobs.length,
    augmentationRebaseJobAt s i = (model.jobs[i].1, model.jobs[i].2.val)

theorem rebaseAugmentationEndpoint_registry {k : ℕ} {s : ArithmeticState} {model : AugmentationRebaseModel k}
    {old port : Fin k} (layout : AugmentationInstallLayout k s)
    (original : s.nm (s.nr 57 + port.val) = old.val) (before : AugmentationRebaseEncoding s model) :
    AugmentationRebaseEncoding (rebaseAugmentationEndpoint s port.val) (model.move old port) := by
  let t := rebaseAugmentationEndpoint s port.val
  have moved := rebaseAugmentationEndpoint_projection layout original
  constructor
  · intro v
    change t.nm (t.nr 74 + v.val) = _
    rw [rebaseAugmentationEndpoint_keeps _ 74 (by decide), moved.nodes v, before.nodes old, before.nodes v]
    by_cases selected : v = port
    · simp [AugmentationRebaseModel.move, selected]
    · simp [AugmentationRebaseModel.move, selected, Function.update_of_ne selected, Function.update_apply]
  · change t.nr 82 = _
    rw [moved.jobs, before.nodes, before.count]
    by_cases vacant : model.nodes old = 0 <;> simp [AugmentationRebaseModel.move, vacant]
  · intro i within
    by_cases vacant : model.nodes old = 0
    · have unchanged : (model.move old port).jobs = model.jobs := by simp [AugmentationRebaseModel.move, vacant]
      have valid : i < model.jobs.length := by simpa only [unchanged] using within
      have slot : (model.move old port).jobs[i]'within = model.jobs[i]'valid := getElem_congr_coll unchanged
      rw [slot]
      exact (moved.priorJobs i (by rwa [before.count])).trans (before.jobs i valid)
    · have extended : (model.move old port).jobs = model.jobs ++ [(model.nodes old, port)] := by
        simp [AugmentationRebaseModel.move, vacant]
      have valid : i < (model.jobs ++ [(model.nodes old, port)]).length := by simpa only [extended] using within
      have slot : (model.move old port).jobs[i]'within = (model.jobs ++ [(model.nodes old, port)])[i]'valid :=
        getElem_congr_coll extended
      rw [slot]
      by_cases earlier : i < model.jobs.length
      · rw [List.getElem_append_left earlier]
        exact (moved.priorJobs i (by rwa [before.count])).trans (before.jobs i earlier)
      · have last : i = model.jobs.length := by simp only [List.length_append, List.length_singleton] at valid; omega
        have pushed : s.nm (s.nr 74 + old.val) ≠ 0 := by rwa [before.nodes]
        have atEnd := moved.lastJob pushed
        rw [before.count, before.nodes] at atEnd
        subst i
        rw [List.getElem_append_right (Nat.le_refl _)]
        simpa using atEnd

theorem installAugmentationCrossingState_registry {k : ℕ} {s : ArithmeticState} {model : AugmentationRebaseModel k}
    (layout : AugmentationInstallLayout k s) (before : AugmentationRebaseEncoding s model)
    (original : Fin k → Fin k) (readOriginal : ∀ v : Fin k, s.nm (s.nr 57 + v.val) = (original v).val)
    (ports : Fin k × Fin k) :
    let t := installAugmentationCrossingState s (ports.1.val, ports.2.val)
    AugmentationInstallLayout k t ∧
      (∀ v : Fin k, t.nm (t.nr 57 + v.val) = (original v).val) ∧
      AugmentationRebaseEncoding t (model.crossing original ports) := by
  intro t
  let m := {s with nm := installedAugmentationMateMemory s (ports.1.val, ports.2.val)}
  let l := rebaseAugmentationEndpoint m ports.1.val
  have mLayout : AugmentationInstallLayout k m := layout.transport (fun _ _ => rfl)
  have lLayout : AugmentationInstallLayout k l := mLayout.transport fun r safe =>
    rebaseAugmentationEndpoint_keeps _ r (by intro eq; simp [eq] at safe)
  have tLayout : AugmentationInstallLayout k t := lLayout.transport fun r safe =>
    rebaseAugmentationEndpoint_keeps _ r (by intro eq; simp [eq] at safe)
  have mateBase := layout.matesBeforeMap
  have repBase := layout.mapBeforeNodes
  have nodeBase := layout.nodesBeforePairs
  have pairBase := layout.pairsBeforeRepresentativeWork
  have workBase := layout.representativeWorkBeforeJobs
  have mateWriteSafe (address : ℕ) (past : s.nr 50 + k ≤ address) : m.nm address = s.nm address :=
    installedAugmentationMateMemory_keeps ports.1.isLt ports.2.isLt (.inr past)
  have mRegistry : AugmentationRebaseEncoding m model := by
    refine ⟨?_, before.count, ?_⟩
    · intro v
      change m.nm (s.nr 74 + v.val) = _
      rw [mateWriteSafe _ (by omega)]
      exact before.nodes v
    · intro i within
      let address := matchingRebaseJobAddress s i
      have start : s.nr 81 ≤ address := by simp [address, matchingRebaseJobAddress]
      change (m.nm address, m.nm (address + 1)) = _
      rw [mateWriteSafe address (by omega), mateWriteSafe (address + 1) (by omega)]
      exact before.jobs i within
  have mOriginal (v : Fin k) : m.nm (m.nr 57 + v.val) = (original v).val := by
    change m.nm (s.nr 57 + v.val) = _
    rw [mateWriteSafe _ (by omega)]
    exact readOriginal v
  have lm := rebaseAugmentationEndpoint_projection mLayout (mOriginal ports.1)
  have lOriginal (v : Fin k) : l.nm (l.nr 57 + v.val) = (original v).val := by
    rw [rebaseAugmentationEndpoint_keeps _ 57 (by decide), lm.originalMap]
    exact mOriginal v
  have rm := rebaseAugmentationEndpoint_projection lLayout (lOriginal ports.2)
  refine ⟨tLayout, ?_, rebaseAugmentationEndpoint_registry lLayout (lOriginal ports.2)
    (rebaseAugmentationEndpoint_registry mLayout (mOriginal ports.1) mRegistry)⟩
  intro v
  change (rebaseAugmentationEndpoint l ports.2.val).nm ((rebaseAugmentationEndpoint l ports.2.val).nr 57 + v.val) = _
  rw [rebaseAugmentationEndpoint_keeps _ 57 (by decide), rm.originalMap v]
  exact lOriginal v

/-- The models of the top-node table and queued requests are exact through
the entire crossing install. The work stack contains only nontrivial nodes. -/
theorem installAugmentationCrossingRows_registry {k : ℕ} {s : ArithmeticState} {model : AugmentationRebaseModel k}
    (layout : AugmentationInstallLayout k s) (before : AugmentationRebaseEncoding s model)
    (original : Fin k → Fin k) (readOriginal : ∀ v : Fin k, s.nm (s.nr 57 + v.val) = (original v).val)
    (rows : List (Fin k × Fin k)) :
    AugmentationRebaseEncoding (installAugmentationCrossingRows s rows)
      (rows.foldl (AugmentationRebaseModel.crossing original) model) := by
  induction rows generalizing s model with
  | nil => exact before
  | cons ports rest ih =>
    obtain ⟨nextLayout, nextOriginal, nextRegistry⟩ :=
      installAugmentationCrossingState_registry layout before original readOriginal ports
    exact ih nextLayout nextRegistry nextOriginal

end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentRebaseJobs

/-! matching/MatchingAugmentRebaseInput.lean -/
section RppSource_MatchingAugmentRebaseInput
namespace VehicleRoutingSurvey.Routing

/-- The recursive rebasing loop receives the exact moved registry entries
and the stack of requested exposed vertices. The original-vertex remap
has no effect on these two tables. -/
theorem AugmentationPreRebaseReady.queuedRegistry {k : ℕ} {s t : ArithmeticState}
    {rows : List (Fin k × Fin k)} (ready : AugmentationPreRebaseReady rows s t)
    (layout : AugmentationInstallLayout k (augmentationCrossingSeed s k))
    (representatives : Fin k → Fin k) (nodes : Fin k → ℕ)
    (original : ∀ v : Fin k, s.nm (s.nr 57 + v.val) = (representatives v).val)
    (initialNodes : ∀ v : Fin k, s.nm (s.nr 74 + v.val) = nodes v) :
    AugmentationRebaseEncoding t
      (rows.foldl (AugmentationRebaseModel.crossing representatives) ⟨nodes, []⟩) := by
  let seed := augmentationCrossingSeed s k
  let model := installAugmentationCrossingRows seed rows
  let registry := rows.foldl (AugmentationRebaseModel.crossing representatives) (⟨nodes, []⟩ : AugmentationRebaseModel k)
  change AugmentationInstallLayout k seed at layout
  have seed57 : seed.nr 57 = s.nr 57 := by simp [seed, augmentationCrossingSeed]
  have seed74 : seed.nr 74 = s.nr 74 := by simp [seed, augmentationCrossingSeed]
  have seed86 : seed.nr 86 = s.nr 86 := by simp [seed, augmentationCrossingSeed]
  have seed89 : seed.nr 89 = s.nr 89 := by simp [seed, augmentationCrossingSeed]
  have seed81 : seed.nr 81 = s.nr 80 + 3 * k := by simp [seed, augmentationCrossingSeed]
  have mapThenNode : s.nr 57 + k ≤ s.nr 74 := by simpa only [seed57, seed74] using layout.mapBeforeNodes
  have nodeThenPair : s.nr 74 + k ≤ s.nr 86 := by simpa only [seed74, seed86] using layout.nodesBeforePairs
  have pairThenWork : s.nr 86 + k ≤ s.nr 89 := by simpa only [seed86, seed89] using layout.pairsBeforeRepresentativeWork
  have workThenStack : s.nr 89 + k ≤ s.nr 80 + 3 * k := by
    simpa only [seed89, seed81] using layout.representativeWorkBeforeJobs
  have seeded : AugmentationRebaseEncoding seed (⟨nodes, []⟩ : AugmentationRebaseModel k) := by
    refine ⟨?_, by simp [seed, augmentationCrossingSeed], ?_⟩
    · intro v
      have finite := v.isLt
      have prior : s.nr 74 + v.val < s.nr 89 := by omega
      rw [seed74]
      simpa [seed, augmentationCrossingSeed, not_le.mpr prior] using initialNodes v
    · intro _ impossible
      simp at impossible
  have originalSeed (v : Fin k) : seed.nm (seed.nr 57 + v.val) = (representatives v).val := by
    have finite := v.isLt
    have prior : s.nr 57 + v.val < s.nr 89 := by omega
    rw [seed57]
    simpa [seed, augmentationCrossingSeed, not_le.mpr prior] using original v
  have observed : AugmentationRebaseEncoding model registry :=
    installAugmentationCrossingRows_registry layout seeded representatives originalSeed rows
  have model74 : model.nr 74 = s.nr 74 :=
    (installAugmentationCrossingRows_keeps rows 74 (by decide)).trans seed74
  have model81 : model.nr 81 = s.nr 80 + 3 * k :=
    (installAugmentationCrossingRows_keeps rows 81 (by decide)).trans seed81
  have untouched (address : ℕ) (later : s.nr 57 + k ≤ address) : t.nm address = model.nm address := by
    rw [ready.memory, remappedAugmentationMemory, if_neg (by omega)]
  refine ⟨?_, ready.jobs.trans observed.count, ?_⟩
  · intro v
    rw [ready.fixed 74 (by decide), untouched (s.nr 74 + v.val) (by omega)]
    exact (show model.nm (s.nr 74 + v.val) = registry.nodes v by rw [← model74]; exact observed.nodes v)
  · intro i within
    let address := s.nr 80 + 3 * k + 2 * i
    have later : s.nr 57 + k ≤ address := by dsimp [address]; omega
    have same : augmentationRebaseJobAt t i = augmentationRebaseJobAt model i := by
      simp only [augmentationRebaseJobAt, matchingRebaseJobAddress, ready.stackBase, model81]
      change (t.nm address, t.nm (address + 1)) = (model.nm address, model.nm (address + 1))
      rw [untouched address later, untouched (address + 1) (by omega)]
    exact same.trans (observed.jobs i within)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentRebaseInput

/-! matching/MatchingAugmentPathProjection.lean -/
section RppSource_MatchingAugmentPathProjection
namespace VehicleRoutingSurvey.Routing

theorem alternatingEdges_length_for_index {α : Type*} (xs : List α) :
    (alternatingEdges xs).length = xs.length / 2 := by
  induction xs using List.twoStepInduction with
  | nil => simp [alternatingEdges]
  | singleton _ => simp [alternatingEdges]
  | cons_cons a b rest ih _ =>
    simp only [alternatingEdges, List.length_cons, ih]
    omega

theorem alternatingEdges_index {α : Type*} (xs : List α) (i : ℕ)
    (inside : i < (alternatingEdges xs).length) :
    (alternatingEdges xs)[i] =
      s(xs[2 * i]'(by have bound := alternatingEdges_length_for_index xs; omega),
        xs[2 * i + 1]'(by have bound := alternatingEdges_length_for_index xs; omega)) := by
  induction xs using List.twoStepInduction generalizing i with
  | nil => simp [alternatingEdges] at inside
  | singleton a => simp [alternatingEdges] at inside
  | cons_cons a b rest ih _ =>
    cases i with
    | zero => rfl
    | succ i =>
      have later : i < (alternatingEdges rest).length := by
        simpa only [alternatingEdges, List.length_cons, Nat.succ_lt_succ_iff] using inside
      have atSlot := ih i later
      have firstIndex : 2 * (i + 1) = 2 * i + 1 + 1 := by omega
      simp only [firstIndex]
      exact atSlot

private theorem augmentationLeg_topEdges {k : ℕ} {forest : AlternatingForestState (Fin k)}
    (forward : Bool) (trail : List (Fin k)) (odd : trail.length % 2 = 1)
    (chain : trail.IsChain fun a b => (forest.role a).parent = some b)
    (witness : Fin k → Fin k × Fin k) (rep : Fin k → Fin k)
    (sound : ∀ child parent : Fin k, (forest.role child).parent = some parent →
      (rep (witness child).1, rep (witness child).2) = (parent, child)) :
    ((augmentationWitnessChildren forward trail).map fun v =>
      orientAugmentationWitness forward (witness v)).map (fun p => s(rep p.1, rep p.2)) =
    alternatingEdges (if forward then trail.tail else trail.tail.reverse) := by
  apply List.ext_getElem
  · cases forward <;>
      simp [alternatingEdges_length_for_index] <;> omega
  · intro i enters matched
    have selected : i < (augmentationWitnessChildren forward trail).length :=
      by simpa only [List.length_map] using enters
    have fits : i < trail.length / 2 := by simpa using selected
    have mapped := augmentationWitness_matches_parent forward trail odd chain witness rep sound i selected
    let slot := augmentationTraceIndex forward (augmentationWitnessStart forward trail.length) i
    let child := trail[slot]'(augmentationWitnessIndex_inBounds forward fits)
    let parent := trail[slot + 1]'(augmentationWitnessIndex_parent_inBounds forward odd fits)
    have code := augmentationWitnessChildren_get forward trail i selected
    have actual :
        (rep (orientAugmentationWitness forward (witness child)).1,
          rep (orientAugmentationWitness forward (witness child)).2) =
        orientAugmentationWitness forward (parent, child) := by
      dsimp only at mapped
      rw [code] at mapped
      exact mapped
    rw [alternatingEdges_index _ _ matched]
    simp only [List.getElem_map, code]
    change s(rep (orientAugmentationWitness forward (witness child)).1,
      rep (orientAugmentationWitness forward (witness child)).2) = _
    have edges := congrArg (fun p : Fin k × Fin k => s(p.1, p.2)) actual
    cases forward
    · simp only [Bool.false_eq_true, if_false, List.getElem_reverse, List.getElem_tail]
      have first : (trail.tail.length - 1 - (2 * i)) + 1 = slot + 1 := by
        simp [slot, augmentationTraceIndex, augmentationWitnessStart]
        omega
      have second : (trail.tail.length - 1 - (2 * i + 1)) + 1 = slot := by
        simp [slot, augmentationTraceIndex, augmentationWitnessStart]
        omega
      simp only [getElem_congr_idx first, getElem_congr_idx second]
      exact edges
    · simp only [if_true, List.getElem_tail]
      have first : 2 * i + 1 = slot := by
        simp [slot, augmentationTraceIndex, augmentationWitnessStart] <;> omega
      have second : (2 * i + 1) + 1 = slot + 1 := congrArg (· + 1) first
      simp only [getElem_congr_idx first, getElem_congr_idx second]
      exact edges

/-- Project the original crossing records onto their top representatives.
The ordered projection is precisely the new edge list of the augmenting path. -/
theorem forestAugmentationCrossings_topEdges {k : ℕ} {forest : AlternatingForestState (Fin k)}
    {left right : List (Fin k)} {u v : Fin k}
    (lHead : left.head? = some u) (rHead : right.head? = some v)
    (lOdd : left.length % 2 = 1) (rOdd : right.length % 2 = 1)
    (lChain : left.IsChain fun a b => (forest.role a).parent = some b)
    (rChain : right.IsChain fun a b => (forest.role a).parent = some b)
    (witness : Fin k → Fin k × Fin k) (rep : Fin k → Fin k) (trigger : Fin k × Fin k)
    (sound : ∀ child parent : Fin k, (forest.role child).parent = some parent →
      (rep (witness child).1, rep (witness child).2) = (parent, child))
    (triggerAt : (rep trigger.1, rep trigger.2) = (u, v)) :
    (forestAugmentationCrossings witness trigger left right).map (fun ports => s(rep ports.1, rep ports.2)) =
      alternatingEdges (left.reverse ++ right) := by
  obtain ⟨lTail, leftForm⟩ := List.head?_eq_some_iff.mp lHead
  obtain ⟨rTail, rightForm⟩ := List.head?_eq_some_iff.mp rHead
  have shape : left.reverse ++ right = left.tail.reverse ++ u :: v :: right.tail := by
    simp [leftForm, rightForm, List.reverse_cons, List.append_assoc]
  have even : left.tail.reverse.length % 2 = 0 := by
    simp only [List.length_reverse, List.length_tail]
    omega
  have lProjected := augmentationLeg_topEdges false left lOdd lChain witness rep sound
  have rProjected := augmentationLeg_topEdges true right rOdd rChain witness rep sound
  have atLeft : rep trigger.1 = u := congrArg Prod.fst triggerAt
  have atRight : rep trigger.2 = v := congrArg Prod.snd triggerAt
  rw [shape, alternatingEdges_append_even _ _ even]
  simp only [forestAugmentationCrossings, List.map_append, List.map_cons, List.map_nil]
  change ((((augmentationWitnessChildren false left).map (fun x =>
      orientAugmentationWitness false (witness x))).map (fun ports => s(rep ports.1, rep ports.2))) ++
      [s(rep trigger.1, rep trigger.2)]) ++
      (((augmentationWitnessChildren true right).map (fun x =>
        orientAugmentationWitness true (witness x))).map (fun ports => s(rep ports.1, rep ports.2))) = _
  rw [lProjected, rProjected, atLeft, atRight]
  simp only [Bool.false_eq_true, if_false, if_true, alternatingEdges, List.append_assoc, List.singleton_append]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentPathProjection

/-! matching/MatchingAugmentJobUniqueness.lean -/
section RppSource_MatchingAugmentJobUniqueness
namespace VehicleRoutingSurvey.Routing



def expectedAugmentationJobs {k : ℕ} (original : Fin k → Fin k) (nodes : Fin k → ℕ)
    (ports : List (Fin k)) : List (ℕ × Fin k) :=
  ports.filterMap fun port =>
    if nodes (original port) = 0 then none else some (nodes (original port), port)

private theorem expectedAugmentationJobs_congr {k : ℕ} (original : Fin k → Fin k) (a b : Fin k → ℕ)
    (ports : List (Fin k)) (agree : ∀ p ∈ ports, a (original p) = b (original p)) :
    expectedAugmentationJobs original a ports = expectedAugmentationJobs original b ports := by
  induction ports with
  | nil => rfl
  | cons p tail ih =>
    have head := agree p (by simp)
    have rest := ih (fun q h => agree q (List.mem_cons_of_mem _ h))
    simp only [expectedAugmentationJobs, List.filterMap_cons, head] at rest ⊢
    rw [rest]

private theorem AugmentationRebaseModel.move_jobs {k : ℕ} (original : Fin k → Fin k)
    (idempotent : ∀ v, original (original v) = original v) (ports : List (Fin k))
    (distinct : (ports.map original).Nodup) (model : AugmentationRebaseModel k) :
    (ports.foldl (fun old port => old.move (original port) port) model).jobs =
      model.jobs ++ expectedAugmentationJobs original model.nodes ports := by
  induction ports generalizing model with
  | nil => simp [expectedAugmentationJobs]
  | cons p tail ih =>
    let next := model.move (original p) p
    have oldFresh := (List.nodup_cons.mp distinct).1
    have tailDistinct := (List.nodup_cons.mp distinct).2
    have unchanged (q : Fin k) (present : q ∈ tail) : next.nodes (original q) = model.nodes (original q) := by
      have notOld : original q ≠ original p := fun equal => oldFresh (List.mem_map.mpr ⟨q, present, equal⟩)
      have notPort : original q ≠ p := by
        intro equal
        exact notOld ((idempotent q).symm.trans (congrArg original equal))
      simp [next, AugmentationRebaseModel.move, Function.update_of_ne notOld, Function.update_of_ne notPort]
    have tailJobs := expectedAugmentationJobs_congr original next.nodes model.nodes tail unchanged
    change (tail.foldl (fun old port => old.move (original port) port) next).jobs = _
    rw [ih tailDistinct next, tailJobs]
    by_cases vacant : model.nodes (original p) = 0 <;>
      simp [expectedAugmentationJobs, next, AugmentationRebaseModel.move, vacant, List.append_assoc]

private theorem AugmentationRebaseModel.crossing_eq_portFold {k : ℕ} (original : Fin k → Fin k)
    (rows : List (Fin k × Fin k)) (model : AugmentationRebaseModel k) :
    rows.foldl (AugmentationRebaseModel.crossing original) model =
      (selectedAugmentationPorts rows).foldl (fun old port => old.move (original port) port) model := by
  induction rows generalizing model with
  | nil => rfl
  | cons edge rest ih =>
    simp only [selectedAugmentationPorts, List.flatMap_cons, List.foldl_cons, List.foldl_append, List.foldl_nil,
      AugmentationRebaseModel.crossing]
    exact ih _

/-- Distinct top-level classes are moved independently. In that case every
rebasing request names the original registered node and the newly matched port. -/
theorem AugmentationRebaseModel.crossing_jobs {k : ℕ} (original : Fin k → Fin k)
    (idempotent : ∀ v, original (original v) = original v) (rows : List (Fin k × Fin k))
    (distinct : ((selectedAugmentationPorts rows).map original).Nodup) (model : AugmentationRebaseModel k) :
    (rows.foldl (AugmentationRebaseModel.crossing original) model).jobs =
      model.jobs ++ expectedAugmentationJobs original model.nodes (selectedAugmentationPorts rows) := by
  rw [AugmentationRebaseModel.crossing_eq_portFold]
  exact AugmentationRebaseModel.move_jobs original idempotent _ distinct model



theorem selectedAugmentationPorts_mem {k : ℕ} (rows : List (Fin k × Fin k))
    (original : Fin k → Fin k) {v : Fin k}
    (present : v ∈ (selectedAugmentationPorts rows).map original) :
    ∃ e ∈ rows.map (fun p => s(original p.1, original p.2)), v ∈ e := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp present
  obtain ⟨edge, belongs, endpoint⟩ := List.mem_flatMap.mp hp
  refine ⟨s(original edge.1, original edge.2), List.mem_map.mpr ⟨edge, belongs, rfl⟩, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at endpoint
  rcases endpoint with rfl | rfl
  · exact Sym2.mem_mk_left _ _
  · exact Sym2.mem_mk_right _ _

private theorem selectedAugmentationPorts_matching_nodup {k : ℕ} (rows : List (Fin k × Fin k))
    (original : Fin k → Fin k) {covered : Finset (Fin k)} {M : Finset (Sym2 (Fin k))}
    (matched : SupplyChainTheory.IsPerfectMatchingOn covered M)
    (inMatching : (rows.map (fun p => s(original p.1, original p.2))).toFinset ⊆ M)
    (different : (rows.map (fun p => s(original p.1, original p.2))).Nodup) :
    ((selectedAugmentationPorts rows).map original).Nodup := by
  induction rows with
  | nil => simp [selectedAugmentationPorts]
  | cons head tail ih =>
    let edge : Sym2 (Fin k) := s(original head.1, original head.2)
    have contains : edge ∈ M := inMatching (by simp [edge])
    have disjoint := List.nodup_cons.mp different
    have endpointDifferent : original head.1 ≠ original head.2 := by
      intro same
      exact (matched.1 edge contains).1 (Sym2.mk_isDiag_iff.mpr same)
    have tailMatching : (tail.map (fun p => s(original p.1, original p.2))).toFinset ⊆ M := by
      intro e member
      exact inMatching (List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp member)))
    have tailDistinct := ih tailMatching disjoint.2
    have noOverlap (v : Fin k) (endAt : v ∈ edge) : v ∉ (selectedAugmentationPorts tail).map original := by
      intro repeated
      obtain ⟨later, inTail, atLater⟩ := selectedAugmentationPorts_mem tail original repeated
      have included := tailMatching (List.mem_toFinset.mpr inTail)
      have coveredHere := (matched.1 edge contains).2 v endAt
      obtain ⟨owner, _, unique⟩ := matched.2 v coveredHere
      have equal : later = edge := (unique later ⟨included, atLater⟩).trans (unique edge ⟨contains, endAt⟩).symm
      rw [equal] at inTail
      exact disjoint.1 inTail
    change (original head.1 :: original head.2 :: (selectedAugmentationPorts tail).map original).Nodup
    exact List.nodup_cons.mpr ⟨by
      simp only [List.mem_cons, not_or]
      exact ⟨endpointDifferent, noOverlap _ (Sym2.mem_mk_left _ _)⟩,
      List.nodup_cons.mpr ⟨noOverlap _ (Sym2.mem_mk_right _ _), tailDistinct⟩⟩

/-- Two distinct-root traces give at most one selected port per top-level
representative. This is the disjointness needed by the recursive job stack. -/
theorem forestAugmentationCrossings_distinct_classes {k : ℕ} {forest : AlternatingForestState (Fin k)}
    {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop} (valid : forest.valid mate tight)
    {a b : Fin k} {aParent bParent : Option (Fin k)} (aOuter : forest.role a = .outer aParent)
    (bOuter : forest.role b = .outer bParent) (separate : forest.commonAncestor a b = none)
    (witness : Fin k → Fin k × Fin k) (original : Fin k → Fin k) (trigger : Fin k × Fin k)
    (sound : ∀ child parent : Fin k, (forest.role child).parent = some parent →
      (original (witness child).1, original (witness child).2) = (parent, child))
    (triggerAt : (original trigger.1, original trigger.2) = (a, b)) :
    let rows := forestAugmentationCrossings witness trigger (forest.traceToRoot a) (forest.traceToRoot b)
    ((selectedAugmentationPorts rows).map original).Nodup := by
  intro rows
  let left := forest.traceToRoot a
  let right := forest.traceToRoot b
  let path := left.reverse ++ right
  obtain ⟨aHead, aNodup, _, aChain, _⟩ := AlternatingForestState.traceToRoot_spec valid (x := a) (by simp [aOuter])
  obtain ⟨bHead, bNodup, _, bChain, _⟩ := AlternatingForestState.traceToRoot_spec valid (x := b) (by simp [bOuter])
  have aOdd := AlternatingForestState.outerTrace_length_odd valid aOuter
  have bOdd := AlternatingForestState.outerTrace_length_odd valid bOuter
  have pathEven : path.length % 2 = 0 := by
    change (left.reverse ++ right).length % 2 = 0
    simp only [List.length_append, List.length_reverse]
    change ((forest.traceToRoot a).length + (forest.traceToRoot b).length) % 2 = 0
    omega
  have pathDistinct : path.Nodup := by
    refine List.nodup_append.mpr ⟨List.nodup_reverse.mpr aNodup, bNodup, ?_⟩
    intro x leftOfPath y rightOfPath equal
    exact firstSharedAncestor_eq_none_iff.mp separate y rightOfPath (equal ▸ List.mem_reverse.mp leftOfPath)
  have projected : (rows.map (fun ports => s(original ports.1, original ports.2))) = alternatingEdges path :=
    forestAugmentationCrossings_topEdges aHead bHead aOdd bOdd
      (aChain.imp fun _ _ link => link.1) (bChain.imp fun _ _ link => link.1)
      witness original trigger sound triggerAt
  obtain ⟨pairsDistinct, matching⟩ := alternatingEdges_perfect path pathDistinct pathEven
  exact selectedAugmentationPorts_matching_nodup rows original matching
    (by rw [projected]) (by rwa [projected])

end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentJobUniqueness

/-! matching/MatchingAugmentComplete.lean -/
section RppSource_MatchingAugmentComplete
namespace VehicleRoutingSurvey.Routing



set_option maxRecDepth 16384 in
theorem prepareMatchingAugmentationBlock_preserves {s t : ArithmeticState} {ticks : ℕ}
    (ran : BlockRuns prepareMatchingAugmentationBlock ticks s t) :
    ∀ r, r ∉ [0, 3, 4, 5, 6, 7, 10, 11, 12, 14, 15, 16, 17, 18, 19, 87] → t.nr r = s.nr r := by
  intro r safe
  rw [← ran.run]
  exact arithmeticRun_keeps_from_destination_list _ (by decide) safe s ticks





end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentComplete

/-! matching/MatchingAugmentProtectedStorage.lean -/
section RppSource_MatchingAugmentProtectedStorage
namespace VehicleRoutingSurvey.Routing

set_option maxHeartbeats 1600000 in
/-- Both header tables and every allocated cycle interval survive the
crossing emitter, dual sweep, and preparation of the rebase stack. -/
theorem matchingAugmentPrefixRegistry {k ticks emitSteps : ℕ} {caller s emitted u t : ArithmeticState}
    {rows : List (Fin k × Fin k)}
    (storage : MatchingStageStorage k caller s) (order : MatchingCycleRecordOrder s)
    (capacity : ∀ n < s.nr 76, n < matchingBlossomCapacity k)
    (emit : BlockRuns writeAugmentationCrossingsBlock emitSteps s emitted) (emittedLive : emitted.halted = false)
    (emittedRows : AugmentationCrossingsReady rows s emitted) (emitBound : emitSteps ≤ 17*k+21)
    (one : s.nr 9 = 1) (repBounds : ∀ i < k, s.nm (s.nr 57+i) < k)
    (prepared : BlockRuns prepareMatchingAugmentationBlock ticks s u)
    (ready : AugmentationPreRebaseReady rows {u with pc := 0} t) :
    MatchingAugmentArchiveFrame s t ∧
      (∀ a < s.nr 86, u.nm a = s.nm a) ∧
      (∀ r ∈ matchingFixedStorageRegisters, u.nr r = s.nr r) ∧
      t.nr 81 = s.nr 80 + 3*k := by
  obtain ⟨warm,_,nodes,_,starts,lengths,traces,right,marks,witness,records,promotion,mask,map,stack,_⟩ := storage
  have mates := warm.matesBefore
  have role := warm.representativesAfter
  have reps := warm.candidatesAfter
  have pairs := warm.pairsAfter
  have size := warm.size
  obtain ⟨out,_,_,observed,_,nm,_⟩ := prepareMatchingAugmentationBlock_correct emit emittedLive emittedRows emitBound size
    one (by omega) (by omega) (by omega) repBounds
  have eq := (observed.same_exit prepared).2
  subst out
  have untouched (a : ℕ) (away : a < s.nr 86 ∨ s.nr 86 + 2*rows.length ≤ a) : u.nm a = s.nm a :=
    (congrFun nm a).trans (emittedRows.natural a away)
  have fixed (r : ℕ) (safe : r ∉ ([0,3,4,5,6,7,10,11,12,14,15,16,17,18,19,87] : List ℕ) := by decide) :=
    prepareMatchingAugmentationBlock_preserves prepared r safe
  have same (r : ℕ) (a : r ∉ ([0,6,9,12,13,14,15,22,26,44,81,82] : List ℕ) := by decide)
      (b : r ∉ ([0,3,4,5,6,7,10,11,12,14,15,16,17,18,19,87] : List ℕ) := by decide) : t.nr r = s.nr r :=
    (ready.fixed r a).trans (fixed r b)
  have archiveBytes (a : ℕ) (outside : (s.nr 77 ≤ a ∧ a < s.nr 83) ∨ s.nr 80+5*k ≤ a) : t.nm a = s.nm a := by
    have room := emittedRows.capacity
    apply (ready.untouched a ?_).trans (untouched _ (by rcases outside with h | h <;> omega))
    simp only [AugmentationPreRebaseUnwritten,AugmentationInstallUnwritten,augmentationCrossingSeed,
      Function.update_self,Function.update_of_ne (by decide : 81 ≠ 82),
      Function.update_of_ne (by decide : 50 ≠ 82),Function.update_of_ne (by decide : 50 ≠ 81),
      Function.update_of_ne (by decide : 74 ≠ 82),Function.update_of_ne (by decide : 74 ≠ 81),
      Function.update_of_ne (by decide : 89 ≠ 82),Function.update_of_ne (by decide : 89 ≠ 81),
      fixed 50,fixed 74,fixed 89,fixed 57,fixed 80]
    rcases outside with h | h <;> omega
  refine ⟨⟨?_,?_,?_⟩,fun a h => untouched a (.inl h),?_,ready.stackBase.trans (congrArg (· + 3*k) (fixed 80))⟩
  · intro r hr
    exact same r (by simp at hr ⊢; omega) (by simp at hr ⊢; omega)
  · intro n lo hi
    have small := capacity n hi
    exact ⟨archiveBytes _ (.inl ⟨by omega,by omega⟩), archiveBytes _ (.inl ⟨by omega,by omega⟩)⟩
  · intro n lo hi a inside
    have low := (order.bounded n lo hi).1.trans inside.1
    exact archiveBytes _ (.inr (by simpa [matchingRebaseScratchEnd,size] using low))
  · intro r hr
    exact fixed r (by simp [matchingFixedStorageRegisters] at hr; simp; omega)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentProtectedStorage

/-! matching/MatchingAugmentCutPort.lean -/
section RppSource_MatchingAugmentCutPort
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



theorem matchingCutPort_of_inner {k : ℕ} {cost : Fin k → Fin k → ℝ} (next : CompactMatchingPrimalDual k cost)
    {B : Finset (Fin k)} {p : Fin k} (inB : p ∈ B) {inner : Finset (Sym2 (Fin k))}
    (localMatching : IsPerfectMatchingOn (B.erase p) inner) (subset : inner ⊆ next.edges) :
    matchingCutPort next B p ∧ ∀ q, matchingCutPort next B q → q = p := by
  have noInside {v : Fin k} (edge : s(p,v) ∈ next.edges) (other : v ∈ B) : False := by
    have distinct : v ≠ p := fun h => (next.perfect.1 _ edge).1 (Sym2.mk_isDiag_iff.mpr h.symm)
    obtain ⟨e, he, _⟩ := localMatching.2 v (Finset.mem_erase.mpr ⟨distinct,other⟩)
    have same := (next.perfect.2 v ((next.perfect.1 _ edge).2 v (Sym2.mem_mk_right _ _))).unique
      ⟨subset he.1, he.2⟩ ⟨edge, Sym2.mem_mk_right _ _⟩
    have impossible := (localMatching.1 _ he.1).2 p (same.symm ▸ Sym2.mem_mk_left p v)
    exact (Finset.mem_erase.mp impossible).1 rfl
  constructor
  · refine ⟨inB, ?_⟩
    intro e used incident whole
    induction e using Sym2.inductionOn with
    | hf a b =>
      rcases Sym2.mem_iff.mp incident with eq | eq
      · subst a
        exact noInside used (whole b (Sym2.mem_mk_right _ _))
      · subst b
        exact noInside (Sym2.eq_swap ▸ used) (whole a (Sym2.mem_mk_left _ _))
  · intro q h
    by_contra ne
    obtain ⟨edge, he, _⟩ := localMatching.2 q (Finset.mem_erase.mpr ⟨ne,h.1⟩)
    exact h.2 edge (subset he.1) he.2 (fun v hv => (Finset.mem_erase.mp ((localMatching.1 _ he.1).2 v hv)).2)



theorem matchingAugmentNodePort_eq {k : ℕ} {cost : Fin k → Fin k → ℝ} (next : CompactMatchingPrimalDual k cost)
    {cuts : Finset (Finset (Fin k))} {node : Finset (Fin k) → ℕ} (inj : Set.InjOn node (cuts : Set (Finset (Fin k))))
    {B : Finset (Fin k)} (live : B ∈ cuts) {p : Fin k} (inB : p ∈ B) {inner : Finset (Sym2 (Fin k))}
    (localMatching : IsPerfectMatchingOn (B.erase p) inner) (subset : inner ⊆ next.edges) :
    matchingAugmentNodePort next cuts node (node B) = p.val := by
  classical
  obtain ⟨good, unique⟩ := matchingCutPort_of_inner next inB localMatching subset
  have existsPort : ∃ v : Fin k, ∃ D ∈ cuts, node D = node B ∧ matchingCutPort next D v := ⟨p,B,live,rfl,good⟩
  rw [matchingAugmentNodePort, dif_pos existsPort]
  obtain ⟨D, hd, same, property⟩ := existsPort.choose_spec
  exact congrArg Fin.val (unique _ (inj hd live same ▸ property))


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentCutPort

/-! matching/MatchingRebaseLivePorts.lean -/
section RppSource_MatchingRebaseLivePorts
namespace VehicleRoutingSurvey.Routing



noncomputable def MatchingLiveCycle.chooseLiftPorts {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    (e : MatchingLiveCycle state node B) (desired : Fin k) (belongs : desired ∈ B) : MatchingCycleLiftPorts e desired := by
  classical
  let vs := e.geometry.cycle
  have has : e.ports.owner desired ∈ vs := by
    apply List.mem_toFinset.mp
    rw [← e.geometry.ports]
    exact (e.ports.covered _ belongs).1
  let free : Fin vs.length := ⟨(List.mem_iff_getElem.mp has).choose, (List.mem_iff_getElem.mp has).choose_spec.1⟩
  have atFree : vs.get free = e.ports.owner desired := (List.mem_iff_getElem.mp has).choose_spec.2
  have nz := Nat.zero_lt_of_lt free.isLt
  let index (i : ℕ) (b : Bool) : Fin vs.length := ⟨matchingRebaseChildIndex vs.length free.val i b, Nat.mod_lt _ nz⟩
  let edge (i : ℕ) := e.geometry.edges (index i false)
  let select (i : ℕ) (b : Bool) := if b then (edge i).2 else (edge i).1
  let existsLabel := matchingRebaseChildPorts_exists free.isLt e.geometry.odd desired select
  let label := existsLabel.choose
  have freeLabel : label free.val = desired := existsLabel.choose_spec.1
  have pairLabel : ∀ i < (vs.length-1)/2, ∀ b, label (index i b).val = select i b := existsLabel.choose_spec.2
  let lookup (p : Fin k) := if h : ∃ i : Fin vs.length, vs.get i = p then label h.choose.val else desired
  have get (i : Fin vs.length) : lookup (vs.get i) = label i.val := by
    have found : ∃ j : Fin vs.length, vs.get j = vs.get i := ⟨i, rfl⟩
    rw [show lookup (vs.get i) = label found.choose.val by simp [lookup, found]]
    exact congrArg label ((List.Nodup.getElem_inj_iff e.geometry.distinct).mp found.choose_spec)
  refine ⟨free, lookup, (get free).trans freeLabel, ?_, ?_⟩
  · intro p listed
    have present : p ∈ vs := List.mem_toFinset.mp (e.geometry.ports ▸ listed)
    obtain ⟨j, hj, asRow⟩ := List.mem_iff_getElem.mp present
    let j' : Fin vs.length := ⟨j, hj⟩
    have row : vs.get j' = p := asRow
    rw [← row, get]
    by_cases base : j = free.val
    · have eq : j' = free := Fin.ext base
      rw [eq, freeLabel, atFree]
      exact (e.ports.covered _ belongs).2
    · obtain ⟨i, hi, b, labelAt⟩ := (matchingRebaseChildIndex_complete free.isLt e.geometry.odd).2.1 j hj base
      have eq : index i b = j' := Fin.ext labelAt
      rw [← eq, pairLabel i hi]
      cases b
      · exact e.geometry.source (index i false)
      · have succ : (((index i false).val + 1) % vs.length) = (index i true).val := by
          change (((free.val + (2*i+1)) % vs.length) + 1) % vs.length = (free.val + (2*i+2)) % vs.length
          rw [Nat.mod_add_mod]
          exact congrArg (· % vs.length) (by omega)
        have next : (⟨((index i false).val + 1) % vs.length, Nat.mod_lt _ nz⟩ : Fin vs.length) = index i true := Fin.ext succ
        exact next ▸ e.geometry.target (index i false)
  · intro i hi
    exact Prod.ext ((get (index i false)).trans (pairLabel i hi false))
      ((get (index i true)).trans (pairLabel i hi true))


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseLivePorts

/-! matching/MatchingRebaseCycleEdges.lean -/
section RppSource_MatchingRebaseCycleEdges
namespace VehicleRoutingSurvey.Routing

/-- The indexed pairs installed by the RAM scan are exactly the abstract
matching obtained by rotating the blossom cycle and removing its new base. -/
theorem rematchBlossomCycle_mem_iff_physicalPair {k : ℕ} (vertices : List (Fin k))
    {free : ℕ} (inside : free < vertices.length) (edge : Sym2 (Fin k)) :
    edge ∈ rematchBlossomCycle vertices free ↔
      ∃ i < (vertices.length - 1) / 2,
        let first := matchingRebaseChildIndex vertices.length free i false
        let second := matchingRebaseChildIndex vertices.length free i true
        edge = s(vertices[first]'(Nat.mod_lt _ (Nat.zero_lt_of_lt inside)),
          vertices[second]'(Nat.mod_lt _ (Nat.zero_lt_of_lt inside))) := by
  let pairs := alternatingEdges (vertices.rotate free).tail
  have length : pairs.length = (vertices.length - 1) / 2 := by
    simp only [pairs, alternatingEdges_length_for_index, List.length_tail, List.length_rotate]
  have row (i : ℕ) (hi : i < pairs.length) :
      pairs[i] = s(vertices[matchingRebaseChildIndex vertices.length free i false]'(Nat.mod_lt _ (Nat.zero_lt_of_lt inside)),
        vertices[matchingRebaseChildIndex vertices.length free i true]'(Nat.mod_lt _ (Nat.zero_lt_of_lt inside))) := by
    let remaining := (vertices.rotate free).tail
    have bound : i < remaining.length / 2 := by
      have fits : i < (alternatingEdges remaining).length := hi
      rwa [alternatingEdges_length_for_index] at fits
    have firstIn : 2 * i < remaining.length := by omega
    have secondIn : 2 * i + 1 < remaining.length := by omega
    have left : (2 * i + 1 + free) % vertices.length = matchingRebaseChildIndex vertices.length free i false := by
      change (2 * i + 1 + free) % vertices.length = (free + (2 * i + 1)) % vertices.length
      exact congrArg (· % vertices.length) (by omega)
    have right : (2 * i + 1 + 1 + free) % vertices.length = matchingRebaseChildIndex vertices.length free i true := by
      change (2 * i + 1 + 1 + free) % vertices.length = (free + (2 * i + 2)) % vertices.length
      exact congrArg (· % vertices.length) (by omega)
    have first : remaining[2 * i]'firstIn =
        vertices[matchingRebaseChildIndex vertices.length free i false]'(Nat.mod_lt _ (Nat.zero_lt_of_lt inside)) := by
      simp only [remaining, List.getElem_tail, List.getElem_rotate]
      exact getElem_congr_idx left
    have second : remaining[2 * i + 1]'secondIn =
        vertices[matchingRebaseChildIndex vertices.length free i true]'(Nat.mod_lt _ (Nat.zero_lt_of_lt inside)) := by
      simp only [remaining, List.getElem_tail, List.getElem_rotate]
      exact getElem_congr_idx right
    exact (alternatingEdges_index remaining i hi).trans (congrArg₂ (fun a b => s(a, b)) first second)
  change edge ∈ pairs.toFinset ↔ _
  rw [List.mem_toFinset]
  constructor
  · intro member
    obtain ⟨i, hi, atIndex⟩ := List.mem_iff_getElem.mp member
    exact ⟨i, length ▸ hi, atIndex.symm.trans (row i hi)⟩
  · rintro ⟨i, hi, equals⟩
    have atPairs : i < pairs.length := length.symm ▸ hi
    exact List.mem_iff_getElem.mpr ⟨i, atPairs, (row i atPairs).trans equals.symm⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseCycleEdges

/-! matching/BlossomMatchingLift.lean -/
section RppSource_BlossomMatchingLift
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

private theorem perfectMatching_biUnion {n : ℕ} {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (vertices : Index → Finset (Fin n)) (localMatching : Index → Finset (Sym2 (Fin n)))
    (disjoint : (indices : Set Index).PairwiseDisjoint vertices)
    (perfect : ∀ i ∈ indices, IsPerfectMatchingOn (vertices i) (localMatching i)) :
    IsPerfectMatchingOn (indices.biUnion vertices) (indices.biUnion localMatching) := by
  induction indices using Finset.induction_on with
  | empty => simp [IsPerfectMatchingOn]
  | @insert i rest absent ih =>
    rw [Finset.biUnion_insert, Finset.biUnion_insert]
    apply perfectMatching_union_disjoint (perfect i (Finset.mem_insert_self _ _))
    · exact ih (fun j hj k hk different => disjoint (Finset.mem_insert_of_mem hj)
        (Finset.mem_insert_of_mem hk) different) fun j hj => perfect j (Finset.mem_insert_of_mem hj)
    · apply Finset.disjoint_left.mpr
      intro v left right
      obtain ⟨j, hj, vJ⟩ := Finset.mem_biUnion.mp right
      have distinct : i ≠ j := fun eq => absent (eq.symm ▸ hj)
      exact Finset.disjoint_left.mp (disjoint (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj) distinct) left vJ



theorem liftMatchingAcrossBlocks_spec {n : ℕ} {Index : Type*} [DecidableEq Index]
    (groups active : Finset Index) (activeSub : active ⊆ groups) (vertices : Index → Finset (Fin n))
    (exposed : Index → Fin n) (internal : Index → Finset (Sym2 (Fin n))) (crossing : Finset (Sym2 (Fin n)))
    (disjoint : (groups : Set Index).PairwiseDisjoint vertices) (atPorts : ∀ i ∈ groups, exposed i ∈ vertices i)
    (inside : ∀ i ∈ groups, IsPerfectMatchingOn ((vertices i).erase (exposed i)) (internal i))
    (outside : IsPerfectMatchingOn (active.image exposed) crossing)
    (tight : Sym2 (Fin n) → Prop)
    (tightInside : ∀ i ∈ groups, ∀ e ∈ internal i, tight e) (tightOutside : ∀ e ∈ crossing, tight e) :
    let result := liftMatchingAcrossBlocks groups internal crossing
    IsPerfectMatchingOn (groups.biUnion (fun i => (vertices i).erase (exposed i)) ∪ active.image exposed) result ∧
      (∀ e ∈ result, tight e) ∧
      ∀ i ∈ groups, ∀ v ∈ vertices i, v ≠ exposed i → ∃ e ∈ result, v ∈ e ∧ ∀ w ∈ e, w ∈ vertices i := by
  have disjointInside : (groups : Set Index).PairwiseDisjoint (fun i => (vertices i).erase (exposed i)) := by
    intro i hi j hj ne
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact Finset.disjoint_left.mp (disjoint hi hj ne) (Finset.mem_erase.mp hv).2 (Finset.mem_erase.mp hw).2
  have insideDisjoint : Disjoint (groups.biUnion fun i => (vertices i).erase (exposed i)) (active.image exposed) := by
    apply Finset.disjoint_left.mpr
    intro v inInternal inPorts
    obtain ⟨i, hi, iv⟩ := Finset.mem_biUnion.mp inInternal
    obtain ⟨j, hj, equal⟩ := Finset.mem_image.mp inPorts
    obtain ⟨noPort, vInside⟩ := Finset.mem_erase.mp iv
    by_cases same : i = j
    · exact noPort (equal.symm.trans (congrArg exposed same.symm))
    · exact Finset.disjoint_left.mp (disjoint hi (activeSub hj) same) vInside
        (equal ▸ atPorts j (activeSub hj))
  refine ⟨perfectMatching_union_disjoint (perfectMatching_biUnion groups _ internal disjointInside inside)
    outside insideDisjoint, ?_, ?_⟩
  · intro e present
    change e ∈ groups.biUnion internal ∪ crossing at present
    rcases Finset.mem_union.mp present with localEdge | edge
    · obtain ⟨i, hi, hasEdge⟩ := Finset.mem_biUnion.mp localEdge
      exact tightInside i hi e hasEdge
    · exact tightOutside e edge
  · intro i hi v hv different
    obtain ⟨edge, covers, _⟩ := (inside i hi).2 v (Finset.mem_erase.mpr ⟨different, hv⟩)
    exact ⟨edge, Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, hi, covers.1⟩), covers.2,
      fun w hw => (Finset.mem_erase.mp (((inside i hi).1 edge covers.1).2 w hw)).2⟩

/-- If one child has no crossing mate, the lifted matching leaves precisely that child's
designated port uncovered. -/
theorem liftedBlossom_vertices {n : ℕ} {Index : Type*} [DecidableEq Index]
    {groups : Finset Index} {free : Index} (freeIn : free ∈ groups)
    (vertices : Index → Finset (Fin n)) (port : Index → Fin n)
    (disjoint : (groups : Set Index).PairwiseDisjoint vertices) (atPorts : ∀ i ∈ groups, port i ∈ vertices i) :
    groups.biUnion (fun i => (vertices i).erase (port i)) ∪ (groups.erase free).image port =
      (groups.biUnion vertices).erase (port free) := by
  have notFree {i : Index} (hi : i ∈ groups) (different : i ≠ free) {v : Fin n} (here : v ∈ vertices i) :
      v ≠ port free := fun eq => Finset.disjoint_left.mp (disjoint hi freeIn different) here
        (eq.symm ▸ atPorts free freeIn)
  ext v
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro (⟨i, hi, noPort, here⟩ | ⟨i, ⟨different, hi⟩, equal⟩)
    · by_cases same : i = free
      · exact ⟨same ▸ noPort, ⟨i, hi, here⟩⟩
      · exact ⟨notFree hi same here, ⟨i, hi, here⟩⟩
    · have here : v ∈ vertices i := equal ▸ atPorts i hi
      exact ⟨notFree hi different here, ⟨i, hi, here⟩⟩
  · rintro ⟨away, i, hi, here⟩
    by_cases eq : v = port i
    · have different : i ≠ free := fun same => away (eq.trans (congrArg port same))
      exact Or.inr ⟨i, ⟨different, hi⟩, eq.symm⟩
    · exact Or.inl ⟨i, hi, eq, here⟩

/-- Distinct matched children have distinct ports, so replacing each quotient edge by the
edge joining its original ports preserves the matching. -/
theorem perfectMatching_map_ports {n k : ℕ} {groups : Finset (Fin k)}
    {M : Finset (Sym2 (Fin k))} (matched : IsPerfectMatchingOn groups M) (port : Fin k → Fin n)
    (injective : Set.InjOn port (groups : Set (Fin k))) :
    IsPerfectMatchingOn (groups.image port) (M.image (Sym2.map port)) := by
  constructor
  · intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    refine ⟨?_, fun v hv => ?_⟩
    · induction f using Sym2.inductionOn with
      | hf a b =>
        rw [Sym2.map_mk, Sym2.mk_isDiag_iff]
        intro same
        have included := (matched.1 _ hf).2
        exact (matched.1 _ hf).1 (Sym2.mk_isDiag_iff.mpr (injective
          (included a (Sym2.mem_mk_left _ _)) (included b (Sym2.mem_mk_right _ _)) same))
    · obtain ⟨w, belongs, equal⟩ := Sym2.mem_map.mp hv
      exact Finset.mem_image.mpr ⟨w, (matched.1 f hf).2 w belongs, equal⟩
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨e, covers, unique⟩ := matched.2 u hu
    refine ⟨Sym2.map port e, ⟨Finset.mem_image_of_mem _ covers.1,
      Sym2.mem_map.mpr ⟨u, covers.2, rfl⟩⟩, ?_⟩
    intro f hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf.1
    obtain ⟨w, atEnd, same⟩ := Sym2.mem_map.mp hf.2
    have equal : w = u := injective ((matched.1 g hg).2 w atEnd) hu same
    exact congrArg (Sym2.map port) (unique g ⟨hg, equal ▸ atEnd⟩)

end VehicleRoutingSurvey.Routing
end RppSource_BlossomMatchingLift

/-! matching/MatchingRebasePrimalLift.lean -/
section RppSource_MatchingRebasePrimalLift
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The alternating edges written by one real cyclic rebase, together with
the recursively lifted child matchings, give a tight perfect matching on all
original vertices of the blossom except its new exposed port. -/
theorem matchingRebaseCycle_liftsPrimal {k n : ℕ} (cycle : List (Fin n))
    (free : ℕ) (inCycle : free < cycle.length) (unique : cycle.Nodup) (odd : Odd cycle.length)
    (vertices : Fin n → Finset (Fin k)) (port : Fin n → Fin k)
    (insideEdges : Fin n → Finset (Sym2 (Fin k))) (tight : Sym2 (Fin k) → Prop)
    (separate : (cycle.toFinset : Set (Fin n)).PairwiseDisjoint vertices)
    (ports : ∀ j ∈ cycle.toFinset, port j ∈ vertices j)
    (inside : ∀ j ∈ cycle.toFinset, IsPerfectMatchingOn ((vertices j).erase (port j)) (insideEdges j))
    (insideTight : ∀ j ∈ cycle.toFinset, ∀ e ∈ insideEdges j, tight e)
    (pairTight : ∀ i < (cycle.length - 1) / 2,
      let a := matchingRebaseChildIndex cycle.length free i false
      let b := matchingRebaseChildIndex cycle.length free i true
      tight s(port (cycle.get ⟨a,Nat.mod_lt _ (Nat.zero_lt_of_lt inCycle)⟩),
        port (cycle.get ⟨b,Nat.mod_lt _ (Nat.zero_lt_of_lt inCycle)⟩))) :
    let crossing := (rematchBlossomCycle cycle free).image (Sym2.map port)
    let lifted := liftMatchingAcrossBlocks cycle.toFinset insideEdges crossing
    IsPerfectMatchingOn ((cycle.toFinset.biUnion vertices).erase (port cycle[free])) lifted ∧
      (∀ e ∈ lifted, tight e) ∧
      ∀ j ∈ cycle.toFinset, ∀ v ∈ vertices j, v ≠ port j → ∃ e ∈ lifted, v ∈ e ∧ ∀ w ∈ e, w ∈ vertices j := by
  intro crossing lifted
  have freeIn : cycle[free] ∈ cycle.toFinset := List.mem_toFinset.mpr (List.getElem_mem _)
  have projected := (rematchBlossomCycle_spec inCycle unique odd (fun _ => True) (fun _ _ => trivial)).1
  have injective : Set.InjOn port ((cycle.toFinset.erase cycle[free]) : Set (Fin n)) := by
    intro a ha b hb same
    by_contra different
    have aIn := (Finset.mem_erase.mp ha).2
    have bIn := (Finset.mem_erase.mp hb).2
    exact Finset.disjoint_left.mp (separate aIn bIn different) (ports a aIn) (same.symm ▸ ports b bIn)
  have crossingPerfect := perfectMatching_map_ports projected port injective
  have onEdges (e : Sym2 (Fin k)) (belongs : e ∈ crossing) : tight e := by
    obtain ⟨q, insideQ, rfl⟩ := Finset.mem_image.mp belongs
    obtain ⟨i, hi, rfl⟩ := (rematchBlossomCycle_mem_iff_physicalPair cycle inCycle q).mp insideQ
    simpa only [Sym2.map_mk, List.get_eq_getElem] using! pairTight i hi
  have all := liftMatchingAcrossBlocks_spec cycle.toFinset (cycle.toFinset.erase cycle[free])
    (Finset.erase_subset _ _) vertices port insideEdges crossing separate ports inside crossingPerfect tight insideTight onEdges
  have covered := liftedBlossom_vertices freeIn vertices port separate ports
  exact ⟨covered ▸ all.1, all.2⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebasePrimalLift

/-! matching/MatchingRebaseRecursivePrimal.lean -/
section RppSource_MatchingRebaseRecursivePrimal
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory







structure MatchingCutLift {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    {node : Finset (Fin k) → ℕ} (lookup : ∀ B ∈ state.cuts, MatchingLiveCycle state node B)
    (B : Finset (Fin k)) (desired : Fin k) (edges : Finset (Sym2 (Fin k))) : Prop where
  actual : MatchingCycleLiftDerivation lookup B desired edges
  perfect : IsPerfectMatchingOn (B.erase desired) edges
  tight : ∀ e ∈ edges, matchingLiftTight state e
  cuts : ∀ D ∈ state.cuts, D ⊆ B → ∃ childBase ∈ D, ∀ v ∈ D, v ≠ childBase →
    ∃ e ∈ edges, v ∈ e ∧ ∀ w ∈ e, w ∈ D

/-- Every live blossom admits a tight internal lift around any prescribed
new original port. Each retained nested cut has a near-perfect internal
matching after the lift, which supplies complementary slackness. -/
theorem matchingCutLift_exists {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    {node : Finset (Fin k) → ℕ} (lookup : ∀ B ∈ state.cuts, MatchingLiveCycle state node B)
    (nontrivial : ∀ B ∈ state.cuts, 1 < B.card)
    (B : Finset (Fin k)) (live : B ∈ state.cuts) (desired : Fin k) (inside : desired ∈ B) :
    ∃ edges, MatchingCutLift lookup B desired edges := by
  classical
  suffices all : ∀ m, ∀ C ∈ state.cuts, C.card = m → ∀ p ∈ C, ∃ edges, MatchingCutLift lookup C p edges by
    exact all B.card B live rfl desired inside
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro C registered card p member
    let e := lookup C registered
    let ports := e.chooseLiftPorts p member
    let groups := e.ports.ports
    let block := e.ports.block
    have smaller {q : Fin k} (hq : q ∈ groups) (notSingle : (block q).card ≠ 1) :
        (block q).card < m := by
      have neq := (Finset.mem_erase.mp (e.ports.live q hq notSingle)).1
      rw [← card]
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨e.ports.subset q hq, neq⟩)
    have child (q : Fin k) : ∃ edges : Finset (Sym2 (Fin k)), q ∈ groups →
        IsPerfectMatchingOn ((block q).erase (ports.choose q)) edges ∧
        (∀ edge ∈ edges, matchingLiftTight state edge) ∧ ((block q).card = 1 → edges = ∅) ∧
        ((block q).card ≠ 1 → MatchingCutLift lookup (block q) (ports.choose q) edges) := by
      by_cases listed : q ∈ groups
      · have picked := ports.members q listed
        by_cases singleton : (block q).card = 1
        · obtain ⟨x, one⟩ := Finset.card_eq_one.mp singleton
          have atX : ports.choose q = x := Finset.mem_singleton.mp (one ▸ picked)
          refine ⟨∅, fun _ => ⟨?_, by simp, fun _ => rfl, fun no => (no singleton).elim⟩⟩
          simp [one, atX, IsPerfectMatchingOn]
        · have present := Finset.mem_of_mem_erase (e.ports.live q listed singleton)
          obtain ⟨edges, ok⟩ := ih _ (smaller listed singleton) _ present rfl _ picked
          exact ⟨edges, fun _ => ⟨ok.perfect, ok.tight, fun yes => (singleton yes).elim, fun _ => ok⟩⟩
      · exact ⟨∅, fun yes => (listed yes).elim⟩
    choose inner childData using child
    let result := matchingLiftTreeEdges ports inner
    have groupsEq : e.geometry.cycle.toFinset = groups := e.geometry.ports.symm
    have separation : (groups : Set (Fin k)).PairwiseDisjoint block := by
      intro a ha b hb diff
      apply Finset.disjoint_left.mpr
      intro v hv hw
      exact diff ((e.ports.unique a ha v hv).symm.trans (e.ports.unique b hb v hw))
    have union : groups.biUnion block = C := by
      ext v
      constructor
      · intro found
        obtain ⟨q, hq, hv⟩ := Finset.mem_biUnion.mp found
        exact e.ports.subset q hq hv
      · intro hv
        exact Finset.mem_biUnion.mpr ⟨_, e.ports.covered v hv⟩
    have tightRows (i : ℕ) (hi : i < (e.geometry.cycle.length-1)/2) :
        let a := matchingRebaseChildIndex e.geometry.cycle.length ports.free.val i false
        let b := matchingRebaseChildIndex e.geometry.cycle.length ports.free.val i true
        matchingLiftTight state s(ports.choose (e.geometry.cycle.get ⟨a,Nat.mod_lt _ (Nat.zero_lt_of_lt ports.free.isLt)⟩),
          ports.choose (e.geometry.cycle.get ⟨b,Nat.mod_lt _ (Nat.zero_lt_of_lt ports.free.isLt)⟩)) := by
      have eq := ports.pairs i hi
      exact (congrArg (fun z : Fin k × Fin k => matchingLiftTight state s(z.1,z.2)) eq).mpr (e.geometry.tight _)
    have lifted := matchingRebaseCycle_liftsPrimal e.geometry.cycle ports.free.val ports.free.isLt
      e.geometry.distinct e.geometry.odd block ports.choose inner (matchingLiftTight state)
      (groupsEq.symm ▸ separation) (groupsEq.symm ▸ ports.members)
      (fun q hq => (childData q (groupsEq ▸ hq)).1) (fun q hq => (childData q (groupsEq ▸ hq)).2.1) tightRows
    have perfect : IsPerfectMatchingOn (C.erase p) result := by
      have support : (e.geometry.cycle.toFinset.biUnion block).erase (ports.choose (e.geometry.cycle.get ports.free)) =
          C.erase p := by rw [groupsEq, union, ports.exposed]
      exact support ▸ lifted.1
    refine ⟨result, ⟨.join registered ports inner perfect (fun q listed => (childData q listed).1)
      (fun q listed => (childData q listed).2.2.1)
      (fun q listed many => ((childData q listed).2.2.2 many).actual), perfect, lifted.2.1, ?_⟩⟩
    intro D dLive subset
    by_cases same : D = C
    · subst D
      refine ⟨p, member, ?_⟩
      intro v hv different
      obtain ⟨x, present, _⟩ := perfect.2 v (Finset.mem_erase.mpr ⟨different, hv⟩)
      exact ⟨x, present.1, present.2, fun w hw => (Finset.mem_erase.mp ((perfect.1 x present.1).2 w hw)).2⟩
    · obtain ⟨q, qIn, dBelow⟩ := e.descendants D (Finset.mem_erase.mpr ⟨same, dLive⟩) subset
      have sizeD := nontrivial D dLive
      have below := Finset.card_le_card dBelow
      have many : (block q).card ≠ 1 := by change D.card ≤ (block q).card at below; omega
      obtain ⟨base, inD, maintains⟩ := ((childData q qIn).2.2.2 many).cuts D dLive dBelow
      refine ⟨base, inD, ?_⟩
      intro v hv diff
      obtain ⟨x, present, incident, contained⟩ := maintains v hv diff
      exact ⟨x, Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨q, groupsEq.symm ▸ qIn, present⟩), incident, contained⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseRecursivePrimal

/-! matching/MatchingAugmentDerivedCut.lean -/
section RppSource_MatchingAugmentDerivedCut
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

theorem MatchingLiveCycle.jobKey {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    (e : MatchingLiveCycle old node B) (i : ℕ) (hi : i < (e.tree.jobs none).length) :
    ((e.tree.jobs none)[i]).representative = (e.geometry.cycle.get
      ⟨i, ((e.tree.jobs_length none).trans e.arity) ▸ hi⟩).val := by
  have labels : (e.tree.jobs none).map MatchingMemberJob.representative = e.geometry.cycle.map Fin.val := by
    rw [← e.keys, ← e.tree.jobs_rootKeys none, List.map_map]
    rfl
  have left : i < ((e.tree.jobs none).map MatchingMemberJob.representative).length := by simpa using hi
  have right : i < (e.geometry.cycle.map Fin.val).length := congrArg List.length labels ▸ left
  have eq : ((e.tree.jobs none).map MatchingMemberJob.representative)[i] = (e.geometry.cycle.map Fin.val)[i] :=
    getElem_congr_coll labels
  simpa only [List.getElem_map,List.get_eq_getElem] using! eq



/-- One mathematical lift determines the future RAM word for every immediate
child, the exact alternating crossing pairs, and all live descendant requests. -/
theorem MatchingCycleLiftDerivation.nodeData {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (cycles : MatchingLiveCycles registry) {B : Finset (Fin k)} (hb : B ∈ old.cuts)
    {p : Fin k} (hp : p ∈ B) {E : Finset (Sym2 (Fin k))}
    (proof : MatchingCycleLiftDerivation cycles.entry B p E) (sub : E ⊆ next.edges) :
    let entry := cycles.entry B hb
    let nodePort := matchingAugmentNodePort next old.cuts dual.node
    nodePort (dual.node B) = p.val ∧ ∃ ports : MatchingCycleLiftPorts entry p,
      (∀ i (hi : i < (entry.tree.jobs none).length),
        matchingRebasePortAt entry.tree (MatchingMemberJob.liftPort nodePort) i =
          (ports.choose (entry.geometry.cycle.get ⟨i, ((entry.tree.jobs_length none).trans entry.arity) ▸ hi⟩)).val) ∧
      (∀ i (hi : i < (entry.geometry.cycle.length - 1) / 2),
        let left : Fin entry.geometry.cycle.length :=
          ⟨matchingRebaseChildIndex entry.geometry.cycle.length ports.free.val i false, Nat.mod_lt _ (Nat.zero_lt_of_lt ports.free.isLt)⟩
        let edge := entry.geometry.edges left
        s(edge.1,edge.2) ∈ next.edges) ∧
      ∀ job ∈ entry.tree.jobs none, ∀ child, job.children = some child →
        ∃ (C : Finset (Fin k)) (hc : C ∈ old.cuts), dual.node C = job.node ∧ (cycles.entry C hc).tree = child ∧
          matchingAugmentDerivedCut cycles.entry next C := by
  cases proof with
  | join live ports inner rootMatching childMatching single down =>
    let entry := cycles.entry B live
    let nodePort := matchingAugmentNodePort next old.cuts dual.node
    have groups : entry.geometry.cycle.toFinset = entry.ports.ports := entry.geometry.ports.symm
    have contains {q : Fin k} (hq : q ∈ entry.ports.ports) : inner q ⊆ next.edges := by
      intro e he
      exact sub (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨q, groups.symm ▸ hq, he⟩))
    have atJob (job : MatchingMemberJob) (listed : job ∈ entry.tree.jobs none)
        (q : Fin k) (label : job.representative = q.val) : job.liftPort nodePort = (ports.choose q).val := by
      obtain ⟨on, leaf⟩ := entry.owner job listed q label
      have chosen := ports.members q on
      cases kind : job.children with
      | none =>
        have c := (leaf (ports.choose q)).mpr chosen
        have key : (ports.choose q).val = job.representative := by simpa [MatchingMemberJob.tree,kind,MatchingMemberTree.leaves] using c
        exact (show job.liftPort nodePort = job.representative from by simp [MatchingMemberJob.liftPort, kind]).trans key.symm
      | some child =>
        obtain ⟨C, cLive, eqId, _, oldBase, cBlock⟩ := cycles.child B live job listed child kind
        have baseQ : (cycles.entry C cLive).base = q := Fin.ext (oldBase.trans label)
        rw [baseQ] at cBlock
        have actual : matchingAugmentNodePort next old.cuts dual.node (dual.node C) = (ports.choose q).val :=
          matchingAugmentNodePort_eq next dual.nodeInjective cLive (cBlock.symm ▸ chosen)
            (cBlock.symm ▸ childMatching q on) (contains on)
        simpa [MatchingMemberJob.liftPort, kind, nodePort, eqId] using actual
    refine ⟨matchingAugmentNodePort_eq next dual.nodeInjective live hp rootMatching sub, ports, ?_, ?_, ?_⟩
    · intro i hi
      have inside : i < (entry.tree.jobs none).length := hi
      exact (show matchingRebasePortAt entry.tree (MatchingMemberJob.liftPort nodePort) i =
          ((entry.tree.jobs none)[i]).liftPort nodePort by simp [matchingRebasePortAt,inside]).trans
        (atJob _ (List.getElem_mem hi) _ (entry.jobKey i hi))
    · intro i hi
      let index (side : Bool) : Fin entry.geometry.cycle.length :=
        ⟨matchingRebaseChildIndex entry.geometry.cycle.length ports.free.val i side, Nat.mod_lt _ (Nat.zero_lt_of_lt ports.free.isLt)⟩
      let edge : Sym2 (Fin k) := s(entry.geometry.cycle.get (index false), entry.geometry.cycle.get (index true))
      have present : edge ∈ rematchBlossomCycle entry.geometry.cycle ports.free.val :=
        (rematchBlossomCycle_mem_iff_physicalPair _ ports.free.isLt _).mpr ⟨i, hi, rfl⟩
      have atPorts : Sym2.map ports.choose edge = s((entry.geometry.edges (index false)).1,(entry.geometry.edges (index false)).2) :=
        congrArg (fun e : Fin k × Fin k => s(e.1,e.2)) (ports.pairs i hi)
      exact sub (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨edge,present,atPorts⟩))
    · intro job listed child kind
      obtain ⟨C, hc, id, tree, key, atC⟩ := cycles.child B live job listed child kind
      let q := (cycles.entry C hc).base
      have member := (entry.owner job listed q key.symm).1
      have large := registry.nontrivial C hc
      have many : (entry.ports.block q).card ≠ 1 := by rw [← atC]; omega
      exact ⟨C,hc,id,tree,ports.choose q,atC.symm ▸ ports.members q member, inner q, contains member,
        atC.symm ▸ down q member many⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentDerivedCut

/-! matching/MatchingAugmentPrimalOutput.lean -/
section RppSource_MatchingAugmentPrimalOutput
namespace VehicleRoutingSurvey.Routing



theorem compactPrimalMateWord_of_edge {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) {a b : Fin k} (edge : s(a,b) ∈ state.edges) :
    compactPrimalMateWord state a.val = b.val ∧ compactPrimalMateWord state b.val = a.val := by
  have value {v w : Fin k} (found : s(v,w) ∈ state.edges) : compactPrimalMateWord state v.val = w.val := by
    have covered := (state.perfect.1 _ found).2 v (Sym2.mem_mk_left _ _)
    have partner := state.partialMate_some_iff.mpr found
    rw [CompactMatchingPrimalDual.partialMate, if_pos covered, Option.some.injEq] at partner
    simpa [compactPrimalMateWord, v.isLt, covered] using congrArg Fin.val partner
  exact ⟨value edge, value (Sym2.eq_swap ▸ edge)⟩

/-- Every selected original crossing is an edge of the given mathematical
matching. Its mate equations follow from unique incidence of a perfect matching. -/
def MatchingRebaseLiftTarget.of_primalEdges {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {base : ArithmeticState} (next : CompactMatchingPrimalDual k cost) (archive : MatchingRebaseArchive base)
    (port : ℕ → ℕ)
    (inherits : ∀ n c, archive.live n c → ∀ free (hf : free < (c.jobs none).length),
      port n ∈ ((c.jobs none)[free]'hf).tree.leaves → matchingRebasePortAt c (MatchingMemberJob.liftPort port) free = port n)
    (pairs : ∀ n c (known : archive.live n c) free (hf : free < (c.jobs none).length),
      port n ∈ ((c.jobs none)[free]'hf).tree.leaves → ∀ i < (c.arity - 1) / 2,
        let left := matchingRebaseChildIndex c.arity free i false
        let right := matchingRebaseChildIndex c.arity free i true
        let edge := (archive.record _ _ known).geometry.edge left
        (matchingRebasePortAt c (MatchingMemberJob.liftPort port) left,
          matchingRebasePortAt c (MatchingMemberJob.liftPort port) right) = edge ∧
          ∃ a b : Fin k, edge = (a.val, b.val) ∧ s(a,b) ∈ next.edges) :
    MatchingRebaseLiftTarget archive (compactPrimalMateWord next) where
  port := port
  inherits := inherits
  pairs := by
    intro n c known free hf belongs i hi
    obtain ⟨eq, a, b, physical, matched⟩ := pairs n c known free hf belongs i hi
    refine ⟨eq, ?_⟩
    rw [physical]
    exact compactPrimalMateWord_of_edge next matched




end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentPrimalOutput

/-! matching/MatchingAugmentDerivedArchive.lean -/
section RppSource_MatchingAugmentDerivedArchive
namespace VehicleRoutingSurvey.Routing

/-- Restrict the immutable registry to the recursively lifted cuts. A nested
request is live because its derivation is part of its parent's derivation. -/
noncomputable def matchingAugmentDerivedArchive {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {s base : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (cycles : MatchingLiveCycles registry) (full : MatchingRebaseArchive base)
    (archived : ∀ B (h : B ∈ old.cuts), full.live (dual.node B) (cycles.entry B h).tree) : MatchingRebaseArchive base := by
  let reaches (n : ℕ) (c : MatchingMemberTree) := ∃ (B : Finset (Fin k)) (h : B ∈ old.cuts),
    dual.node B = n ∧ (cycles.entry B h).tree = c ∧ matchingAugmentDerivedCut cycles.entry next B
  have known (n c) (h : reaches n c) : full.live n c := by
    obtain ⟨B,live,rfl,rfl,_⟩ := h
    exact archived B live
  refine ⟨reaches, fun n c h => full.record n c (known n c h), fun n c h => full.allocated n c (known n c h),
    ?_, fun n c h => full.headers n c (known n c h), full.order,full.mates,full.mapWalk,full.walkJobs,full.jobsRecords⟩
  intro n c h job listed child within
  obtain ⟨B,hb,rfl,rfl,p,hp,E,inNext,found⟩ := h
  obtain ⟨_, _, _, _, descend⟩ := found.nodeData cycles hb hp inNext
  exact descend job listed child within

theorem MatchingCycleLiftPorts.free_of_leaf {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)} {desired : Fin k}
    {entry : MatchingLiveCycle old node B} (ports : MatchingCycleLiftPorts entry desired) (i : ℕ)
    (hi : i < (entry.tree.jobs none).length) (contains : desired.val ∈ ((entry.tree.jobs none)[i]).tree.leaves) :
    i = ports.free.val := by
  let actual : Fin entry.geometry.cycle.length := ⟨i, ((entry.tree.jobs_length none).trans entry.arity) ▸ hi⟩
  have child := entry.owner _ (List.getElem_mem hi) _ (entry.jobKey i hi)
  have oldOwner := entry.ports.unique _ child.1 desired ((child.2 _).mp contains)
  let actualFree := entry.geometry.cycle.get ports.free
  have listed : actualFree ∈ entry.ports.ports := by
    rw [entry.geometry.ports]
    exact List.mem_toFinset.mpr (List.get_mem entry.geometry.cycle ports.free)
  have newOwner := entry.ports.unique _ listed desired (ports.exposed ▸ ports.members _ listed)
  exact (List.Nodup.getElem_inj_iff entry.geometry.distinct).mp (oldOwner.symm.trans newOwner)

/-- The close-out target for the RAM is supplied by the mathematical lifted
matching itself, including every recursive mate and every inherited port. -/
noncomputable def matchingAugmentDerivedPlan {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {s base : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (cycles : MatchingLiveCycles registry) (full : MatchingRebaseArchive base)
    (archived : ∀ B (h : B ∈ old.cuts), full.live (dual.node B) (cycles.entry B h).tree)
    (originals : ∀ B (h : B ∈ old.cuts), ∀ (i : Fin (cycles.entry B h).geometry.cycle.length),
      let edge := (cycles.entry B h).geometry.edges i
      (full.record _ _ (archived B h)).geometry.edge i.val = (edge.1.val,edge.2.val)) :
    MatchingRebaseLiftTarget (matchingAugmentDerivedArchive (next := next) cycles full archived) (compactPrimalMateWord next) := by
  let nodePort := matchingAugmentNodePort next old.cuts dual.node
  apply MatchingRebaseLiftTarget.of_primalEdges next _ nodePort
  · intro n c known free hf atFree
    obtain ⟨B,hb,rfl,rfl,p,hp,E,inNext,found⟩ := known
    let e := cycles.entry B hb
    obtain ⟨nodeWord, ports, table, _, _⟩ := found.nodeData cycles hb hp inNext
    have inChild : p.val ∈ ((e.tree.jobs none)[free]'hf).tree.leaves := nodeWord ▸ atFree
    have eq := ports.free_of_leaf free hf inChild
    have loc : (⟨free, ((e.tree.jobs_length none).trans e.arity) ▸ hf⟩ : Fin e.geometry.cycle.length) = ports.free := Fin.ext eq
    exact (table free hf).trans ((congrArg (fun j : Fin e.geometry.cycle.length =>
      (ports.choose (e.geometry.cycle.get j)).val) loc).trans ((congrArg Fin.val ports.exposed).trans nodeWord.symm))
  · intro n c known free hf belongs i hi
    obtain ⟨B,hb,rfl,rfl,p,hp,E,inNext,found⟩ := known
    let e := cycles.entry B hb
    obtain ⟨nodeWord, ports, table, paired, _⟩ := found.nodeData cycles hb hp inNext
    have inChild : p.val ∈ ((e.tree.jobs none)[free]'hf).tree.leaves := nodeWord ▸ belongs
    have eq := ports.free_of_leaf free hf inChild
    have enough : i < (e.geometry.cycle.length-1)/2 := e.arity ▸ hi
    let index (b : Bool) : Fin e.geometry.cycle.length :=
      ⟨matchingRebaseChildIndex e.geometry.cycle.length ports.free.val i b, Nat.mod_lt _ (Nat.zero_lt_of_lt ports.free.isLt)⟩
    have loc (b : Bool) : matchingRebaseChildIndex e.tree.arity free i b = (index b).val :=
      congrArg₂ (fun length first => matchingRebaseChildIndex length first i b) e.arity eq
    have word (b : Bool) : matchingRebasePortAt e.tree (MatchingMemberJob.liftPort nodePort)
        (matchingRebaseChildIndex e.tree.arity free i b) = (ports.choose (e.geometry.cycle.get (index b))).val := by
      rw [loc]
      exact table _ (((e.tree.jobs_length none).trans e.arity).symm ▸ (index b).isLt)
    let edge := e.geometry.edges (index false)
    have raw : (full.record _ _ (archived B hb)).geometry.edge (matchingRebaseChildIndex e.tree.arity free i false) =
        (edge.1.val,edge.2.val) := (congrArg _ (loc false)).trans (originals B hb (index false))
    change (_,_) = (full.record _ _ (archived B hb)).geometry.edge _ ∧
      ∃ a b : Fin k, (full.record _ _ (archived B hb)).geometry.edge _ = (a.val,b.val) ∧ s(a,b) ∈ next.edges
    rw [raw]
    exact ⟨(Prod.ext (word false) (word true)).trans
      (congrArg (fun z : Fin k × Fin k => (z.1.val,z.2.val)) (ports.pairs i enough)),
      edge.1,edge.2,rfl,paired i enough⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentDerivedArchive

/-! matching/MatchingAugmentArchiveRows.lean -/
section RppSource_MatchingAugmentArchiveRows
namespace VehicleRoutingSurvey.Routing

/-- Ownership orients an undirected archived record uniquely. Both the
expansion view and any rebase view of that record read the same original edge. -/
theorem MatchingArchivedCycle.liveEdge {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    {entry : MatchingLiveCycle old node B} {s : ArithmeticState}
    (rows : MatchingNodeCycleRows s (node B) entry.geometry.cycle entry.geometry.edges)
    (arch : MatchingArchivedCycle s (node B) entry.tree) (i : Fin entry.geometry.cycle.length) :
    arch.geometry.edge i.val = ((entry.geometry.edges i).1.val,(entry.geometry.edges i).2.val) := by
  let g := entry.geometry
  let cell := matchingCycleChildAt s.nm (matchingCycleRecordStart s (node B) + 4*i.val)
  have hi : i.val < entry.tree.arity := entry.arity.symm ▸ i.isLt
  have r : (cell.endpointA,cell.endpointB) = ((g.edges i).1.val,(g.edges i).2.val) := (rows.records i).2
  have encoded := arch.geometry.row i.val hi
  change (cell.endpointA,cell.endpointB) = arch.geometry.edge i.val ∨
    (cell.endpointA,cell.endpointB) = (arch.geometry.edge i.val).swap at encoded
  rcases encoded with forward | reversed
  · exact forward.symm.trans r
  · have second := congrArg Prod.snd (reversed.symm.trans r)
    have hj : i.val < (entry.tree.jobs none).length := (entry.tree.jobs_length none).symm ▸ hi
    have raw := arch.geometry.source i.val hj
    change (arch.geometry.edge i.val).1 = (g.edges i).2.val at second
    rw [second] at raw
    have side := entry.owner _ (List.getElem_mem hj) _ (entry.jobKey i.val hj)
    have atLeft := entry.ports.unique _ side.1 _ ((side.2 _).mp raw)
    let j : Fin g.cycle.length := ⟨(i.val+1)%g.cycle.length,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    have onRight : g.cycle.get j ∈ entry.ports.ports := by
      rw [g.ports]
      exact List.mem_toFinset.mpr (List.get_mem ..)
    have atRight := entry.ports.unique _ onRight _ (g.target i)
    have eq : i.val = j.val := (List.Nodup.getElem_inj_iff g.distinct).mp (atLeft.symm.trans atRight)
    have big : 2 ≤ g.cycle.length := entry.arity ▸ arch.members.proper.2.1
    have inside : i.val < g.cycle.length := i.isLt
    change i.val = (i.val+1)%g.cycle.length at eq
    by_cases below : i.val+1 < g.cycle.length
    · rw [Nat.mod_eq_of_lt below] at eq
      omega
    · have edge : i.val+1 = g.cycle.length := by omega
      rw [edge,Nat.mod_self] at eq
      omega

/-- Oriented persistent cycle rows discharge the actual-record premise of
the mathematical mate target for the recursively reached archive. -/
noncomputable def matchingAugmentPlanOfRows {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {s base : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (cycles : MatchingLiveCycles registry) (full : MatchingRebaseArchive base)
    (archived : ∀ B (h : B ∈ old.cuts), full.live (dual.node B) (cycles.entry B h).tree)
    (rows : ∀ B (h : B ∈ old.cuts), MatchingNodeCycleRows base (dual.node B)
      (cycles.entry B h).geometry.cycle (cycles.entry B h).geometry.edges) :
    MatchingRebaseLiftTarget (matchingAugmentDerivedArchive (next := next) cycles full archived) (compactPrimalMateWord next) :=
  matchingAugmentDerivedPlan cycles full archived (fun B h => (full.record _ _ (archived B h)).liveEdge (rows B h))


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentArchiveRows

/-! matching/MatchingAugmentInitialTasks.lean -/
section RppSource_MatchingAugmentInitialTasks
namespace VehicleRoutingSurvey.Routing



theorem MatchingLiveCycle.leaves_iff {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    (e : MatchingLiveCycle old node B) (v : Fin k) : v.val ∈ e.tree.leaves ↔ v ∈ B := by
  have children := e.tree.jobs none
  have count := (e.tree.jobs_length none).trans e.arity
  constructor
  · intro leaf
    rw [← e.tree.jobs_frontier_vertices none] at leaf
    obtain ⟨word, hw, atV⟩ := List.mem_map.mp leaf
    obtain ⟨j, listed, belongs⟩ := List.mem_flatMap.mp hw
    obtain ⟨i, hi, row⟩ := List.mem_iff_getElem.mp listed
    let q := e.geometry.cycle.get ⟨i, count ▸ hi⟩
    have label : j.representative = q.val := row ▸ e.jobKey i hi
    obtain ⟨present, inBlock⟩ := e.owner j listed q label
    have mem : v.val ∈ j.assignments.map Prod.fst := List.mem_map.mpr ⟨_,belongs,atV⟩
    exact e.ports.subset q present ((inBlock v).mp (j.assignments_vertices ▸ mem))
  · intro inside
    obtain ⟨qIn,vIn⟩ := e.ports.covered v inside
    have on : e.ports.owner v ∈ e.geometry.cycle := List.mem_toFinset.mp (e.geometry.ports ▸ qIn)
    obtain ⟨i, hi, selected⟩ := List.mem_iff_getElem.mp on
    have hj : i < (e.tree.jobs none).length := count.symm ▸ hi
    let j := (e.tree.jobs none)[i]'hj
    have label : j.representative = (e.ports.owner v).val := (e.jobKey i hj).trans (congrArg Fin.val selected)
    have leaf := ((e.owner j (List.getElem_mem hj) _ label).2 v).mpr vIn
    have inAssigned := j.assignments_vertices.symm ▸ leaf
    obtain ⟨word, hw, eq⟩ := List.mem_map.mp inAssigned
    rw [← e.tree.jobs_frontier_vertices none]
    exact List.mem_map.mpr ⟨word,List.mem_flatMap.mpr ⟨j,List.getElem_mem hj,hw⟩,eq⟩

theorem matchingAugmentTopTask_records {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (cycles : MatchingLiveCycles registry) (ports : List (Fin k)) :
    ((ports.filterMap (matchingAugmentTopTask cycles)).map (fun t => (t.node,t.port))) =
      (expectedAugmentationJobs part.representative (fun x => blossomNodeAt s x) ports).map (fun p => (p.1,p.2.val)) := by
  induction ports with
  | nil => rfl
  | cons x rest ih =>
    let q := part.representative x
    have fixed : part.representative q = q := part.representative_idem x
    by_cases big : (part.blocks.block q).card ≠ 1
    · have live := part.blocks.cut_mem (Finset.mem_univ q) big
      have id := dual.nodeNonzero _ live
      simp [matchingAugmentTopTask,expectedAugmentationJobs,dual.top, q,part.representative_idem,
        show (part.blocks.block (part.representative x)).card ≠ 1 from big,id] at ih ⊢
      exact ih
    · have single : (part.blocks.block q).card = 1 := not_ne_iff.mp big
      simpa [matchingAugmentTopTask,expectedAugmentationJobs,dual.top,q,part.representative_idem,
        show (part.blocks.block (part.representative x)).card = 1 from single] using ih

theorem AugmentationPreRebaseReady.liveTasks {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {s u t : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (cycles : MatchingLiveCycles registry) {rows : List (Fin k × Fin k)} (ready : AugmentationPreRebaseReady rows u t)
    (layout : AugmentationInstallLayout k (augmentationCrossingSeed u k))
    (original : ∀ v : Fin k, u.nm (u.nr 57+v.val) = (part.representative v).val)
    (nodes : ∀ v : Fin k, u.nm (u.nr 74+v.val) = blossomNodeAt s v)
    (unique : ((selectedAugmentationPorts rows).map part.representative).Nodup) :
    let tasks := (selectedAugmentationPorts rows).filterMap (matchingAugmentTopTask cycles)
    MatchingRebaseQueueEncoding t tasks := by
  intro tasks
  let select := part.representative
  let node := fun v : Fin k => blossomNodeAt s v
  let model := rows.foldl (AugmentationRebaseModel.crossing select) (⟨node,[]⟩ : AugmentationRebaseModel k)
  have encoded := ready.queuedRegistry layout select node original nodes
  have expected : model.jobs = expectedAugmentationJobs select node (selectedAugmentationPorts rows) := by
    simpa [model] using AugmentationRebaseModel.crossing_jobs select part.representative_idem rows unique
      (⟨node,[]⟩ : AugmentationRebaseModel k)
  have exactRows : tasks.map (fun j => (j.node,j.port)) = model.jobs.map (fun p => (p.1,p.2.val)) :=
    (matchingAugmentTopTask_records cycles _).trans (congrArg (List.map (fun p : ℕ × Fin k => (p.1,p.2.val))) expected.symm)
  have count : tasks.length = model.jobs.length := by simpa using congrArg List.length exactRows
  refine ⟨encoded.count.trans count.symm, ?_⟩
  intro i hi
  have hj := count ▸ hi
  have values := congrArg (fun xs : List (ℕ × ℕ) => xs[i]?) exactRows
  simp only [List.getElem?_map,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj, Option.map_some, Option.some.injEq] at values
  exact (encoded.jobs i hj).trans values.symm


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentInitialTasks

/-! matching/MatchingAugmentQuotient.lean -/
section RppSource_MatchingAugmentQuotient
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Old matched edges between top-level representatives. -/
noncomputable def CompactMatchingPartition.quotientEdges {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) : Finset (Sym2 (Fin k)) :=
  state.edges.filter fun e => ∀ v ∈ e, v ∈ part.activeRepresentatives

def CompactMatchingPartition.quotientCovered {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) : Finset (Fin k) :=
  state.covered ∩ part.activeRepresentatives

noncomputable def CompactMatchingPartition.quotientMate {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (v : Fin k) : Option (Fin k) :=
  if v ∈ part.activeRepresentatives then state.partialMate v else none

theorem CompactTopMatching.quotientMate_some {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    (top : CompactTopMatching part) {a b : Fin k} :
    part.quotientMate a = some b ↔ s(a,b) ∈ part.quotientEdges := by
  constructor
  · intro someMate
    by_cases present : a ∈ part.activeRepresentatives
    · have original : state.partialMate a = some b := by simpa [CompactMatchingPartition.quotientMate, present] using someMate
      have actual := state.partialMate_some_iff.mp original
      have separated := top.matchedBase ((part.mem_activeRepresentatives _).mp present) original
      obtain ⟨_, other⟩ := top.crossing_endpoints actual separated
      apply Finset.mem_filter.mpr
      refine ⟨actual, ?_⟩
      intro v member
      rcases Sym2.mem_iff.mp member with eq | eq
      · exact eq.symm ▸ present
      · exact eq.symm ▸ (part.mem_activeRepresentatives b).mpr other
    · simp [CompactMatchingPartition.quotientMate, present] at someMate
  · intro recorded
    obtain ⟨original, active⟩ := Finset.mem_filter.mp recorded
    have aActive := active a (Sym2.mem_mk_left _ _)
    simpa [CompactMatchingPartition.quotientMate, aActive] using state.partialMate_some_iff.mpr original

theorem CompactTopMatching.quotientPerfect {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    (top : CompactTopMatching part) : IsPerfectMatchingOn part.quotientCovered part.quotientEdges := by
  constructor
  · intro e he
    obtain ⟨present, active⟩ := Finset.mem_filter.mp he
    exact ⟨(state.perfect.1 e present).1, fun v member => Finset.mem_inter.mpr
      ⟨(state.perfect.1 e present).2 v member, active v member⟩⟩
  · intro v hv
    obtain ⟨covered, active⟩ := Finset.mem_inter.mp hv
    let w := mateOfMatching state.perfect v
    have edge := mateOfMatching_edge state.perfect covered
    have mate : part.quotientMate v = some w := by
      simp [CompactMatchingPartition.quotientMate, CompactMatchingPrimalDual.partialMate, covered, active, w]
    have existsEdge := top.quotientMate_some.mp mate
    exact ⟨s(v,w), ⟨existsEdge, Sym2.mem_mk_left _ _⟩, fun e h =>
      (state.perfect.2 v covered).unique ⟨(Finset.mem_filter.mp h.1).1, h.2⟩ ⟨edge, Sym2.mem_mk_left _ _⟩⟩




end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentQuotient

/-! matching/MatchingAugmentTopSupport.lean -/
section RppSource_MatchingAugmentTopSupport
namespace VehicleRoutingSurvey.Routing

theorem CompactMatchingPartition.membership_representative {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    {q v : Fin k} (fixed : q ∈ part.activeRepresentatives) :
    v ∈ part.blocks.block q ↔ part.representative v = q := by
  have base := (part.mem_activeRepresentatives q).mp fixed
  constructor
  · intro hv
    exact (part.same_block.mpr (part.blocks.same_of_mem (Finset.mem_univ _) hv)).trans base
  · intro eq
    have same := part.same_block.mp (eq.trans base.symm)
    rw [← same]
    exact part.blocks.self_mem _ (Finset.mem_univ _)

theorem CompactMatchingPartition.topDisjoint {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) :
    (part.activeRepresentatives : Set (Fin k)).PairwiseDisjoint part.blocks.block := by
  intro u hu v hv ne
  apply Finset.disjoint_left.mpr
  intro x xin yin
  exact ne (((part.membership_representative hu).mp xin).symm.trans ((part.membership_representative hv).mp yin))

/-- All vertices of newly matched top-level blocks are covered. A block outside
the augmented quotient matching retains its previous exposed original. -/
theorem CompactMatchingPartition.augmentedSupport {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    {a b : Fin k} (aTop : a ∈ part.activeRepresentatives) (bTop : b ∈ part.activeRepresentatives)
    (port : Fin k → Fin k) (inside : ∀ p ∈ part.activeRepresentatives, port p ∈ part.blocks.block p)
    (stable : ∀ p ∈ part.activeRepresentatives, p ∉ insert a (insert b part.quotientCovered) → port p = p) :
    (part.activeRepresentatives.biUnion (fun p => (part.blocks.block p).erase (port p)) ∪
      (insert a (insert b part.quotientCovered)).image port) = insert a (insert b state.covered) := by
  let active := insert a (insert b part.quotientCovered)
  have onTop {q : Fin k} (h : q ∈ active) : q ∈ part.activeRepresentatives := by
    rcases Finset.mem_insert.mp h with rfl | h
    · exact aTop
    rcases Finset.mem_insert.mp h with rfl | h
    · exact bTop
    · exact (Finset.mem_inter.mp h).2
  ext v
  let q := part.representative v
  have repIn : q ∈ part.activeRepresentatives := (part.mem_activeRepresentatives _).mpr (part.representative_idem v)
  have vIn : v ∈ part.blocks.block q := (part.membership_representative repIn).mpr rfl
  have insideQ : v ∈ state.covered ↔ v ≠ q ∨ q ∈ part.quotientCovered := by
    constructor
    · intro covered
      by_cases same : v = q
      · exact .inr (Finset.mem_inter.mpr ⟨same ▸ covered, repIn⟩)
      · exact .inl same
    · rintro (ne | inQuot)
      · exact part.coveredAway v v (part.blocks.self_mem v (Finset.mem_univ _)) ne
      · by_cases same : v = q
        · exact same.symm ▸ (Finset.mem_inter.mp inQuot).1
        · exact part.coveredAway v v (part.blocks.self_mem v (Finset.mem_univ _)) same
  have shape : v ∈ part.activeRepresentatives.biUnion (fun p => (part.blocks.block p).erase (port p)) ∪ active.image port ↔
      v ≠ port q ∨ q ∈ active := by
    constructor
    · intro h
      rcases Finset.mem_union.mp h with within | atPort
      · obtain ⟨g, hg, hv⟩ := Finset.mem_biUnion.mp within
        have r : q = g := (part.membership_representative hg).mp (Finset.mem_erase.mp hv).2
        exact .inl (r.symm ▸ (Finset.mem_erase.mp hv).1)
      · obtain ⟨g, hg, same⟩ := Finset.mem_image.mp atPort
        have r : part.representative (port g) = g := (part.membership_representative (onTop hg)).mp (inside g (onTop hg))
        have asQ : q = g := (congrArg part.representative same).symm.trans r
        exact .inr (asQ.symm ▸ hg)
    · rintro (different | included)
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨q, repIn, Finset.mem_erase.mpr ⟨different,vIn⟩⟩)
      · by_cases same : v = port q
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, included, same.symm⟩)
        · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨q,repIn,Finset.mem_erase.mpr ⟨same,vIn⟩⟩)
  rw [shape]
  by_cases changed : q ∈ active
  · simp only [changed, or_true, true_iff, Finset.mem_insert]
    by_cases different : v ≠ q
    · exact .inr (.inr (insideQ.mpr (.inl different)))
    · have eq := not_ne_iff.mp different
      change q ∈ insert a (insert b part.quotientCovered) at changed
      rcases Finset.mem_insert.mp changed with ra | rest
      · exact .inl (eq.trans ra)
      rcases Finset.mem_insert.mp rest with rb | old
      · exact .inr (.inl (eq.trans rb))
      · exact .inr (.inr (insideQ.mpr (.inr old)))
  · have frozen := stable q repIn changed
    have old : q ∉ part.quotientCovered := fun h => changed (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have na : v ≠ a := by
      intro eq
      have r : q = a := (congrArg part.representative eq).trans ((part.mem_activeRepresentatives _).mp aTop)
      exact changed (Finset.mem_insert.mpr (.inl r))
    have nb : v ≠ b := by
      intro eq
      have r : q = b := (congrArg part.representative eq).trans ((part.mem_activeRepresentatives _).mp bTop)
      exact changed (Finset.mem_insert.mpr (.inr (Finset.mem_insert.mpr (.inl r))))
    simp only [frozen, changed, or_false, Finset.mem_insert, na, nb, false_or, insideQ, old]


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentTopSupport

/-! matching/MatchingAugmentInitialCapacity.lean -/
section RppSource_MatchingAugmentInitialCapacity
namespace VehicleRoutingSurvey.Routing

theorem matchingAugmentTopTask_shape {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (cycles : MatchingLiveCycles registry) (p : Fin k) {task : MatchingRebaseTask}
    (emits : matchingAugmentTopTask cycles p = some task) :
    (MatchingMemberTree.blossom 0 task.node task.children .nil).proper ∧ task.children.leaves.Nodup ∧
      task.registryIds = (registry.trees.tree (part.representative p)).registryIds ∧
      ∀ v ∈ task.children.leaves, ∃ h : v < k, part.representative ⟨v,h⟩ = part.representative p := by
  let q := part.representative p
  let B := part.blocks.block q
  have fixed : part.representative q = q := part.representative_idem p
  have top := (part.mem_activeRepresentatives _).mpr fixed
  by_cases big : B.card ≠ 1
  · let hb := part.blocks.cut_mem (Finset.mem_univ q) big
    let e := cycles.entry B hb
    have someTask : matchingAugmentTopTask cycles p = some ⟨dual.node B,p.val,e.tree⟩ := dif_pos big
    have eq := Option.some.inj (someTask.symm.trans emits)
    subst task
    have members := (cycles.memory B hb).members
    have tree := (cycles.top q hb fixed).2
    refine ⟨by simpa [matchingRebaseNodeState] using members.proper, members.unique, ?_, ?_⟩
    · rw [tree]
      simp [MatchingRebaseTask.registryIds, MatchingMemberTree.registryIds, B, e]
    · intro v leaf
      have bounded := members.valid v leaf
      have h : v < k := by simpa [matchingRebaseNodeState,dual.dimension] using bounded
      exact ⟨h,(part.membership_representative top).mp ((e.leaves_iff ⟨v,h⟩).mp leaf)⟩
  · have none : matchingAugmentTopTask cycles p = none := dif_neg big
    rw [none] at emits
    cases emits

/-- The semantic tasks decoded from the actual request array use at most
one slot of credit per original, with no duplicate original or registry ID. -/
theorem matchingAugmentInitialTasks_capacity {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (cycles : MatchingLiveCycles registry) (ports : List (Fin k))
    (unique : (ports.map part.representative).Nodup) :
    let tasks := ports.filterMap (matchingAugmentTopTask cycles)
    (matchingRebaseTaskLeaves tasks).Nodup ∧ (matchingRebaseQueueIds tasks).Nodup ∧
      (∀ n ∈ matchingRebaseQueueIds tasks, 0 < n ∧ n < s.nr 76) ∧ matchingRebaseQueueWork tasks ≤ k := by
  intro tasks
  let rep := part.representative
  let ids (q : Fin k) := (registry.trees.tree q).registryIds
  have sources : (ports.map rep).Subperm (List.finRange k) :=
    List.subperm_of_subset unique (fun q _ => List.mem_finRange q)
  have retained (xs : List (Fin k)) :
      (matchingRebaseQueueIds (xs.filterMap (matchingAugmentTopTask cycles))).Sublist ((xs.map rep).flatMap ids) := by
    induction xs with
    | nil => exact .slnil
    | cons p rest ih =>
      cases eq : matchingAugmentTopTask cycles p with
      | none =>
        simpa [eq] using ih.trans (List.sublist_append_right (ids (rep p)) ((rest.map rep).flatMap ids))
      | some t =>
        have id : t.registryIds = ids (rep p) := (matchingAugmentTopTask_shape cycles p eq).2.2.1
        simpa only [List.filterMap_cons, eq, matchingRebaseQueueIds, List.flatMap_cons, List.map_cons, id] using
          ih.append_left (ids (rep p))
  obtain ⟨ordered, perm, sub⟩ := List.subperm_iff.mp sources
  have contained : (matchingRebaseQueueIds tasks).Subperm registry.trees.registryIds :=
    List.subperm_iff.mpr ⟨ordered.flatMap ids, perm.flatMap_right _, (retained ports).trans (sub.flatMap ids)⟩
  obtain ⟨orderedIds, permIds, subIds⟩ := List.subperm_iff.mp contained
  have distinctIds := subIds.nodup (permIds.nodup_iff.mpr registry.unique)
  have account (xs : List (Fin k)) {v : ℕ} (leaf : v ∈ matchingRebaseTaskLeaves (xs.filterMap (matchingAugmentTopTask cycles))) :
      ∃ h : v < k, rep ⟨v,h⟩ ∈ xs.map rep := by
    obtain ⟨t, ht, within⟩ := List.mem_flatMap.mp leaf
    obtain ⟨p, hp, found⟩ := List.mem_filterMap.mp ht
    obtain ⟨bound,tag⟩ := (matchingAugmentTopTask_shape cycles p found).2.2.2 v within
    exact ⟨bound,List.mem_map.mpr ⟨p,hp,tag.symm⟩⟩
  have leaves (xs : List (Fin k)) (separate : (xs.map rep).Nodup) :
      (matchingRebaseTaskLeaves (xs.filterMap (matchingAugmentTopTask cycles))).Nodup := by
    induction xs with
    | nil => simp [matchingRebaseTaskLeaves]
    | cons p rest ih =>
      obtain ⟨fresh, tail⟩ := List.nodup_cons.mp separate
      have old := ih tail
      cases eq : matchingAugmentTopTask cycles p with
      | none => simpa [eq] using old
      | some t =>
        have shape := matchingAugmentTopTask_shape cycles p eq
        simp only [List.filterMap_cons,eq,matchingRebaseTaskLeaves,List.flatMap_cons]
        refine List.nodup_append.mpr ⟨shape.2.1,old,?_⟩
        intro a ha b hb same
        obtain ⟨h,tag⟩ := shape.2.2.2 a ha
        obtain ⟨j,taken⟩ := account rest (same.symm ▸ hb)
        have eqRep : rep ⟨a,j⟩ = rep p := tag
        rw [eqRep] at taken
        exact fresh taken
  have distinct := leaves ports unique
  have range : (matchingRebaseTaskLeaves tasks).toFinset ⊆ Finset.range k := by
    intro n hn
    exact Finset.mem_range.mpr (account ports (List.mem_toFinset.mp hn)).choose
  have capacity : (matchingRebaseTaskLeaves tasks).length ≤ k := by
    have noDuplicates : (matchingRebaseTaskLeaves tasks).Nodup := distinct
    rw [← List.toFinset_card_of_nodup noDuplicates]
    exact (Finset.card_le_card range).trans_eq (Finset.card_range k)
  refine ⟨distinct,distinctIds,?_,(matchingRebaseQueueWork_le_leaves tasks ?_).trans capacity⟩
  · intro n hn
    obtain ⟨B,hb,eq⟩ := (registry.keys n).mp (contained.subset hn)
    exact eq ▸ And.intro (Nat.pos_of_ne_zero (dual.nodeNonzero B hb)) (registry.allocated B hb)
  · intro task ht
    obtain ⟨port,hp,found⟩ := List.mem_filterMap.mp ht
    exact (matchingAugmentTopTask_shape cycles port found).1


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentInitialCapacity

/-! matching/MatchingAugmentBlockLifts.lean -/
section RppSource_MatchingAugmentBlockLifts
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

theorem CompactTopMatching.internal_avoids_base {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    (top : CompactTopMatching part) {p : Fin k} (fixed : part.representative p = p)
    {e : Sym2 (Fin k)} (used : e ∈ state.edges) (inside : ∀ v ∈ e, v ∈ part.blocks.block p) : p ∉ e := by
  induction e using Sym2.inductionOn with
  | hf a b =>
    intro atPort
    rcases Sym2.mem_iff.mp atPort with eq | eq
    · subst a
      have outside := top.matchedBase fixed (state.partialMate_some_iff.mpr used)
      exact outside (part.blocks.same_of_mem (Finset.mem_univ _) (inside b (Sym2.mem_mk_right _ _))).symm
    · subst b
      have outside := top.matchedBase fixed (state.partialMate_some_iff.mpr (Sym2.eq_swap ▸ used))
      exact outside (part.blocks.same_of_mem (Finset.mem_univ _) (inside a (Sym2.mem_mk_left _ _))).symm

/-- A top block on the alternating path receives its recursive lifted edges.
Every other top block keeps exactly its old internal edges in the new primal. -/
theorem matchingAugmentBlockLifts {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    {part : CompactMatchingPartition state} {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (cycles : MatchingLiveCycles registry) (top : CompactTopMatching part) (oldCuts : state.InternalCuts)
    (touched : Finset (Fin k)) (port : Fin k → Fin k)
    (atPort : ∀ q ∈ part.activeRepresentatives, port q ∈ part.blocks.block q)
    (untouched : ∀ q ∉ touched, port q = q) :
    ∃ inner : Fin k → Finset (Sym2 (Fin k)), ∀ q ∈ part.activeRepresentatives,
      let B := part.blocks.block q
      IsPerfectMatchingOn (B.erase (port q)) (inner q) ∧
      (∀ edge ∈ inner q, matchingLiftTight state edge) ∧
      (∀ D ∈ state.cuts, D ⊆ B → ∃ p ∈ D, ∀ v ∈ D, v ≠ p →
        ∃ e ∈ inner q, v ∈ e ∧ ∀ w ∈ e, w ∈ D) ∧
      (q ∉ touched → inner q = matchingCycleInterior state B q) ∧
      (q ∈ touched → B.card ≠ 1 → MatchingCycleLiftDerivation cycles.entry B (port q) (inner q)) := by
  classical
  let value (q : Fin k) : Finset (Sym2 (Fin k)) :=
    if old : q ∉ touched then matchingCycleInterior state (part.blocks.block q) q
    else if (part.blocks.block q).card = 1 then ∅
    else if existsLift : ∃ edges, MatchingCutLift cycles.entry (part.blocks.block q) (port q) edges
      then existsLift.choose else ∅
  refine ⟨value, ?_⟩
  intro q current
  let B := part.blocks.block q
  have fixed := (part.mem_activeRepresentatives _).mp current
  have picked := atPort q current
  by_cases single : B.card = 1
  · obtain ⟨x, alone⟩ := Finset.card_eq_one.mp single
    have idPort : port q = x := Finset.mem_singleton.mp (alone ▸ picked)
    have idBase : q = x := Finset.mem_singleton.mp (alone ▸ (part.blocks.self_mem q (Finset.mem_univ _)))
    have noEdge : matchingCycleInterior state B q = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      induction e using Sym2.inductionOn with
      | hf a b =>
        have within := (Finset.mem_filter.mp he).2 a (Sym2.mem_mk_left _ _)
        simpa [alone, idBase] using within
    have noValue : value q = ∅ := by
      dsimp only [value]
      by_cases old : q ∉ touched
      · rw [dif_pos old]; exact noEdge
      · rw [dif_neg old, if_pos single]
    refine ⟨?_, ?_, ?_, fun _ => noValue.trans noEdge.symm, fun _ no => (no single).elim⟩
    · rw [noValue]
      change IsPerfectMatchingOn (B.erase (port q)) ∅
      simp [alone,idPort,IsPerfectMatchingOn]
    · simp [noValue]
    · intro D hd sub
      have a : D.card ≤ 1 := (Finset.card_le_card sub).trans (le_of_eq single)
      have b := registry.nontrivial D hd
      omega
  · have live := part.blocks.cut_mem (Finset.mem_univ q) single
    by_cases old : q ∉ touched
    · have remains : value q = matchingCycleInterior state B q := dif_pos old
      have fixedPort := untouched q old
      obtain ⟨base, _⟩ := cycles.top q live fixed
      have near := (cycles.entry B live).internal
      rw [base] at near
      refine ⟨?_, ?_, ?_, fun _ => remains, fun h => (old h).elim⟩
      · rw [fixedPort, remains]; exact near
      · intro edge present
        exact state.tight _ (Finset.mem_filter.mp (remains ▸ present)).1
      · intro D dLive below
        obtain ⟨p, hp, localEdges⟩ := oldCuts D dLive
        refine ⟨p, hp, ?_⟩
        intro v hv nv
        obtain ⟨e, he, atV, inD⟩ := localEdges v hv nv
        have inB : ∀ w ∈ e, w ∈ B := fun w hw => below (inD w hw)
        have away := top.internal_avoids_base fixed he inB
        rw [remains]
        exact ⟨e, Finset.mem_filter.mpr ⟨he, fun w hw => Finset.mem_erase.mpr
          ⟨fun eq => away (eq ▸ hw), inB w hw⟩⟩, atV, inD⟩
    · have existsLift := matchingCutLift_exists cycles.entry registry.nontrivial B live (port q) picked
      have lifted : MatchingCutLift cycles.entry B (port q) (value q) := by
        dsimp only [value]
        rw [dif_neg old, if_neg single, dif_pos existsLift]
        exact existsLift.choose_spec
      exact ⟨lifted.perfect, lifted.tight, lifted.cuts, fun h => (old h).elim, fun _ _ => lifted.actual⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentBlockLifts

/-! matching/MatchingAugmentLiftedState.lean -/
section RppSource_MatchingAugmentLiftedState
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

structure MatchingAugmentedPrimal {k : ℕ} {cost : Fin k → Fin k → ℝ} {old : CompactMatchingPrimalDual k cost}
    (part : CompactMatchingPartition old) (a b : Fin k) (port : Fin k → Fin k)
    (inner : Fin k → Finset (Sym2 (Fin k))) (quotient : Finset (Sym2 (Fin k))) where
  next : CompactMatchingPrimalDual k cost
  covered : next.covered = insert a (insert b old.covered)
  edges : next.edges = liftMatchingAcrossBlocks part.activeRepresentatives inner (quotient.image (Sym2.map port))
  eachBlock : ∀ q ∈ part.activeRepresentatives, IsPerfectMatchingOn ((part.blocks.block q).erase (port q)) (inner q)
  increased : next.edges.card = old.edges.card + 1
  cuts : next.cuts = old.cuts
  potential : next.potential = old.potential
  cutDual : next.cutDual = old.cutDual
  allCuts : next.InternalCuts
  partition : CompactMatchingPartition next
  blocks : partition.blocks.block = part.blocks.block
  representatives : partition.representative = port ∘ part.representative
  top : CompactTopMatching partition

/-- Lift an augmented quotient matching, with the recorded original crossings
and recursive internal matchings, to the primal and partition of the next stage. -/
noncomputable def matchingAugmentLiftedState {k : ℕ} {cost : Fin k → Fin k → ℝ} {old : CompactMatchingPrimalDual k cost}
    (part : CompactMatchingPartition old) (a b : Fin k)
    (aTop : a ∈ part.activeRepresentatives) (bTop : b ∈ part.activeRepresentatives)
    (aFree : a ∉ old.covered) (bFree : b ∉ old.covered) (different : a ≠ b)
    (port : Fin k → Fin k) (inside : ∀ p ∈ part.activeRepresentatives, port p ∈ part.blocks.block p)
    (stable : ∀ p ∈ part.activeRepresentatives, p ∉ insert a (insert b part.quotientCovered) → port p = p)
    (quotient : Finset (Sym2 (Fin k)))
    (cross : IsPerfectMatchingOn (insert a (insert b part.quotientCovered)) quotient)
    (crossTight : ∀ e ∈ quotient, matchingLiftTight old (Sym2.map port e))
    (inner : Fin k → Finset (Sym2 (Fin k)))
    (internal : ∀ p ∈ part.activeRepresentatives, IsPerfectMatchingOn ((part.blocks.block p).erase (port p)) (inner p))
    (tight : ∀ p ∈ part.activeRepresentatives, ∀ e ∈ inner p, matchingLiftTight old e)
    (cuts : ∀ p ∈ part.activeRepresentatives, ∀ D ∈ old.cuts, D ⊆ part.blocks.block p →
      ∃ v ∈ D, ∀ w ∈ D, w ≠ v → ∃ e ∈ inner p, w ∈ e ∧ ∀ z ∈ e, z ∈ D)
    (nested : ∀ D ∈ old.cuts, ∀ u ∈ D, ∀ v ∈ D, part.blocks.block u = part.blocks.block v) :
    MatchingAugmentedPrimal part a b port inner quotient := by
  classical
  let groups := part.activeRepresentatives
  let active := insert a (insert b part.quotientCovered)
  let edges := liftMatchingAcrossBlocks groups inner (quotient.image (Sym2.map port))
  have sub : active ⊆ groups := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact aTop
    rcases Finset.mem_insert.mp hq with rfl | oldQ
    · exact bTop
    · exact (Finset.mem_inter.mp oldQ).2
  have label {q : Fin k} (hq : q ∈ groups) : part.representative (port q) = q :=
    (part.membership_representative hq).mp (inside q hq)
  have inj : Set.InjOn port (active : Set (Fin k)) := by
    intro p hp q hq eq
    exact (label (sub hp)).symm.trans ((congrArg part.representative eq).trans (label (sub hq)))
  have lifted := liftMatchingAcrossBlocks_spec groups active sub part.blocks.block port inner _
    part.topDisjoint inside internal (perfectMatching_map_ports cross port inj) (matchingLiftTight old) tight
    (fun e h => by obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h; exact crossTight x hx)
  have perfect : IsPerfectMatchingOn (insert a (insert b old.covered)) edges :=
    (part.augmentedSupport aTop bTop port inside stable) ▸ lifted.1
  have all {D : Finset (Fin k)} (hd : D ∈ old.cuts) : ∃ p ∈ D, ∀ v ∈ D, v ≠ p →
      ∃ e ∈ edges, v ∈ e ∧ ∀ w ∈ e, w ∈ D := by
    have nonempty : D.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simpa using (old.cutValid _ hd).1
    obtain ⟨u, hu⟩ := nonempty
    let q := part.representative u
    have fixed : q ∈ groups := (part.mem_activeRepresentatives _).mpr (part.representative_idem u)
    have within : D ⊆ part.blocks.block q := by
      intro v hv
      apply (part.membership_representative fixed).mpr
      exact part.constant _ _ (nested D hd v hv u hu)
    obtain ⟨p, hp, covered⟩ := cuts q fixed D hd within
    refine ⟨p, hp, ?_⟩
    intro v hv diff
    obtain ⟨e, he, atV, allE⟩ := covered v hv diff
    exact ⟨e, Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨q, fixed, he⟩), atV, allE⟩
  let next : CompactMatchingPrimalDual k cost := {
    covered := insert a (insert b old.covered)
    edges := edges
    perfect := perfect
    cuts := old.cuts
    potential := old.potential
    cutDual := old.cutDual
    cutValid := old.cutValid
    feasible := old.feasible
    tight := lifted.2.1
    internal := fun _ hd _ => all hd }
  have groupRep (v : Fin k) : part.representative v ∈ groups :=
    (part.mem_activeRepresentatives _).mpr (part.representative_idem v)
  have blockRep (v : Fin k) : part.blocks.block (part.representative v) = part.blocks.block v :=
    part.blocks.same_of_mem (Finset.mem_univ _) (part.inside v)
  have interior (v w : Fin k) (hw : w ∈ part.blocks.block v) (diff : w ≠ port (part.representative v)) :
      ∃ e ∈ edges, w ∈ e ∧ ∀ z ∈ e, z ∈ part.blocks.block v := by
    have h := lifted.2.2 _ (groupRep v)
    rw [blockRep] at h
    exact h w hw diff
  let partition : CompactMatchingPartition next := {
    blocks := part.blocks
    representative := port ∘ part.representative
    inside := fun v => (blockRep v) ▸ inside _ (groupRep v)
    constant := fun v w h => congrArg port (part.constant v w h)
    coveredAway := fun v w hw diff => by
      obtain ⟨e, he, atW, _⟩ := interior v w hw diff
      exact (perfect.1 e he).2 w atW }
  have top : CompactTopMatching partition := by
    refine ⟨interior, ?_⟩
    intro v w fixed paired same
    have he : s(v,w) ∈ edges := next.partialMate_some_iff.mp paired
    rcases Finset.mem_union.mp he with within | crossing
    · obtain ⟨q, hq, ve⟩ := Finset.mem_biUnion.mp within
      obtain ⟨away, inQ⟩ := Finset.mem_erase.mp ((internal q hq).1 _ ve |>.2 v (Sym2.mem_mk_left _ _))
      have rep := (part.membership_representative hq).mp inQ
      exact away (fixed.symm.trans (congrArg port rep))
    · obtain ⟨e, present, eq⟩ := Finset.mem_image.mp crossing
      induction e using Sym2.inductionOn with
      | hf x y =>
        have ends := (cross.1 _ present).2
        have origX := label (sub (ends x (Sym2.mem_mk_left _ _)))
        have origY := label (sub (ends y (Sym2.mem_mk_right _ _)))
        have ne := (cross.1 _ present).1
        change s(port x, port y) = s(v,w) at eq
        change part.blocks.block v = part.blocks.block w at same
        have sameRep := part.same_block.mpr same
        rcases Sym2.eq_iff.mp eq with direct | reverse
        · exact ne (Sym2.mk_isDiag_iff.mpr (origX.symm.trans ((congrArg part.representative direct.1).trans
            (sameRep.trans ((congrArg part.representative direct.2).symm.trans origY)))))
        · exact ne (Sym2.mk_isDiag_iff.mpr (origX.symm.trans ((congrArg part.representative reverse.1).trans
            (sameRep.symm.trans ((congrArg part.representative reverse.2).symm.trans origY)))))
  have count := perfectMatching_card_twice perfect
  have fresh : a ∉ insert b old.covered := by simpa [different] using aFree
  rw [Finset.card_insert_of_notMem fresh, Finset.card_insert_of_notMem bFree, perfectMatching_card_twice old.perfect] at count
  refine ⟨next, rfl, rfl, internal, ?_, rfl, rfl, rfl, fun _ h => all h, partition, rfl, rfl, top⟩
  change edges.card = old.edges.card + 1
  omega


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentLiftedState

/-! matching/MatchingAugmentPortTable.lean -/
section RppSource_MatchingAugmentPortTable
namespace VehicleRoutingSurvey.Routing

private theorem matchingAugmentPortFold {k : ℕ} (rows : List (Fin k × Fin k)) (rep start : Fin k → Fin k) :
    rows.foldl (chooseAugmentationRepresentatives rep) start =
      (selectedAugmentationPorts rows).foldl (fun acc p => Function.update acc (rep p) p) start := by
  induction rows generalizing start with
  | nil => rfl
  | cons h t ih =>
    change t.foldl _ (Function.update (Function.update start (rep h.1) h.1) (rep h.2) h.2) = _
    exact ih _

private theorem matchingAugmentPortFold_meaning {k : ℕ} (ports : List (Fin k)) (rep start : Fin k → Fin k)
    (unique : (ports.map rep).Nodup) :
    let next := ports.foldl (fun acc p => Function.update acc (rep p) p) start
    (∀ p ∈ ports, next (rep p) = p) ∧ ∀ q ∉ ports.map rep, next q = start q := by
  induction ports generalizing start with
  | nil => simp
  | cons p tail ih =>
    obtain ⟨fresh, distinct⟩ := List.nodup_cons.mp unique
    obtain ⟨present, unchanged⟩ := ih (Function.update start (rep p) p) distinct
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | later
      · exact (unchanged _ fresh).trans (Function.update_self ..)
      · exact present v later
    · intro q outside
      have diff : q ≠ rep p := fun eq => outside (eq.symm ▸ List.mem_cons_self ..)
      have missing : q ∉ tail.map rep := fun h => outside (List.mem_cons_of_mem _ h)
      exact (unchanged _ missing).trans (Function.update_of_ne diff _ _)

/-- The actual representative remap chooses the recorded original on each
selected block and fixes every top representative outside the path. -/
theorem matchingAugmentationNewPorts {k : ℕ} (rows : List (Fin k × Fin k)) (rep : Fin k → Fin k)
    (unique : ((selectedAugmentationPorts rows).map rep).Nodup) :
    let next := rows.foldl (chooseAugmentationRepresentatives rep) id
    (∀ p ∈ selectedAugmentationPorts rows, next (rep p) = p) ∧
      ∀ q ∉ (selectedAugmentationPorts rows).map rep, next q = q := by
  rw [matchingAugmentPortFold]
  exact matchingAugmentPortFold_meaning _ _ _ unique

theorem matchingAugmentationNewPort_inBlock {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (rows : List (Fin k × Fin k)) (unique : ((selectedAugmentationPorts rows).map part.representative).Nodup)
    (q : Fin k) :
    (rows.foldl (chooseAugmentationRepresentatives part.representative) id) q ∈ part.blocks.block q := by
  have port := matchingAugmentationNewPorts rows part.representative unique
  by_cases found : q ∈ (selectedAugmentationPorts rows).map part.representative
  · obtain ⟨v, hv, eq⟩ := List.mem_map.mp found
    rw [← eq, port.1 v hv]
    have same := part.blocks.same_of_mem (Finset.mem_univ v) (part.inside v)
    rw [same]
    exact part.blocks.self_mem _ (Finset.mem_univ _)
  · rw [port.2 q found]
    exact part.blocks.self_mem _ (Finset.mem_univ _)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentPortTable

/-! matching/MatchingAugmentOutsidePair.lean -/
section RppSource_MatchingAugmentOutsidePair
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- An original whose new incident edges were all old edges retains its
precise mate word, including the sentinel when it remains uncovered. -/
theorem compactPrimalMateWord_unchanged {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (old next : CompactMatchingPrimalDual k cost) {v : Fin k} (included : old.covered ⊆ next.covered)
    (preserved : ∀ e ∈ next.edges, v ∈ e → e ∈ old.edges) :
    compactPrimalMateWord next v.val = compactPrimalMateWord old v.val := by
  by_cases covered : v ∈ next.covered
  · have matched := mateOfMatching_edge next.perfect covered
    exact (compactPrimalMateWord_of_edge next matched).1.trans
      (compactPrimalMateWord_of_edge old (preserved _ matched (Sym2.mem_mk_left _ _))).1.symm
  · have absent : v ∉ old.covered := fun h => covered (included h)
    simp [compactPrimalMateWord, v.isLt, covered, absent]

theorem MatchingAugmentedPrimal.outsideMate {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {a b : Fin k} {port : Fin k → Fin k} {inner : Fin k → Finset (Sym2 (Fin k))}
    {quotient : Finset (Sym2 (Fin k))} (lift : MatchingAugmentedPrimal part a b port inner quotient)
    (rows : List (Fin k × Fin k)) (v : Fin k)
    (unselected : part.representative v ∉ (selectedAugmentationPorts rows).map part.representative)
    (keep : inner (part.representative v) = matchingCycleInterior old (part.blocks.block (part.representative v)) (part.representative v))
    (crossing : ∀ e ∈ quotient.image (Sym2.map port), e ∈ old.edges ∨ ∃ p ∈ rows, e = s(p.1,p.2)) :
    compactPrimalMateWord lift.next v.val = compactPrimalMateWord old v.val := by
  apply compactPrimalMateWord_unchanged _ _ (fun u h => lift.covered.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  intro e he atV
  rw [lift.edges] at he
  rcases Finset.mem_union.mp he with innerEdge | crossEdge
  · obtain ⟨q, hq, localEdge⟩ := Finset.mem_biUnion.mp innerEdge
    have key := (part.membership_representative hq).mp
      (Finset.mem_erase.mp (((lift.eachBlock q hq).1 e localEdge).2 v atV)).2
    rw [← key, keep] at localEdge
    exact (Finset.mem_filter.mp localEdge).1
  · rcases crossing e crossEdge with retained | ⟨p,hp,rfl⟩
    · exact retained
    · have vIn : v ∈ selectedAugmentationPorts rows := List.mem_flatMap.mpr ⟨p,hp,by
        rcases Sym2.mem_iff.mp atV with hv | hv <;> simp [hv]⟩
      exact (unselected (List.mem_map.mpr ⟨v,vIn,rfl⟩)).elim

private theorem installMatePairFold_outside {k : ℕ} (rows : List (Fin k × Fin k)) (base : ℕ)
    (m : ℕ → ℕ) (v : Fin k) (away : v ∉ selectedAugmentationPorts rows) :
    rows.foldl (installMatePair base) m (base+v.val) = m (base+v.val) := by
  induction rows generalizing m with
  | nil => rfl
  | cons p rest ih =>
    change v ∉ p.1 :: p.2 :: selectedAugmentationPorts rest at away
    simp only [List.mem_cons, not_or] at away
    have first : base+v.val ≠ base+p.1.val := fun eq => away.1 (Fin.ext (Nat.add_left_cancel eq))
    have second : base+v.val ≠ base+p.2.val := fun eq => away.2.1 (Fin.ext (Nat.add_left_cancel eq))
    exact (ih _ away.2.2).trans (by simp [installMatePair,Function.update_of_ne first,Function.update_of_ne second])

theorem installMatePairFold_row {k : ℕ} (rows : List (Fin k × Fin k)) (rep : Fin k → Fin k) (base : ℕ)
    (m : ℕ → ℕ) (unique : ((selectedAugmentationPorts rows).map rep).Nodup) (p : Fin k × Fin k) (hp : p ∈ rows) :
    let out := rows.foldl (installMatePair base) m
    out (base+p.1.val) = p.2.val ∧ out (base+p.2.val) = p.1.val := by
  induction rows generalizing m with
  | nil => simp at hp
  | cons first later ih =>
    change (rep first.1 :: rep first.2 :: (selectedAugmentationPorts later).map rep).Nodup at unique
    obtain ⟨newLeft,rightUnique⟩ := List.nodup_cons.mp unique
    obtain ⟨newRight,remaining⟩ := List.nodup_cons.mp rightUnique
    rcases List.mem_cons.mp hp with same | after
    · subst p
      have l : first.1 ∉ selectedAugmentationPorts later := fun h => newLeft (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_,h,rfl⟩))
      have r : first.2 ∉ selectedAugmentationPorts later := fun h => newRight (List.mem_map.mpr ⟨_,h,rfl⟩)
      have diff : base+first.1.val ≠ base+first.2.val := fun h =>
        newLeft (List.mem_cons.mpr (.inl (congrArg rep (Fin.ext (Nat.add_left_cancel h)))))
      let installed := installMatePair base m first
      change (later.foldl (installMatePair base) installed) (base+first.1.val) = first.2.val ∧
        (later.foldl (installMatePair base) installed) (base+first.2.val) = first.1.val
      rw [installMatePairFold_outside later base _ _ l, installMatePairFold_outside later base _ _ r]
      simp [installed, installMatePair,Function.update_of_ne diff]
    · exact ih _ remaining after

/-- The only originals whose mate word still needs work are interiors of
the queued selected nontrivial blocks. Every selected original already
has its crossing mate installed by the actual row loop. -/
theorem AugmentationPreRebaseReady.boundaryOfRows {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {s t : ArithmeticState}
    {rows : List (Fin k × Fin k)} (ready : AugmentationPreRebaseReady rows s t)
    (layout : AugmentationInstallLayout k (augmentationCrossingSeed s k)) (rep : Fin k → Fin k)
    (original : ∀ v : Fin k, s.nm (s.nr 57+v.val) = (rep v).val)
    (mates : ∀ v : Fin k, s.nm (s.nr 50+v.val) = compactPrimalMateWord old v.val)
    (unique : ((selectedAugmentationPorts rows).map rep).Nodup)
    (crossing : ∀ p ∈ rows, s(p.1,p.2) ∈ next.edges) (jobs : List MatchingRebaseTask)
    (accounted : ∀ v : Fin k, v ∉ selectedAugmentationPorts rows → (∀ j ∈ jobs, ¬j.needs v.val) →
      compactPrimalMateWord next v.val = compactPrimalMateWord old v.val) :
    ∀ v : Fin k, (∀ j ∈ jobs, ¬j.needs v.val) → t.nm (s.nr 50+v.val) = compactPrimalMateWord next v.val := by
  intro v closed
  rw [(ready.typedTables layout rep original).1 v]
  by_cases touched : v ∈ selectedAugmentationPorts rows
  · obtain ⟨p, hp, whereAt⟩ := List.mem_flatMap.mp touched
    have result := installMatePairFold_row rows rep (s.nr 50) s.nm unique p hp
    have target := compactPrimalMateWord_of_edge next (crossing p hp)
    rcases List.mem_cons.mp whereAt with x | rest
    · exact x.symm ▸ result.1.trans target.1.symm
    · have x : v = p.2 := List.mem_singleton.mp rest
      exact x.symm ▸ result.2.trans target.2.symm
  · exact (installMatePairFold_outside rows _ _ _ touched).trans ((mates v).trans (accounted v touched closed).symm)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentOutsidePair

/-! matching/MatchingAugmentInitialBoundary.lean -/
section RppSource_MatchingAugmentInitialBoundary
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

theorem matchingAugmentInitialTasks_cover {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (cycles : MatchingLiveCycles registry) (selected : List (Fin k)) (v : Fin k)
    (away : v ∉ selected)
    (closed : ∀ task ∈ selected.filterMap (matchingAugmentTopTask cycles), ¬task.needs v.val) :
    part.representative v ∉ selected.map part.representative := by
  intro hit
  obtain ⟨p, hp, eq⟩ := List.mem_map.mp hit
  let q := part.representative p
  let B := part.blocks.block q
  have current : q ∈ part.activeRepresentatives := (part.mem_activeRepresentatives _).mpr (part.representative_idem p)
  have vp : v ∈ B := (part.membership_representative current).mpr eq.symm
  have pp : p ∈ B := (part.membership_representative current).mpr rfl
  have ne : v ≠ p := fun same => away (same.symm ▸ hp)
  by_cases big : B.card ≠ 1
  · let present := part.blocks.cut_mem (Finset.mem_univ q) big
    let entry := cycles.entry B present
    let task : MatchingRebaseTask := ⟨dual.node B,p.val,entry.tree⟩
    have yes : matchingAugmentTopTask cycles p = some task := dif_pos big
    exact closed task (List.mem_filterMap.mpr ⟨p,hp,yes⟩)
      ⟨(entry.leaves_iff v).mpr vp,fun same => ne (Fin.ext same)⟩
  · obtain ⟨x,rfl'⟩ := Finset.card_eq_one.mp (not_ne_iff.mp big)
    exact ne ((Finset.mem_singleton.mp (rfl' ▸ vp)).trans (Finset.mem_singleton.mp (rfl' ▸ pp)).symm)

/-- Each emitted task is backed by its old top block's lifted derivation
and requests exactly the port selected by the new global primal. -/
theorem matchingAugmentInitialTasks_planned {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {s base : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (cycles : MatchingLiveCycles registry) (full : MatchingRebaseArchive base)
    (archived : ∀ B (h : B ∈ old.cuts), full.live (dual.node B) (cycles.entry B h).tree)
    (rows : List (Fin k × Fin k)) (unique : ((selectedAugmentationPorts rows).map part.representative).Nodup)
    {start finish : Fin k} {inner : Fin k → Finset (Sym2 (Fin k))} {quotient : Finset (Sym2 (Fin k))}
    (lift : MatchingAugmentedPrimal part start finish (rows.foldl (chooseAugmentationRepresentatives part.representative) id) inner quotient)
    (derived : ∀ p ∈ part.activeRepresentatives, p ∈ (selectedAugmentationPorts rows).map part.representative →
      (part.blocks.block p).card ≠ 1 → MatchingCycleLiftDerivation cycles.entry (part.blocks.block p)
      ((rows.foldl (chooseAugmentationRepresentatives part.representative) id) p) (inner p)) :
    let target := matchingAugmentDerivedArchive (next := lift.next) cycles full archived
    ∀ task ∈ (selectedAugmentationPorts rows).filterMap (matchingAugmentTopTask cycles),
      target.live task.node task.children ∧ task.port ∈ task.children.leaves ∧
      task.port = matchingAugmentNodePort lift.next old.cuts dual.node task.node := by
  intro target task listed
  obtain ⟨v,hv,eq⟩ := List.mem_filterMap.mp listed
  let q := part.representative v
  let B := part.blocks.block q
  let port := rows.foldl (chooseAugmentationRepresentatives part.representative) id
  have selected := (matchingAugmentationNewPorts rows part.representative unique).1 _ hv
  have current : q ∈ part.activeRepresentatives := (part.mem_activeRepresentatives _).mpr (part.representative_idem v)
  have vIn : v ∈ B := (part.membership_representative current).mpr rfl
  by_cases big : B.card ≠ 1
  · let hb := part.blocks.cut_mem (Finset.mem_univ q) big
    let entry := cycles.entry B hb
    have correct : (⟨dual.node B,v.val,entry.tree⟩ : MatchingRebaseTask) = task :=
      Option.some.inj ((show matchingAugmentTopTask cycles v = some ⟨dual.node B,v.val,entry.tree⟩ from dif_pos big).symm.trans eq)
    subst task
    have inside : inner q ⊆ lift.next.edges := by
      rw [lift.edges]
      exact fun e he => Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨q,current,he⟩)
    have matching : IsPerfectMatchingOn (B.erase v) (inner q) := selected ▸ lift.eachBlock q current
    have liftV : MatchingCycleLiftDerivation cycles.entry B v (inner q) :=
      selected ▸ derived _ current (List.mem_map.mpr ⟨v,hv,rfl⟩) big
    exact ⟨⟨B,hb,rfl,rfl,v,vIn,inner q,inside,liftV⟩,(entry.leaves_iff v).mpr vIn,
      (matchingAugmentNodePort_eq lift.next dual.nodeInjective hb vIn matching inside).symm⟩
  · have none : matchingAugmentTopTask cycles v = none := dif_neg big
    rw [none] at eq
    cases eq


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentInitialBoundary

/-! matching/MatchingAugmentPreparedPrimal.lean -/
section RppSource_MatchingAugmentPreparedPrimal
namespace VehicleRoutingSurvey.Routing

/-- The actual executable prefix initializes the recursive proof with the
precise lifted primal, the selected live top cuts, and its linear work credit. -/
noncomputable def AugmentationPreRebaseReady.liftedMatching {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {s u t : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (cycles : MatchingLiveCycles registry) {rows : List (Fin k × Fin k)} (ready : AugmentationPreRebaseReady rows u t)
    (layout : AugmentationInstallLayout k (augmentationCrossingSeed u k))
    (original : ∀ v : Fin k, u.nm (u.nr 57+v.val) = (part.representative v).val)
    (nodes : ∀ v : Fin k, u.nm (u.nr 74+v.val) = blossomNodeAt s v)
    (mates : ∀ v : Fin k, u.nm (u.nr 50+v.val) = compactPrimalMateWord old v.val)
    (size : t.nr 55 = k) (cursor : t.nr 76 = s.nr 76)
    (unique : ((selectedAugmentationPorts rows).map part.representative).Nodup)
    {start finish : Fin k} {inner : Fin k → Finset (Sym2 (Fin k))} {quotient : Finset (Sym2 (Fin k))}
    (lift : MatchingAugmentedPrimal part start finish (rows.foldl (chooseAugmentationRepresentatives part.representative) id) inner quotient)
    (installed : ∀ p ∈ rows, s(p.1,p.2) ∈ lift.next.edges)
    (crossing : ∀ e ∈ quotient.image (Sym2.map (rows.foldl (chooseAugmentationRepresentatives part.representative) id)),
      e ∈ old.edges ∨ ∃ p ∈ rows, e = s(p.1,p.2))
    (blocks : ∀ q ∈ part.activeRepresentatives,
      (q ∉ ((selectedAugmentationPorts rows).map part.representative).toFinset →
        inner q = matchingCycleInterior old (part.blocks.block q) q) ∧
      (q ∈ ((selectedAugmentationPorts rows).map part.representative).toFinset → (part.blocks.block q).card ≠ 1 →
        MatchingCycleLiftDerivation cycles.entry (part.blocks.block q)
          ((rows.foldl (chooseAugmentationRepresentatives part.representative) id) q) (inner q)))
    (full : MatchingRebaseArchive t)
    (archived : ∀ B (h : B ∈ old.cuts), full.live (dual.node B) (cycles.entry B h).tree)
    (physical : ∀ B (h : B ∈ old.cuts), MatchingNodeCycleRows t (dual.node B)
      (cycles.entry B h).geometry.cycle (cycles.entry B h).geometry.edges) :
    let tasks := (selectedAugmentationPorts rows).filterMap (matchingAugmentTopTask cycles)
    MatchingPreparedLift t tasks (compactPrimalMateWord lift.next) ×' (matchingRebaseQueueWork tasks ≤ k) := by
  intro tasks
  let archive := matchingAugmentDerivedArchive (next := lift.next) cycles full archived
  let plan := matchingAugmentPlanOfRows (next := lift.next) cycles full archived physical
  have planned := matchingAugmentInitialTasks_planned cycles full archived rows unique lift
    (fun p hp selected => (blocks p hp).2 (List.mem_toFinset.mpr selected))
  have counts := matchingAugmentInitialTasks_capacity cycles (selectedAugmentationPorts rows) unique
  refine ⟨⟨⟨archive, ready.liveTasks cycles layout original nodes unique,
    fun task ht => ⟨(planned task ht).1,(planned task ht).2.1⟩,counts.1,counts.2.1,
    fun n hn => cursor.symm ▸ counts.2.2.1 n hn⟩,plan,fun task ht => (planned task ht).2.2,?_⟩,counts.2.2.2⟩
  intro i hi closed
  let v : Fin k := ⟨i,size ▸ hi⟩
  have words := ready.boundaryOfRows layout part.representative original mates unique installed tasks (by
    intro w absent settled
    have away := matchingAugmentInitialTasks_cover cycles _ w absent settled
    have current := (part.mem_activeRepresentatives _).mpr (part.representative_idem w)
    exact lift.outsideMate rows w away ((blocks _ current).1 (fun hit => away (List.mem_toFinset.mp hit))) crossing)
  rw [ready.fixed 50 (by decide)]
  exact words v closed


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentPreparedPrimal

/-! matching/MatchingAugmentStorageArchive.lean -/
section RppSource_MatchingAugmentStorageArchive
namespace VehicleRoutingSurvey.Routing

/-- Build the actual post-installation immutable archive using the same
permanent IDs, child subtrees, and oriented rows as the live pre-event registry. -/
noncomputable def MatchingLiveCycles.augmentationArchive {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {caller s t : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (cycles : MatchingLiveCycles registry) (storage : MatchingStageStorage k caller s) (order : MatchingCycleRecordOrder s)
    (capacity : ∀ n < s.nr 76, n < matchingBlossomCapacity k)
    (frame : MatchingAugmentArchiveFrame s t) (stackBase : t.nr 81 = s.nr 80+3*k) :
    Σ' full : MatchingRebaseArchive t,
      (∀ B (h : B ∈ old.cuts), full.live (dual.node B) (cycles.entry B h).tree) ∧
      ∀ B (h : B ∈ old.cuts), MatchingNodeCycleRows t (dual.node B) (cycles.entry B h).geometry.cycle (cycles.entry B h).geometry.edges := by
  classical
  let live (n : ℕ) (c : MatchingMemberTree) := ∃ (B : Finset (Fin k)) (h : B ∈ old.cuts),
    dual.node B = n ∧ (cycles.entry B h).tree = c
  have keep (r : ℕ) (h : r ∈ ([50,55,68,76,77,78,79,80] : List ℕ) := by decide) := frame.fixed r h
  obtain ⟨warm,_,nodes,_,starts,lengths,traces,right,marks,witnesses,records,promotion,mask,map,stack,_⟩ := storage
  have mates := warm.matesBefore
  have role := warm.representativesAfter
  have reps := warm.candidatesAfter
  have pairs := warm.pairsAfter
  have size := warm.size
  have matBound : t.nr 50+t.nr 55 ≤ t.nr 79 := by rw [keep 50,keep 55,keep 79]; omega
  have walkMap : t.nr 79+t.nr 55 ≤ t.nr 80 := by rw [keep 79,keep 55,keep 80]; omega
  have walkJobs : t.nr 80+3*t.nr 55 ≤ t.nr 81 := by rw [keep 80,keep 55,stackBase]; omega
  have jobsRows : t.nr 81+2*t.nr 55 ≤ matchingRebaseScratchEnd t := by
    rw [matchingRebaseScratchEnd,stackBase,keep 80,keep 55]; omega
  have headers (n : ℕ) (small : n < s.nr 76) : matchingRebaseHeaderArea t (t.nr 77+n) ∧ matchingRebaseHeaderArea t (t.nr 78+n) := by
    have less := capacity n small
    simp only [matchingRebaseHeaderArea,keep 50,keep 55,keep 77,keep 78,keep 79]
    omega
  have root (B : Finset (Fin k)) (h : B ∈ old.cuts) : 0 < dual.node B ∧ dual.node B < s.nr 76 :=
    ⟨Nat.pos_of_ne_zero (dual.nodeNonzero B h),registry.allocated B h⟩
  have range (B : Finset (Fin k)) (h : B ∈ old.cuts) (n : ℕ) (member : n ∈ dual.node B :: (cycles.entry B h).tree.registryIds) :
      0 < n ∧ n < s.nr 76 := by
    rcases List.mem_cons.mp member with eq | below
    · exact eq.symm ▸ root B h
    · obtain ⟨D,hd,eq⟩ := (registry.keys n).mp (cycles.ids B h n below)
      exact eq ▸ root D hd
  have adjusted (B : Finset (Fin k)) (h : B ∈ old.cuts) := frame.cycle (cycles.memory B h) (range B h)
  have allocated (n c) (h : live n c) : 0 < n ∧ n < t.nr 76 := by
    obtain ⟨B,hb,rfl,_⟩ := h
    rw [keep 76]
    exact root B hb
  refine ⟨⟨live,?_,allocated,?_,fun n c h => headers n (keep 76 ▸ (allocated n c h).2),
    frame.recordOrder order,matBound,walkMap,walkJobs,jobsRows⟩,
    fun B h => ⟨B,h,rfl,rfl⟩, fun B h => (adjusted B h).rows⟩
  · intro n c property
    let B := property.choose
    let hb := property.choose_spec.choose
    have eq : dual.node B = n ∧ (cycles.entry B hb).tree = c := property.choose_spec.choose_spec
    rw [← eq.1, ← eq.2]
    exact (adjusted B hb).archived (frame.recordOrder order)
      (fun id hi => (keep 76).symm ▸ range B hb id hi) (fun id hi => headers id (range B hb id hi).2)
  · intro n c property job listed child eq
    obtain ⟨B,hb,_,rfl⟩ := property
    obtain ⟨D,hd,id,tree,_,_⟩ := cycles.child B hb job listed child eq
    exact ⟨D,hd,id,tree⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentStorageArchive

/-! matching/MatchingAugmentInstalledEdges.lean -/
section RppSource_MatchingAugmentInstalledEdges
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Every newly installed crossing joins its two selected original ports.
Old quotient edges that survive the flip have neither endpoint on one of
these crossing rows, so both their originals and their tightness persist. -/
theorem matchingAugmentInstalledEdges {k : ℕ} {cost : Fin k → Fin k → ℝ} {old : CompactMatchingPrimalDual k cost}
    (part : CompactMatchingPartition old) (rows : List (Fin k × Fin k))
    {covered : Finset (Fin k)} {quotient : Finset (Sym2 (Fin k))}
    (perfect : IsPerfectMatchingOn covered quotient)
    (unique : ((selectedAugmentationPorts rows).map part.representative).Nodup)
    (rowTight : ∀ p ∈ rows, oddCutDualEdgeValue old.cuts old.potential old.cutDual s(p.1,p.2) = edgeCost cost s(p.1,p.2))
    (installed : ∀ p ∈ rows, s(part.representative p.1, part.representative p.2) ∈ quotient)
    (fromOld : ∀ e ∈ quotient, (∀ p ∈ rows, s(part.representative p.1, part.representative p.2) ≠ e) →
      e ∈ part.quotientEdges) :
    let port := rows.foldl (chooseAugmentationRepresentatives part.representative) id
    (∀ e ∈ quotient, oddCutDualEdgeValue old.cuts old.potential old.cutDual (Sym2.map port e) =
      edgeCost cost (Sym2.map port e)) ∧
    (∀ q ∉ covered, port q = q) ∧
    (∀ p ∈ rows, s(p.1,p.2) ∈ quotient.image (Sym2.map port)) ∧
    ∀ e ∈ quotient.image (Sym2.map port), e ∈ old.edges ∨ ∃ p ∈ rows, e = s(p.1,p.2) := by
  intro port
  let rep := part.representative
  have selected := matchingAugmentationNewPorts rows rep unique
  have ends (p : Fin k × Fin k) (hp : p ∈ rows) : port (rep p.1) = p.1 ∧ port (rep p.2) = p.2 := by
    exact ⟨selected.1 _ (List.mem_flatMap.mpr ⟨p, hp, by simp⟩),
      selected.1 _ (List.mem_flatMap.mpr ⟨p,hp, by simp⟩)⟩
  have realize (p : Fin k × Fin k) (hp : p ∈ rows) :
      Sym2.map port s(rep p.1,rep p.2) = s(p.1,p.2) := by
    rw [Sym2.map_mk, (ends p hp).1, (ends p hp).2]
  have owner {q : Fin k} (used : q ∈ (selectedAugmentationPorts rows).map rep) :
      ∃ p ∈ rows, q ∈ s(rep p.1,rep p.2) := by
    obtain ⟨e, he, atQ⟩ := selectedAugmentationPorts_mem rows rep used
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    exact ⟨p, hp, atQ⟩
  have origin (e : Sym2 (Fin k)) (he : e ∈ quotient) :
      Sym2.map port e ∈ old.edges ∨ ∃ p ∈ rows, Sym2.map port e = s(p.1,p.2) := by
    by_cases fresh : ∃ p ∈ rows, s(rep p.1, rep p.2) = e
    · obtain ⟨p, hp, rfl⟩ := fresh
      exact .inr ⟨p,hp,realize p hp⟩
    · have original := fromOld e he (fun p hp eq => fresh ⟨p,hp,eq⟩)
      have keep (v : Fin k) (hv : v ∈ e) : port v = v := by
        apply selected.2
        intro wasSet
        obtain ⟨p, hp, atP⟩ := owner wasSet
        have same := (perfect.2 v ((perfect.1 _ he).2 v hv)).unique
          ⟨installed p hp, atP⟩ ⟨he, hv⟩
        exact fresh ⟨p, hp, same⟩
      have fixed : Sym2.map port e = e := by
        induction e using Sym2.inductionOn with
        | hf a b => rw [Sym2.map_mk, keep a (Sym2.mem_mk_left _ _), keep b (Sym2.mem_mk_right _ _)]
      exact .inl (fixed.symm ▸ (Finset.mem_filter.mp original).1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    rcases origin e he with oldEdge | ⟨p, hp, eq⟩
    · exact old.tight _ oldEdge
    · exact eq.symm ▸ rowTight p hp
  · intro q free
    apply selected.2
    intro outside
    obtain ⟨p, hp, incident⟩ := owner outside
    exact free ((perfect.1 _ (installed p hp)).2 q incident)
  · intro p hp
    exact Finset.mem_image.mpr ⟨_, installed p hp, realize p hp⟩
  · intro e he
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
    exact origin x hx


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentInstalledEdges

/-! matching/MatchingAugmentSelectedPath.lean -/
section RppSource_MatchingAugmentSelectedPath
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

theorem MatchingForestLinkMemory.quotientForest {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    (links : MatchingForestLinkMemory part forest s) (valid : forest.valid old.partialMate part.tightBetween) :
    forest.valid part.quotientMate (fun _ _ => True) := by
  have same (v : Fin k) (marked : forest.role v ≠ .unlabelled) : part.quotientMate v = old.partialMate v := by
    have h : part.representative v = v := by
      by_contra away
      exact marked (links.inactive v away)
    simp [CompactMatchingPartition.quotientMate,(part.mem_activeRepresentatives _).mpr h]
  intro x
  have row := valid x
  cases eq : forest.role x with
  | unlabelled => trivial
  | inner p =>
    rw [eq] at row
    rw [same x (by simp [eq])]
    exact ⟨row.1, row.2.1, row.2.2.1, trivial, row.2.2.2.2⟩
  | outer prior =>
    rw [eq] at row
    cases prior with
    | none => exact (same x (by simp [eq])).trans row
    | some p =>
      obtain ⟨⟨q, inner⟩, outMate, inMate, _, depth⟩ := row
      exact ⟨⟨q, inner⟩, (same x (by simp [eq])).trans outMate,
        (same p (by simp [inner])).trans inMate, trivial, depth⟩

/-- Computing the set difference on the two traces adds exactly the rows
emitted by the augmentation handler, and preserves only old edges elsewhere. -/
theorem forestAugmentationCrossings_installed {k : ℕ} {forest : AlternatingForestState (Fin k)}
    {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop}
    (valid : forest.valid mate tight) {a b : Fin k} {pa pb : Option (Fin k)}
    (aOuter : forest.role a = .outer pa) (bOuter : forest.role b = .outer pb)
    (witness : Fin k → Fin k × Fin k) (rep : Fin k → Fin k) (trigger : Fin k × Fin k)
    (sound : ∀ child parent, (forest.role child).parent = some parent →
      (rep (witness child).1, rep (witness child).2) = (parent,child))
    (triggerAt : (rep trigger.1, rep trigger.2) = (a,b)) (M : Finset (Sym2 (Fin k))) :
    let rows := forestAugmentationCrossings witness trigger (forest.traceToRoot a) (forest.traceToRoot b)
    let result := augmentFromOuterForests forest M a b
    (∀ p ∈ rows, s(rep p.1, rep p.2) ∈ result) ∧
      (∀ e ∈ result, (∀ p ∈ rows, s(rep p.1, rep p.2) ≠ e) → e ∈ M) := by
  intro rows result
  obtain ⟨aHead, _, _, aChain, start, aEnd, _⟩ :=
    AlternatingForestState.traceToRoot_spec valid (x := a) (by simp [aOuter])
  obtain ⟨bHead, _, _, bChain, finish, bEnd, _⟩ :=
    AlternatingForestState.traceToRoot_spec valid (x := b) (by simp [bOuter])
  obtain ⟨back, asLeft⟩ := List.getLast?_eq_some_iff.mp aEnd
  obtain ⟨front, asRight⟩ := List.getLast?_eq_some_iff.mp bEnd
  have projected : rows.map (fun p => s(rep p.1,rep p.2)) = alternatingEdges ((forest.traceToRoot a).reverse ++ forest.traceToRoot b) :=
    forestAugmentationCrossings_topEdges aHead bHead (AlternatingForestState.outerTrace_length_odd valid aOuter)
      (AlternatingForestState.outerTrace_length_odd valid bOuter) (aChain.imp fun _ _ h => h.1)
      (bChain.imp fun _ _ h => h.1) witness rep trigger sound triggerAt
  let oldPairs := (alternatingEdges (back.reverse ++ front)).toFinset
  have edges : result = (M \ oldPairs) ∪ (rows.map (fun p => s(rep p.1,rep p.2))).toFinset := by
    simp [result, augmentFromOuterForests, aEnd, bEnd, augmentMatchingAlong, projected,
      asLeft, asRight, List.append_assoc, oldPairs]
  rw [edges]
  constructor
  · intro p hp
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨p,hp,rfl⟩))
  · intro e he outside
    rcases Finset.mem_union.mp he with old | newEdge
    · exact (Finset.mem_sdiff.mp old).1
    · obtain ⟨p, hp, same⟩ := List.mem_map.mp (List.mem_toFinset.mp newEdge)
      exact (outside p hp same).elim

/-- A forest witness read on one leg is a real tight original crossing. -/
theorem forestAugmentationCrossings_tight {k : ℕ} {forest : AlternatingForestState (Fin k)}
    {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop}
    (valid : forest.valid mate tight) {a b : Fin k} {pa pb : Option (Fin k)}
    (aOuter : forest.role a = .outer pa) (bOuter : forest.role b = .outer pb)
    (witness : Fin k → Fin k × Fin k) (trigger : Fin k × Fin k) (edgeTight : Sym2 (Fin k) → Prop)
    (sound : ∀ child parent, (forest.role child).parent = some parent → edgeTight s((witness child).1, (witness child).2))
    (triggerTight : edgeTight s(trigger.1,trigger.2)) :
    ∀ p ∈ forestAugmentationCrossings witness trigger (forest.traceToRoot a) (forest.traceToRoot b), edgeTight s(p.1,p.2) := by
  have leg (side : Bool) (q : Fin k) {previous : Option (Fin k)} (marked : forest.role q = .outer previous) :
      ∀ child ∈ augmentationWitnessChildren side (forest.traceToRoot q), edgeTight s((witness child).1,(witness child).2) := by
    let trail := forest.traceToRoot q
    obtain ⟨_, _, _, chain, _⟩ := AlternatingForestState.traceToRoot_spec valid (x := q) (by simp [marked])
    have odd := AlternatingForestState.outerTrace_length_odd valid marked
    intro child listed
    obtain ⟨i, hi, eq⟩ := List.mem_iff_getElem.mp listed
    let j := augmentationTraceIndex side (augmentationWitnessStart side trail.length) i
    have bounded : j+1 < trail.length := augmentationWitnessIndex_parent_inBounds side odd
      (by simpa only [augmentationWitnessChildren_length] using hi)
    have seen : trail[j]'(by omega) = child := (augmentationWitnessChildren_get side trail i hi).symm.trans eq
    have link := (List.isChain_iff_getElem.mp chain j bounded).1
    exact sound child trail[j+1] (seen ▸ link)
  intro p hp
  rcases List.mem_append.mp hp with left | right
  · rcases List.mem_append.mp left with old | picked
    · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp old
      exact leg false a aOuter c hc
    · have eq : p = trigger := List.mem_singleton.mp picked
      exact eq.symm ▸ triggerTight
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp right
    exact Sym2.eq_swap ▸ leg true b bOuter c hc


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentSelectedPath

/-! matching/MatchingAugmentSelectedPrimal.lean -/
section RppSource_MatchingAugmentSelectedPrimal
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



theorem matchingAugmentationSavedWitness_spec {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    (stored : MatchingForestOriginalWitnesses part forest s) (child p : Fin k)
    (link : (forest.role child).parent = some p) :
    let w := matchingAugmentationSavedWitness stored child
    matchingForestWitnessAt s.nm (s.nr 90) child.val = (w.1.val,w.2.val) ∧
      (part.representative w.1,part.representative w.2) = (p,child) ∧ matchingLiftTight old s(w.1,w.2) := by
  classical
  have hp : ∃ q, (forest.role child).parent = some q := ⟨p,link⟩
  have eq : hp.choose = p := Option.some.inj (hp.choose_spec.symm.trans link)
  have all := (stored hp.choose_spec).choose_spec.choose_spec
  simp only [matchingAugmentationSavedWitness, dif_pos hp]
  exact ⟨all.1, Prod.ext (all.2.1.trans eq) all.2.2.1, all.2.2.2⟩

/-- The chosen edge between distinct outer trees gives an actual integral
primal state on the originals. Its top-level crossings are precisely the
original records chosen by the machine; only the selected subtrees are rebased. -/
theorem matchingAugmentSelectedPrimal {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (cycles : MatchingLiveCycles registry) (top : CompactTopMatching part) (inside : old.InternalCuts)
    (valid : forest.valid old.partialMate part.tightBetween) (links : MatchingForestLinkMemory part forest s)
    (stored : MatchingForestOriginalWitnesses part forest s) (trigger : Fin k × Fin k)
    {a b : Fin k} {pa pb : Option (Fin k)}
    (aOuter : forest.role a = .outer pa) (bOuter : forest.role b = .outer pb)
    (different : forest.commonAncestor a b = none)
    (direction : (part.representative trigger.1,part.representative trigger.2) = (a,b))
    (newTight : matchingLiftTight old s(trigger.1,trigger.2)) :
    let witness := matchingAugmentationSavedWitness stored
    let rows := forestAugmentationCrossings witness trigger (forest.traceToRoot a) (forest.traceToRoot b)
    let touched := ((selectedAugmentationPorts rows).map part.representative).toFinset
    let port := rows.foldl (chooseAugmentationRepresentatives part.representative) id
    let quotient := augmentFromOuterForests forest part.quotientEdges a b
    ∃ start finish inner, ∃ lift : MatchingAugmentedPrimal part start finish port inner quotient,
      (∀ p ∈ rows, s(p.1,p.2) ∈ lift.next.edges) ∧
      (∀ e ∈ quotient.image (Sym2.map port), e ∈ old.edges ∨ ∃ p ∈ rows, e = s(p.1,p.2)) ∧
      ∀ q ∈ part.activeRepresentatives,
        (q ∉ touched → inner q = matchingCycleInterior old (part.blocks.block q) q) ∧
        (q ∈ touched → (part.blocks.block q).card ≠ 1 →
          MatchingCycleLiftDerivation cycles.entry (part.blocks.block q) (port q) (inner q)) := by
  intro witness rows touched port quotient
  let rep := part.representative
  have valid' := links.quotientForest valid
  have free (v : Fin k) (unmatched : part.quotientMate v = none) : v ∉ part.quotientCovered := by
    intro h
    obtain ⟨hv, ht⟩ := Finset.mem_inter.mp h
    simp [CompactMatchingPartition.quotientMate, CompactMatchingPrimalDual.partialMate, hv, ht] at unmatched
  obtain ⟨start,finish,_,_,startRole,finishRole,startFree,finishFree,distinct,perfect,_,_⟩ :=
    augmentFromOuterForests_roots (tight := fun _ => True) top.quotientPerfect valid'
      (fun _ _ h => top.quotientMate_some.mp h) free (fun _ _ => trivial) aOuter bOuter different trivial
  have rootTop (v : Fin k) (role : forest.role v = .outer none) : v ∈ part.activeRepresentatives := by
    apply (part.mem_activeRepresentatives _).mpr
    by_contra ne
    have impossible := (links.inactive v ne).symm.trans role
    cases impossible
  have startTop := rootTop _ startRole
  have finishTop := rootTop _ finishRole
  have source {c p : Fin k} (link : (forest.role c).parent = some p) :=
    matchingAugmentationSavedWitness_spec stored c p link
  have projected := fun c p link => (source (c := c) (p := p) link).2.1
  have unique := forestAugmentationCrossings_distinct_classes valid aOuter bOuter different witness rep trigger projected direction
  have form := forestAugmentationCrossings_installed valid aOuter bOuter witness rep trigger projected direction part.quotientEdges
  have rowTight := forestAugmentationCrossings_tight valid aOuter bOuter witness trigger (matchingLiftTight old)
    (fun _ _ link => (source link).2.2) newTight
  have resolved := matchingAugmentInstalledEdges part rows perfect unique rowTight form.1 form.2
  have insidePort (q : Fin k) (_ : q ∈ part.activeRepresentatives) : port q ∈ part.blocks.block q :=
    matchingAugmentationNewPort_inBlock part rows unique q
  have untouched (q : Fin k) (notTouched : q ∉ touched) : port q = q :=
    (matchingAugmentationNewPorts rows rep unique).2 _ (fun h => notTouched (List.mem_toFinset.mpr h))
  obtain ⟨inner, parts⟩ := matchingAugmentBlockLifts cycles top inside touched port insidePort untouched
  let lift := matchingAugmentLiftedState part start finish startTop finishTop
    (fun h => startFree (Finset.mem_inter.mpr ⟨h,startTop⟩)) (fun h => finishFree (Finset.mem_inter.mpr ⟨h,finishTop⟩))
    distinct port insidePort (fun q _ => resolved.2.1 q) quotient perfect resolved.1 inner
    (fun q h => (parts q h).1) (fun q h => (parts q h).2.1) (fun q h => (parts q h).2.2.1) registry.nested
  refine ⟨start, finish, inner, lift, ?_, resolved.2.2.2, fun q listed => (parts q listed).2.2.2⟩
  intro p hp
  rw [lift.edges]
  exact Finset.mem_union_right _ (resolved.2.2.1 p hp)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentSelectedPrimal

/-! matching/MatchingRebaseUpdatedGeometry.lean -/
section RppSource_MatchingRebaseUpdatedGeometry
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory





/-- A near-perfect local matching contained in the global matching is exactly
the globally matched edges whose two endpoints avoid the distinguished port. -/
theorem matchingCycleInterior_eq {k : ℕ} {cost : Fin k → Fin k → ℝ} {next : CompactMatchingPrimalDual k cost}
    {B : Finset (Fin k)} {p : Fin k} {inner : Finset (Sym2 (Fin k))}
    (perfect : IsPerfectMatchingOn (B.erase p) inner) (subset : inner ⊆ next.edges) :
    matchingCycleInterior next B p = inner := by
  ext e
  constructor
  · intro he
    obtain ⟨global,inside⟩ := Finset.mem_filter.mp he
    induction e using Sym2.inductionOn with
    | hf a b =>
      have atA := inside a (Sym2.mem_mk_left _ _)
      obtain ⟨f,hf,_⟩ := perfect.2 a atA
      have unique := (next.perfect.2 a ((next.perfect.1 _ global).2 a (Sym2.mem_mk_left _ _))).unique
        ⟨subset hf.1,hf.2⟩ ⟨global,Sym2.mem_mk_left _ _⟩
      exact unique ▸ hf.1
  · intro he
    exact Finset.mem_filter.mpr ⟨subset he,(perfect.1 _ he).2⟩




end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseUpdatedGeometry

/-! matching/MatchingAugmentCheckedLift.lean -/
section RppSource_MatchingAugmentCheckedLift
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory





/-- The chosen two-root event runs the real augmentation loop and produces
the new primal matching with one additional edge and the exact registry row effects. -/
theorem matchingAugmentationHandlerBlock_selectedLift {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {caller initial s : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest (matchingAugmentDualPoint s)}
    {registry : MatchingRegistryView dual} (cycles : MatchingLiveCycles registry)
    (top : CompactTopMatching part) (allCuts : old.InternalCuts)
    (valid : forest.valid old.partialMate part.tightBetween)
    (links : MatchingForestLinkMemory part forest (matchingAugmentDualPoint s))
    (stored : MatchingForestOriginalWitnesses part forest (matchingAugmentDualPoint s))
    (primal : CompactMatchingPrimalDualMemory old caller s)
    (storage : MatchingStageStorage k caller s) (order : MatchingCycleRecordOrder s)
    (capacity : ∀ n < s.nr 76, n < matchingBlossomCapacity k)
    (trigger : Fin k × Fin k) {a b : Fin k} {pa pb : Option (Fin k)} {traceBase : ℕ}
    (aOuter : forest.role a = .outer pa) (bOuter : forest.role b = .outer pb)
    (different : forest.commonAncestor a b = none)
    (direction : (part.representative trigger.1,part.representative trigger.2) = (a,b))
    (triggerTight : matchingLiftTight old s(trigger.1,trigger.2))
    (traced : MatchingForestTraceResult forest a b traceBase initial s)
    (triggerRAM : (s.nr 92,s.nr 93) = (trigger.1.val,trigger.2.val))
    (entry : s.pc = 0) (live : s.halted = false) (one : s.nr 9 = 1) :
    let witness := matchingAugmentationSavedWitness stored
    let rows := forestAugmentationCrossings witness trigger (forest.traceToRoot a) (forest.traceToRoot b)
    ∃ (next : CompactMatchingPrimalDual k cost) (nextPart : CompactMatchingPartition next)
      (t : ArithmeticState) (steps : ℕ),
      BlockRuns matchingAugmentationHandlerBlock steps s t ∧ t.halted = false ∧
      steps + (34*k+61) ≤ 512*(k^2+1) ∧
      t.nr 1 = 0 ∧ t.nr 33 = 0 ∧ t.nr 82 = 0 ∧
      t.rr 15 = s.rr 15+s.rr 1 ∧ t.rm = iterateBlossomDuals {s with rm := advancedEffectiveMemory s} k ∧
      CompactMatchingPrimalDualMemory next caller t ∧ next.edges.card = old.edges.card+1 ∧
      next.InternalCuts ∧ CompactTopMatching nextPart ∧ nextPart.blocks.block = part.blocks.block ∧
      next.cuts = old.cuts ∧ next.potential = old.potential ∧ next.cutDual = old.cutDual ∧
      ∃ (base : ArithmeticState) (jobs : List MatchingRebaseTask) (prepared : MatchingPreparedLift base jobs (compactPrimalMateWord next)),
        MatchingAugmentPreparedRegistry cycles rows nextPart prepared ∧
        MatchingRebaseCompletedRows prepared.lift jobs t := by
  intro witness rows
  let port := rows.foldl (chooseAugmentationRepresentatives part.representative) id
  let quotient := augmentFromOuterForests forest part.quotientEdges a b
  obtain ⟨start,finish,inner,lift,installed,crossing,blocks⟩ := matchingAugmentSelectedPrimal cycles top allCuts
    valid links stored trigger aOuter bOuter different direction triggerTight
  have storedLayout := storage
  obtain ⟨warm,realFloor,nodes,_,starts,lengths,left,right,marks,words,records,promote,mask,member,stack,_⟩ := storage
  have roles := warm.representativesAfter
  have reps := warm.candidatesAfter
  have caches := warm.pairsAfter
  have mates := warm.matesBefore
  have room := AlternatingForestState.disjointOuterTraces_length_le valid (by simp [aOuter]) (by simp [bOuter]) different
  have projections (c p : Fin k) (h : (forest.role c).parent = some p) :=
    matchingAugmentationSavedWitness_spec stored c p h
  obtain ⟨emitted,ticks,emit,emittedLive,bound,emittedRows⟩ := writeAugmentationCrossings_fromTrace valid
    aOuter bOuter traced different witness trigger entry live (by omega) (by omega)
    (fun c p h => (projections c p h).1) (by omega) triggerRAM
  have unique := forestAugmentationCrossings_distinct_classes valid aOuter bOuter different witness part.representative trigger
    (fun c p h => (projections c p h).2.1) direction
  have preserves (q : Fin k) (hq : q ∈ part.activeRepresentatives)
      (outside : q ∉ (selectedAugmentationPorts rows).map part.representative)
      (e : Sym2 (Fin k)) (inBlock : ∀ v ∈ e, v ∈ part.blocks.block q) :
      e ∈ lift.next.edges ↔ e ∈ old.edges := by
    have label : port q = q := (matchingAugmentationNewPorts rows part.representative unique).2 q outside
    have oldLabels := (part.mem_activeRepresentatives q).mp hq
    have newLabels : lift.partition.representative q = q := by
      rw [lift.representatives, Function.comp_apply, oldLabels]
      exact label
    have same := (blocks q hq).1 (fun found => outside (List.mem_toFinset.mp found))
    have localMatching : IsPerfectMatchingOn ((part.blocks.block q).erase q) (inner q) := by
      have checked := lift.eachBlock q hq
      change IsPerfectMatchingOn ((part.blocks.block q).erase (port q)) (inner q) at checked
      rw [label] at checked
      exact checked
    have included : inner q ⊆ lift.next.edges := by
      intro f hf
      rw [lift.edges]
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨q,hq,hf⟩)
    have updated := matchingCycleInterior_eq localMatching included
    have equivalence : matchingCycleInterior lift.next (part.blocks.block q) q =
        matchingCycleInterior old (part.blocks.block q) q := updated.trans same
    constructor
    · intro present
      have avoids := lift.top.internal_avoids_base newLabels present (by rw [lift.blocks]; exact inBlock)
      have yes : e ∈ matchingCycleInterior lift.next (part.blocks.block q) q :=
        Finset.mem_filter.mpr ⟨present, fun x hx => Finset.mem_erase.mpr ⟨fun same => avoids (same ▸ hx),inBlock x hx⟩⟩
      rw [equivalence] at yes
      exact (Finset.mem_filter.mp yes).1
    · intro present
      have avoids := top.internal_avoids_base oldLabels present inBlock
      have yes : e ∈ matchingCycleInterior old (part.blocks.block q) q :=
        Finset.mem_filter.mpr ⟨present, fun x hx => Finset.mem_erase.mpr ⟨fun same => avoids (same ▸ hx),inBlock x hx⟩⟩
      rw [← equivalence] at yes
      exact (Finset.mem_filter.mp yes).1
  have repBound (i : ℕ) (hi : i < k) : s.nm (s.nr 57+i) < k := (dual.reps ⟨i,hi⟩).symm ▸ (part.representative ⟨i,hi⟩).isLt
  have install : AugmentationInstallLayout k (augmentationCrossingSeed s k) := by
    constructor <;> simp [augmentationCrossingSeed] <;> omega
  have ready : ∀ u steps t, BlockRuns prepareMatchingAugmentationBlock steps s u →
      AugmentationPreRebaseReady rows {u with pc := 0} t →
      ∃ (jobs : List MatchingRebaseTask) (prepared : MatchingPreparedLift t jobs (compactPrimalMateWord lift.next)),
        MatchingAugmentPreparedRegistry cycles rows lift.partition prepared ∧
        matchingRebaseQueueWork jobs ≤ k := by
    intro u st t prepared prep
    obtain ⟨stable,unchanged,registers,stackBase⟩ :=
      matchingAugmentPrefixRegistry storedLayout order capacity emit emittedLive emittedRows bound one repBound prepared prep
    have fixed (r : ℕ) (h : r ∈ matchingFixedStorageRegisters := by decide) : u.nr r = s.nr r := registers r h
    have formed : MatchingAugmentArchiveFrame (matchingAugmentDualPoint s) t :=
      ⟨stable.fixed, stable.headers, stable.rows⟩
    have snapshotLayout := storedLayout.keeps (t := matchingAugmentDualPoint s) (fun _ _ => rfl)
    have snapshotOrder := order.transport (t := matchingAugmentDualPoint s) rfl rfl rfl
      (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    obtain ⟨full,archived,physical⟩ :=
      cycles.augmentationArchive snapshotLayout snapshotOrder capacity formed stackBase
    have original (v : Fin k) : u.nm (u.nr 57+v.val) = (part.representative v).val := by
      rw [fixed 57, unchanged _ (by have := v.isLt; omega)]
      exact dual.reps v
    have copied (v : Fin k) : u.nm (u.nr 74+v.val) = blossomNodeAt (matchingAugmentDualPoint s) v := by
      rw [fixed 74,unchanged _ (by have := v.isLt; omega)]
      rfl
    have mateWord (v : Fin k) : u.nm (u.nr 50+v.val) = compactPrimalMateWord old v.val := by
      rw [fixed 50,unchanged _ (by have := v.isLt; omega),primal.mate]
      simp [compactPrimalMateWord,v.isLt]
    have newLayout : AugmentationInstallLayout k (augmentationCrossingSeed {u with pc := 0} k) := by
      constructor <;> simp [augmentationCrossingSeed, fixed 50,fixed 57,fixed 74,fixed 86,fixed 89,fixed 80] <;> omega
    let result := prep.liftedMatching cycles newLayout original copied mateWord
      ((stable.fixed 55 (by decide)).trans primal.dimension) (stable.fixed 76 (by decide)) unique lift
      installed crossing blocks full archived physical
    refine ⟨_, result.1, ⟨formed, rfl, rfl, fun _ _ => Iff.rfl, ?_, ?_, unique,
      lift.representatives, preserves, ?_, ?_⟩, result.2⟩
    · intro a low
      change a < s.nr 50 at low
      exact (prep.preservedPrefix a (by simpa only [fixed 50] using low)).trans (unchanged a (by omega))
    · intro a lower upper
      change s.nr 51 ≤ a at lower
      change a < s.nr 51 + 3*k at upper
      have untouched := prep.untouched a
      apply (untouched ?_).trans (unchanged a (by omega))
      simp only [AugmentationPreRebaseUnwritten, AugmentationInstallUnwritten, augmentationCrossingSeed,
        Function.update_self, Function.update_of_ne (by decide : 81 ≠ 82),
        Function.update_of_ne (by decide : 50 ≠ 82), Function.update_of_ne (by decide : 50 ≠ 81),
        Function.update_of_ne (by decide : 74 ≠ 82), Function.update_of_ne (by decide : 74 ≠ 81),
        Function.update_of_ne (by decide : 89 ≠ 82), Function.update_of_ne (by decide : 89 ≠ 81),
        fixed 50, fixed 74, fixed 89, fixed 57, fixed 80]
      exact ⟨⟨.inr (by omega), .inl (by omega), .inl (by omega), .inl (by omega)⟩, .inl (by omega)⟩
    · intro v
      have table := (prep.typedTables newLayout part.representative original).2 v
      change t.nm (u.nr 57 + v.val) = _ at table
      rw [fixed 57] at table
      rw [lift.representatives]
      exact table
    · intro v
      have table := (prep.queuedRegistry newLayout part.representative
        (fun p => blossomNodeAt (matchingAugmentDualPoint s) p) original copied).nodes v
      have nodeBase : t.nr 74 = s.nr 74 := (prep.fixed 74 (by decide)).trans (fixed 74)
      rw [nodeBase] at table
      exact table
  have cutFloor : caller.nr 64 ≤ s.nr 75 := by
    have sep : s.nr 62 + k ≤ s.nr 75 := dual.separated
    omega
  obtain ⟨t,steps,ran,running,budget,flag,done,empty,clock,numerical,memory,records⟩ :=
    matchingAugmentationHandlerBlock_primal primal emit emittedLive emittedRows bound one (by omega) (by omega) (by omega)
      repBound install (by omega) cutFloor ready
  exact ⟨lift.next,lift.partition,t,steps,ran,running,budget,flag,done,empty,clock,numerical,memory,
    lift.increased,lift.allCuts,lift.top,lift.blocks,lift.cuts,lift.potential,lift.cutDual,records⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentCheckedLift

open VehicleRoutingSurvey.Routing SupplyChainTheory in
theorem solution : (fun {P : Prop} (_ : P) => P) (@VehicleRoutingSurvey.Routing.matchingAugmentationHandlerBlock_selectedLift) :=
  @VehicleRoutingSurvey.Routing.matchingAugmentationHandlerBlock_selectedLift
