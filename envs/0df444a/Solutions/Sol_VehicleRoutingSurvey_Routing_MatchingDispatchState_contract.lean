-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.MatchingDispatchState.contract
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T16:16:53.318796+00:00
-- url     : https://prove2.me/submissions/152e308a-4547-4a10-a825-d423022b5599

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_ContractionArm
import Theorems.Thm_VehicleRoutingSurvey_Routing_matchingContractionStructure_spec
import Theorems.Thm_VehicleRoutingSurvey_Routing_matchingContractionHandlerBlock_runs
import Theorems.Thm_VehicleRoutingSurvey_Routing_MatchingChosenStage_contractionDualSnapshot
import Theorems.Thm_VehicleRoutingSurvey_Routing_matchingContractionRegistersCycles
import Theorems.Thm_VehicleRoutingSurvey_Routing_matchingContractionSuffix_searchRows
import Theorems.Thm_VehicleRoutingSurvey_Routing_writeMatchingContractionCycle_spec
import Theorems.Thm_VehicleRoutingSurvey_Routing_MatchingDispatchState_traceOuter

/-! matching/MatchingPartitionView.lean -/
section RppSource_MatchingPartitionView
namespace VehicleRoutingSurvey.Routing









theorem CompactMatchingPartition.exposed_fixed {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    {v : Fin k} (exposed : v ∉ state.covered) : part.representative v = v := by
  by_contra different
  exact exposed (part.coveredAway v v (part.blocks.self_mem v (Finset.mem_univ v)) (Ne.symm different))








end VehicleRoutingSurvey.Routing
end RppSource_MatchingPartitionView

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







end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestAncestor

/-! matching/WeightedForestDispatch.lean -/
section RppSource_WeightedForestDispatch
namespace VehicleRoutingSurvey.Routing



/-- A positive edge rate can trigger two outer nodes, or one outer node and one unlabelled node. -/
theorem risingForestEdge_iff {α β : Type*} (left : AlternatingForestRole α) (right : AlternatingForestRole β) :
    0 < left.dualDirection + right.dualDirection ↔
      ((∃ p, left = .outer p) ∧ ((∃ q, right = .outer q) ∨ right = .unlabelled)) ∨
        (left = .unlabelled ∧ ∃ q, right = .outer q) := by
  cases left <;> cases right <;> norm_num [AlternatingForestRole.dualDirection, reduceCtorEq] <;> grind









/-- A cut can limit the dual step only when its blossom is a contracted inner node. -/
theorem forestCutDirection_negative_iff {n : ℕ} {O : Finset (Fin n)} {cuts : Finset (Finset (Fin n))}
    (blocks : TopLevelMatchingBlocks O cuts) (role : Finset (Fin n) → AlternatingForestRole (Fin n))
    (S : Finset (Fin n)) :
    forestCutDirection blocks (fun B => (role B).dualDirection) S < 0 ↔
      (S ∈ O.image blocks.block ∧ S.card ≠ 1) ∧ ∃ parent, role S = .inner parent := by
  by_cases enabled : S ∈ O.image blocks.block ∧ S.card ≠ 1
  · rw [forestCutDirection, if_pos enabled]
    simp only [enabled, true_and]
    cases label : role S <;>
      norm_num [label, enabled.1, enabled.2, AlternatingForestRole.dualDirection, reduceCtorEq] <;> grind
  · have impossible : ¬((S ∈ O.image blocks.block ∧ S.card ≠ 1) ∧ ∃ parent, role S = .inner parent) :=
      fun h => enabled h.1
    simp only [forestCutDirection, if_neg enabled, lt_self_iff_false, impossible]

end VehicleRoutingSurvey.Routing
end RppSource_WeightedForestDispatch

/-! matching/WeightedEffectivePotential.lean -/
section RppSource_WeightedEffectivePotential
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory





private theorem effectiveForestDirection {n : ℕ} {O : Finset (Fin n)} {cuts : Finset (Finset (Fin n))}
    (blocks : TopLevelMatchingBlocks O cuts) (label : Finset (Fin n) → ℝ) {v : Fin n} (hv : v ∈ O) :
    effectiveVertexPotential cuts (forestVertexDirection blocks label) (forestCutDirection blocks label) v =
      label (blocks.block v) := by
  have support : (cuts.filter (v ∈ ·)).filter (fun S => S ∈ O.image blocks.block ∧ S.card ≠ 1) =
      if (blocks.block v).card = 1 then ∅ else {blocks.block v} := by
    by_cases singleton : (blocks.block v).card = 1
    · rw [if_pos singleton]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S present
      obtain ⟨inCut, top, nontrivial⟩ := Finset.mem_filter.mp present
      have inside := (Finset.mem_filter.mp inCut).2
      obtain ⟨w, hw, shape⟩ := Finset.mem_image.mp top
      have same : blocks.block v = S := (blocks.same_of_mem hw (shape.symm ▸ inside)).trans shape
      exact nontrivial (same ▸ singleton)
    · rw [if_neg singleton]
      ext S
      constructor
      · intro present
        obtain ⟨inCut, top, _⟩ := Finset.mem_filter.mp present
        have inside := (Finset.mem_filter.mp inCut).2
        obtain ⟨w, hw, shape⟩ := Finset.mem_image.mp top
        exact Finset.mem_singleton.mpr ((blocks.same_of_mem hw (shape.symm ▸ inside)).trans shape).symm
      · intro equal
        obtain rfl := Finset.mem_singleton.mp equal
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨blocks.cut_mem hv singleton, blocks.self_mem v hv⟩,
          Finset.mem_image_of_mem _ hv, singleton⟩
  have cutSum : (∑ S ∈ cuts.filter (v ∈ ·), forestCutDirection blocks label S) =
      ∑ S ∈ (if (blocks.block v).card = 1 then ∅ else {blocks.block v}), label S := by
    rw [← support]
    exact (Finset.sum_filter _ _).symm
  by_cases one : (blocks.block v).card = 1 <;>
    simp [effectiveVertexPotential, forestVertexDirection, cutSum, one]

/-- The effective-potential table is updated by the label of each vertex's current
top-level blossom. This is one linear pass over the vertices. -/
theorem effectiveVertexPotential_shift {n : ℕ} {O : Finset (Fin n)} {cuts : Finset (Finset (Fin n))}
    (blocks : TopLevelMatchingBlocks O cuts) (label : Finset (Fin n) → ℝ)
    (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ) (δ : ℝ) {v : Fin n} (hv : v ∈ O) :
    effectiveVertexPotential cuts (fun x => potential x + δ * forestVertexDirection blocks label x)
      (fun S => cutDual S + δ * forestCutDirection blocks label S) v =
    effectiveVertexPotential cuts potential cutDual v + δ * label (blocks.block v) := by
  rw [← effectiveForestDirection blocks label hv]
  simp only [effectiveVertexPotential, Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
  abel



end VehicleRoutingSurvey.Routing
end RppSource_WeightedEffectivePotential

/-! matching/MatchingSearchTopology.lean -/
section RppSource_MatchingSearchTopology
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

theorem effectiveVertexPotential_register_cut {k : ℕ} (cuts : Finset (Finset (Fin k)))
    (B : Finset (Fin k)) (potential : Fin k → ℝ) (cutDual : Finset (Fin k) → ℝ) (v : Fin k) :
    effectiveVertexPotential (insert B cuts) potential (extendBlossomCutDual cuts cutDual) v =
      effectiveVertexPotential cuts potential cutDual v := by
  simp only [effectiveVertexPotential, Finset.sum_filter]
  congr 1
  have same : (∑ S ∈ cuts, if v ∈ S then extendBlossomCutDual cuts cutDual S else 0) =
      ∑ S ∈ cuts, if v ∈ S then cutDual S else 0 := by
    apply Finset.sum_congr rfl
    intro S present
    rw [extendBlossomCutDual, if_pos present]
  by_cases old : B ∈ cuts
  · rwa [Finset.insert_eq_of_mem old]
  · rw [Finset.sum_insert old, same]
    simp [extendBlossomCutDual, old]







theorem CompactMatchingPrimalDual.InternalCuts.registerCut {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (internal : state.InternalCuts)
    {B : Finset (Fin k)} (odd : Odd B.card)
    (new : ∃ base ∈ B, ∀ v ∈ B, v ≠ base → ∃ e ∈ state.edges, v ∈ e ∧ ∀ w ∈ e, w ∈ B) :
    (state.registerCut B odd).InternalCuts := by
  intro S present
  rcases Finset.mem_insert.mp present with rfl | old
  · exact new
  · exact internal S old




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



theorem dispatchMatchingActionBlock_spec
    {grow contract expand augment : List ArithmeticInstruction} {s t : ArithmeticState} {ticks : ℕ}
    (entry : s.pc = 0) (running : s.halted = false) (live : t.halted = false)
    (zero : s.nr 36 = 0) (one : s.nr 37 = 1) (two : s.nr 38 = 2)
    (action : s.nr 35 ≤ 3)
    (ran : BlockRuns (match s.nr 35 with
      | 0 => grow | 1 => contract | 2 => expand | _ => augment) ticks s t) :
    ∃ steps ≤ ticks + 4, BlockRuns (dispatchMatchingActionBlock grow contract expand augment) steps s
      {t with pc := (dispatchMatchingActionBlock grow contract expand augment).length} := by
  have cases : s.nr 35 = 0 ∨ s.nr 35 = 1 ∨ s.nr 35 = 2 ∨ s.nr 35 = 3 := by omega
  rcases cases with tag | tag | tag | tag
  · rw [tag] at ran
    have first := branchOnAtMost_left 35 36 grow contract entry running (by omega) ran live
    have routed := branchOnAtMost_left 35 37 _ (branchOnAtMost 35 38 expand augment) entry running (by omega) first (by exact live)
    exact ⟨1 + (1 + ticks + 1) + 1, by omega, routed⟩
  · rw [tag] at ran
    have second := branchOnAtMost_right 35 36 grow contract entry running (by omega) ran live
    have routed := branchOnAtMost_left 35 37 _ (branchOnAtMost 35 38 expand augment) entry running (by omega) second (by exact live)
    exact ⟨1 + (1 + ticks) + 1, by omega, routed⟩
  · rw [tag] at ran
    have third := branchOnAtMost_left 35 38 expand augment entry running (by omega) ran live
    have routed := branchOnAtMost_right 35 37 (branchOnAtMost 35 36 grow contract) _ entry running (by omega) third (by exact live)
    exact ⟨1 + (1 + ticks + 1), by omega, routed⟩
  · rw [tag] at ran
    have last := branchOnAtMost_right 35 38 expand augment entry running (by omega) ran live
    have routed := branchOnAtMost_right 35 37 (branchOnAtMost 35 36 grow contract) _ entry running (by omega) last (by exact live)
    exact ⟨1 + (1 + ticks), by omega, routed⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingEventDispatchRAM

/-! matching/MatchingGrowCacheRAM.lean -/
section RppSource_MatchingGrowCacheRAM
namespace VehicleRoutingSurvey.Routing

attribute [local simp] List.forall_mem_append List.forall_mem_map
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000





















structure CacheMemoryFrame (s t : ArithmeticState) : Prop where
  natural : ∀ a < s.nr 58, t.nm a = s.nm a
  real : ∀ a < s.nr 59, s.nr 59 ≤ s.nr 60 → s.nr 59 ≤ s.nr 66 → t.rm a = s.rm a





















































































end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowCacheRAM

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

/-! matching/MatchingStageBudget.lean -/
section RppSource_MatchingStageBudget
namespace VehicleRoutingSurvey.Routing







theorem MatchingStageTransition.charge_le {before after : MatchingStageCounts} {charge : ℕ}
    (transition : MatchingStageTransition before charge after) :
    charge + after.credit ≤ before.credit := by
  cases transition <;> simp only [MatchingStageCounts.credit] <;> omega

theorem MatchingStageTransition.charge_pos {before after : MatchingStageCounts} {charge : ℕ}
    (transition : MatchingStageTransition before charge after) : 0 < charge := by
  cases transition <;> omega







end VehicleRoutingSurvey.Routing
end RppSource_MatchingStageBudget

/-! matching/BlossomCreditBounds.lean -/
section RppSource_BlossomCreditBounds
namespace VehicleRoutingSurvey.Routing

variable {α : Type*} [DecidableEq α]







/-- Count original vertices that are still nonouter, inherited blossoms,
and distinct outer blocks of the current partition. -/
def matchingPartitionCounts {k : ℕ} {vertices : Finset (Fin k)}
    {cuts : Finset (Finset (Fin k))} (blocks : TopLevelMatchingBlocks vertices cuts)
    (outer : Finset (Fin k) → Prop) [DecidablePred outer] (inherited : Finset (Finset (Fin k))) :
    MatchingStageCounts :=
  ⟨(vertices.filter (fun v => ¬outer (blocks.block v))).card, inherited.card,
    ((vertices.image blocks.block).filter outer).card⟩







end VehicleRoutingSurvey.Routing
end RppSource_BlossomCreditBounds

/-! matching/TightBlossomContraction.lean -/
section RppSource_TightBlossomContraction
namespace VehicleRoutingSurvey.Routing

def traceBefore {α : Type*} [DecidableEq α] (root : α) (trace : List α) : List α :=
  trace.takeWhile (fun x => decide (x ≠ root))

theorem traceBefore_eq {α : Type*} [DecidableEq α] {root : α} {before after : List α}
    (outside : root ∉ before) : traceBefore root (before ++ (root :: after)) = before := by
  have passes : ∀ x ∈ before, decide (x ≠ root) = true := fun x hx =>
    decide_eq_true (show x ≠ root from fun equal => outside (equal ▸ hx))
  rw [traceBefore, List.takeWhile_append_of_pos passes]
  simp

private theorem cycle_tight_of_chain {n : ℕ} {vs : List (Fin n)} {a b : Fin n}
    {tight : Sym2 (Fin n) → Prop} (head : vs.head? = some a) (last : vs.getLast? = some b)
    (chain : vs.IsChain (fun u v => tight s(u, v))) (closing : tight s(b, a)) : CycleEdgesTight vs tight := by
  intro i hi
  by_cases interior : i + 1 < vs.length
  · simpa only [Nat.mod_eq_of_lt interior] using List.isChain_iff_getElem.mp chain i interior
  · have atEnd : i + 1 = vs.length := by omega
    have wrap : (i + 1) % vs.length = 0 := by rw [atEnd, Nat.mod_self]
    have wrapped : vs[(i + 1) % vs.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi)) = vs[0]'(by omega) :=
      getElem_congr_idx wrap
    have headValue : vs[0]'(by omega) = a := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (show 0 < vs.length by omega)] at head
      exact Option.some.inj head
    have lastValue : vs[i] = b := by
      have lastIndex : vs.length - 1 = i := by omega
      rw [List.getLast?_eq_getElem?, lastIndex, List.getElem?_eq_getElem hi] at last
      exact Option.some.inj last
    simpa only [wrapped, headValue, lastValue] using closing

/-- The contraction cycle follows the two outer vertices to their common base, then closes
with the tight edge that triggered the contraction. -/
def contractionCycle {α : Type*} [DecidableEq α] (left right : List α) (root : α) : List α :=
  traceBefore root left ++ (root :: (traceBefore root right).reverse)

theorem contractionCycle_spec {n : ℕ} {left right : List (Fin n)} {root a b : Fin n}
    (ancestor : firstSharedAncestor left right = some root)
    (leftDistinct : left.Nodup) (rightDistinct : right.Nodup)
    (leftHead : left.head? = some a) (rightHead : right.head? = some b) (different : a ≠ b)
    (leftEven : (traceBefore root left).length % 2 = 0)
    (rightEven : (traceBefore root right).length % 2 = 0)
    (tight : Sym2 (Fin n) → Prop) (leftTight : left.IsChain (fun u v => tight s(u, v)))
    (rightTight : right.IsChain (fun u v => tight s(u, v))) (closing : tight s(b, a)) :
    let vs := contractionCycle left right root
    vs.Nodup ∧ 3 ≤ vs.length ∧ Odd vs.length ∧ CycleEdgesTight vs tight := by
  obtain ⟨rootLeft, r, rAfter, rightEq, disjoint⟩ := firstSharedAncestor_eq_some_iff.mp ancestor
  obtain ⟨l, lAfter, leftEq⟩ := List.append_of_mem rootLeft
  have lDistinct : (l ++ [root]).Nodup := by
    have decomp : left = (l ++ [root]) ++ lAfter := by simpa [List.append_assoc] using leftEq
    exact List.Nodup.sublist (List.sublist_append_left _ lAfter) (decomp ▸ leftDistinct)
  have rDistinct : r.Nodup := List.Nodup.sublist (List.sublist_append_left r _) (rightEq ▸ rightDistinct)
  have rootNotL : root ∉ l := fun seen =>
    (List.nodup_append.mp lDistinct).2.2 root seen root (by simp) rfl
  have rootNotR : root ∉ r := fun seen => disjoint root seen rootLeft
  have beforeL : traceBefore root left = l := by rw [leftEq, traceBefore_eq rootNotL]
  have beforeR : traceBefore root right = r := by rw [rightEq, traceBefore_eq rootNotR]
  have leftPrefix : (l ++ [root]).IsChain (fun u v => tight s(u, v)) := by
    rw [leftEq] at leftTight
    rw [show l ++ (root :: lAfter) = (l ++ [root]) ++ lAfter by simp [List.append_assoc]] at leftTight
    exact leftTight.left_of_append
  have rightPrefix : (r ++ [root]).IsChain (fun u v => tight s(v, u)) := by
    rw [rightEq] at rightTight
    rw [show r ++ (root :: rAfter) = (r ++ [root]) ++ rAfter by simp [List.append_assoc]] at rightTight
    apply rightTight.left_of_append.imp
    intro u v h
    exact Sym2.eq_swap ▸ h
  have rightBack : (root :: r.reverse).IsChain (fun u v => tight s(u, v)) := by
    simpa only [List.reverse_append, List.reverse_singleton, List.singleton_append] using
      List.isChain_reverse.mpr rightPrefix
  have chain : (l ++ root :: r.reverse).IsChain (fun u v => tight s(u, v)) := by
    have pieces := List.isChain_append.mp leftPrefix
    refine List.IsChain.append pieces.1 rightBack ?_
    simpa only [List.head?_cons] using pieces.2.2
  simp only [beforeL] at leftEven
  simp only [beforeR] at rightEven
  simp only [contractionCycle, beforeL, beforeR]
  refine ⟨?_, ?_, ?_, cycle_tight_of_chain ?_ ?_ chain closing⟩
  · refine List.nodup_append.mpr ⟨(List.nodup_append.mp lDistinct).1,
      List.nodup_cons.mpr ⟨by simpa using rootNotR, List.nodup_reverse.mpr rDistinct⟩, ?_⟩
    intro x xMem y yMem
    rcases List.mem_cons.mp yMem with isBase | inRight
    · simpa only [isBase] using (List.nodup_append.mp lDistinct).2.2 x xMem root (by simp)
    · intro equal
      exact disjoint y (List.mem_reverse.mp inRight) (equal ▸ (leftEq.symm ▸ List.mem_append_left _ xMem))
  · by_contra tooShort
    simp only [List.length_append, List.length_cons, List.length_reverse] at tooShort
    have leftEmpty : l = [] := List.length_eq_zero_iff.mp (by omega)
    have rightEmpty : r = [] := List.length_eq_zero_iff.mp (by omega)
    have firstEq : root = a := by simpa [leftEq, leftEmpty] using leftHead
    have lastEq : root = b := by simpa [rightEq, rightEmpty] using rightHead
    exact different (firstEq.symm.trans lastEq)
  · rw [Nat.odd_iff]
    simp only [List.length_append, List.length_cons, List.length_reverse]
    omega
  · simpa only [leftEq, List.head?_append, List.head?_cons] using leftHead
  · rw [List.getLast?_eq_head?_reverse]
    simpa [rightEq, List.reverse_append, List.reverse_reverse, Option.or_assoc] using rightHead

end VehicleRoutingSurvey.Routing
end RppSource_TightBlossomContraction

/-! matching/AlternatingForestContract.lean -/
section RppSource_AlternatingForestContract
namespace VehicleRoutingSurvey.Routing





theorem AlternatingForestState.contract_valid {α : Type*} [DecidableEq α]
    {state : AlternatingForestState α} {mate : α → Option α} {tight tight' : α → α → Prop}
    (valid : state.valid mate tight) (cycle : Finset α) (base : α) {baseParent : Option α}
    (baseOuter : state.role base = .outer baseParent)
    (baseRank : ∀ x ∈ cycle, state.depth base ≤ state.depth x)
    (insideParent : ∀ x ∈ cycle, x ≠ base → ∀ p, (state.role x).parent = some p → p ∈ cycle)
    (insideMate : ∀ x ∈ cycle, ∀ p, state.role x = .inner p → ∀ y, mate x = some y → y ∈ cycle)
    (preservesEdges : ∀ x y, tight x y →
      tight' (blossomRepresentative cycle base x) (blossomRepresentative cycle base y)) :
    (state.contract cycle base).valid mate tight' := by
  let after := state.contract cycle base
  let rep := blossomRepresentative cycle base
  have retained {x : α} (keep : ¬(x ∈ cycle ∧ x ≠ base)) : rep x = x := by
    by_cases inside : x ∈ cycle
    · have equal : x = base := by by_contra bad; exact keep ⟨inside, bad⟩
      simp [rep, blossomRepresentative, inside, equal]
    · simp [rep, blossomRepresentative, inside]
  have depthBound (x : α) : state.depth (rep x) ≤ state.depth x := by
    by_cases inside : x ∈ cycle
    · simpa only [rep, blossomRepresentative, if_pos inside] using baseRank x inside
    · simp [rep, blossomRepresentative, inside]
  have staysOuter {x : α} {p : Option α} (keep : ¬(x ∈ cycle ∧ x ≠ base))
      (old : state.role x = .outer p) : after.role x = .outer p := by
    simp [after, contract, keep, old]
  change after.valid mate tight'
  intro x
  by_cases removed : x ∈ cycle ∧ x ≠ base
  · have idle : after.role x = .unlabelled := by simp [after, contract, removed]
    rw [idle]
    trivial
  have xKind : after.role x = (match state.role x with | .inner p => .inner (rep p) | kind => kind) := by
    cases kind : state.role x <;> simp [after, contract, removed, rep, kind]
  rw [xKind]
  have old := valid x
  cases kind : state.role x with
  | unlabelled => trivial
  | outer pOpt =>
    try rw [kind] at old
    cases pOpt with
    | none => exact old
    | some p =>
      obtain ⟨⟨grand, pRole⟩, xMate, pMate, edge, earlier⟩ := old
      have outside : p ∉ cycle := by
        intro included
        have xIn := insideMate p included grand pRole x pMate
        have xBase : x = base := by by_contra different; exact removed ⟨xIn, different⟩
        rw [xBase] at earlier
        exact (not_lt_of_ge (baseRank p included)) earlier
      refine ⟨⟨rep grand, ?_⟩, xMate, pMate, ?_, earlier⟩
      · simp [after, contract, outside, pRole, rep]
      · have pRetained : rep p = p := by simp [rep, blossomRepresentative, outside]
        have keptEdge : tight' (rep p) (rep x) := preservesEdges p x edge
        simpa only [pRetained, retained removed] using keptEdge
  | inner p =>
    try rw [kind] at old
    obtain ⟨⟨grand, pRole⟩, notMate, ⟨child, childMate, childRole⟩, edge, earlier⟩ := old
    have outside : x ∉ cycle := by
      intro included
      by_cases equal : x = base
      · have isOuter : state.role x = .outer baseParent := equal.symm ▸ baseOuter
        have impossible := kind.symm.trans isOuter
        cases impossible
      · exact removed ⟨included, equal⟩
    have childKeeps : ¬(child ∈ cycle ∧ child ≠ base) := by
      intro absorbs
      have link : (state.role child).parent = some x := by simp [childRole, AlternatingForestRole.parent]
      exact outside (insideParent child absorbs.1 absorbs.2 x link)
    have parentStillOuter : ∃ q, after.role (rep p) = .outer q := by
      by_cases included : p ∈ cycle
      · refine ⟨baseParent, ?_⟩
        have rb : rep p = base := by simp [rep, blossomRepresentative, included]
        rw [rb]
        exact staysOuter (by simp) baseOuter
      · refine ⟨grand, ?_⟩
        have rp : rep p = p := by simp [rep, blossomRepresentative, included]
        rw [rp]
        exact staysOuter (by simp [included]) pRole
    have parentNotMate : mate x ≠ some (rep p) := by
      by_cases included : p ∈ cycle
      · intro equates
        have childIsBase : child = base := Option.some.inj (childMate.symm.trans
          (by simpa [rep, blossomRepresentative, included] using equates))
        have childValid := valid child
        rw [childRole] at childValid
        have predRank := childValid.2.2.2.2
        rw [childIsBase] at predRank
        exact (not_lt_of_ge ((baseRank p included).trans earlier.le)) predRank
      · simpa [rep, blossomRepresentative, included] using notMate
    have preserved : tight' (rep p) x := by
      have result : tight' (rep p) (rep x) := preservesEdges p x edge
      simpa only [retained removed] using result
    exact ⟨parentStillOuter, parentNotMate, ⟨child, childMate, staysOuter childKeeps childRole⟩,
      preserved, (depthBound p).trans_lt earlier⟩

end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestContract

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

private theorem trace_last_step {α : Type*} {R : α → α → Prop} {base : α}
    {before after : List α} (nonempty : before ≠ []) (chain : (before ++ (base :: after)).IsChain R) :
    ∃ x ∈ before, R x base := by
  let x := before.getLast nonempty
  have atEnd : before.getLast? = some x := List.getLast?_eq_some_getLast nonempty
  exact ⟨x, List.mem_of_getLast? atEnd,
    (List.isChain_append.mp chain).2.2 x (by simp [atEnd]) base (by simp)⟩

private theorem common_base_outer {α : Type*} [DecidableEq α] {state : AlternatingForestState α}
    {mate : α → Option α} {tight : α → α → Prop} (valid : state.valid mate tight)
    {left right : List α} {a b base : α} (ancestor : firstSharedAncestor left right = some base)
    (leftHead : left.head? = some a) (rightHead : right.head? = some b)
    {aParent bParent : Option α} (aOuter : state.role a = .outer aParent)
    (bOuter : state.role b = .outer bParent)
    (leftChain : left.IsChain (fun u v => (state.role u).parent = some v))
    (rightChain : right.IsChain (fun u v => (state.role u).parent = some v)) :
    ∃ baseParent, state.role base = .outer baseParent := by
  obtain ⟨baseLeft, r, rAfter, rightEq, disjoint⟩ := firstSharedAncestor_eq_some_iff.mp ancestor
  obtain ⟨l, lAfter, leftEq⟩ := List.append_of_mem baseLeft
  by_cases leftEmpty : l = []
  · have equal : base = a := by simpa [leftEq, leftEmpty] using leftHead
    exact ⟨aParent, equal.symm ▸ aOuter⟩
  obtain ⟨x, xIn, link⟩ := trace_last_step leftEmpty (leftEq ▸ leftChain)
  rcases parent_step_roles valid link with ⟨previous, _, innerBase, mateX⟩ | ⟨previous, _, outerBase⟩
  · have rightNonempty : r ≠ [] := by
      intro empty
      have equal : base = b := by simpa [rightEq, empty] using rightHead
      have impossible := innerBase.symm.trans (equal.symm ▸ bOuter)
      cases impossible
    obtain ⟨y, yIn, yLink⟩ := trace_last_step rightNonempty (rightEq ▸ rightChain)
    rcases parent_step_roles valid yLink with ⟨_, _, _, mateY⟩ | ⟨_, _, outerBase⟩
    · have equal : x = y := Option.some.inj (mateX.symm.trans mateY)
      exact (disjoint y yIn (equal ▸ (leftEq.symm ▸ List.mem_append_left _ xIn))).elim
    · have impossible := innerBase.symm.trans outerBase
      cases impossible
  · exact ⟨previous, outerBase⟩

/-- Both legs of an actual contraction consist of labelled forest nodes, and
their common base was outer before the contraction. -/
theorem alternatingForest_contractionLabels {n : ℕ} {state : AlternatingForestState (Fin n)}
    {mate : Fin n → Option (Fin n)} {tight : Fin n → Fin n → Prop} (valid : state.valid mate tight)
    {a b base : Fin n} {pa pb : Option (Fin n)}
    (aOuter : state.role a = .outer pa) (bOuter : state.role b = .outer pb)
    (ancestor : state.commonAncestor a b = some base) :
    (∃ p, state.role base = .outer p) ∧
      ∀ v ∈ traceBefore base (state.traceToRoot a) ++ traceBefore base (state.traceToRoot b),
        state.role v ≠ .unlabelled := by
  obtain ⟨aHead, _, _, aChain, _⟩ := AlternatingForestState.traceToRoot_spec valid (x := a) (by simp [aOuter])
  obtain ⟨bHead, _, _, bChain, _⟩ := AlternatingForestState.traceToRoot_spec valid (x := b) (by simp [bOuter])
  have labelled (trail : List (Fin n))
      (head : ∀ x ∈ trail.head?, state.role x ≠ .unlabelled)
      (chain : trail.IsChain (fun u v => (state.role u).parent = some v ∧ tight v u)) :
      ∀ v ∈ trail, state.role v ≠ .unlabelled := by
    induction trail with
    | nil => simp
    | cons u rest ih =>
      intro v hv
      rcases List.mem_cons.mp hv with rfl | inside
      · exact head _ (by simp)
      · apply ih _ chain.tail v inside
        intro w hw
        have link := (List.isChain_cons.mp chain).1 w hw
        rcases parent_step_roles valid link.1 with ⟨_,_,kind,_⟩ | ⟨_,_,kind⟩ <;> simp [kind]
  refine ⟨common_base_outer valid ancestor aHead bHead aOuter bOuter
    (aChain.imp (fun _ _ h => h.1)) (bChain.imp (fun _ _ h => h.1)), ?_⟩
  intro v h
  rcases List.mem_append.mp h with left | right
  · exact labelled _ (by
      intro x hx
      have eq : a = x := by simpa only [aHead, Option.mem_some_iff] using hx
      simp [← eq, aOuter]) aChain v
      (List.takeWhile_subset _ left)
  · exact labelled _ (by
      intro x hx
      have eq : b = x := by simpa only [bHead, Option.mem_some_iff] using hx
      simp [← eq, bOuter]) bChain v
      (List.takeWhile_subset _ right)

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

theorem trace_before_outer_even {α : Type*} [DecidableEq α] {state : AlternatingForestState α}
    {mate : α → Option α} {tight : α → α → Prop} (valid : state.valid mate tight)
    {trace : List α} {first base : α} (baseMem : base ∈ trace)
    {firstParent baseParent : Option α} (firstOuter : state.role first = .outer firstParent)
    (baseOuter : state.role base = .outer baseParent) (head : trace.head? = some first)
    (distinct : trace.Nodup) (chain : trace.IsChain (fun u v => (state.role u).parent = some v)) :
    (traceBefore base trace).length % 2 = 0 := by
  obtain ⟨before, after, split⟩ := List.append_of_mem baseMem
  have outside : base ∉ before := fun present =>
    (List.nodup_append.mp (split ▸ distinct)).2.2 base present base (by simp) rfl
  have decomp : trace = (before ++ [base]) ++ after := by simpa [List.append_assoc] using split
  have original : ((before ++ [base]) ++ after).IsChain (fun u v => (state.role u).parent = some v) :=
    decomp ▸ chain
  have path : (before ++ [base]).IsChain (fun u v => (state.role u).outerTag ≠ (state.role v).outerTag) := by
    refine original.left_of_append.imp ?_
    intro u v link
    exact parent_step_alternates valid link
  have start : (before ++ [base]).head? = some first := by
    simpa only [split, List.head?_append, List.head?_cons] using head
  rw [split, traceBefore_eq outside]
  apply (alternating_chain_parity (fun v => (state.role v).outerTag) base before path).mpr
  simp [start, firstOuter, baseOuter, AlternatingForestRole.outerTag]

/-- A tight edge between distinct outer nodes in the same tree yields a simple tight odd
cycle through their common outer base. -/
theorem alternatingForest_contractionCycle {n : ℕ} {state : AlternatingForestState (Fin n)}
    {mate : Fin n → Option (Fin n)} {tight : Sym2 (Fin n) → Prop}
    (valid : state.valid mate (fun u v => tight s(u, v))) {a b base : Fin n}
    (different : a ≠ b) {aParent bParent : Option (Fin n)}
    (aOuter : state.role a = .outer aParent) (bOuter : state.role b = .outer bParent)
    (closing : tight s(b, a)) (ancestor : state.commonAncestor a b = some base) :
    let vs := contractionCycle (state.traceToRoot a) (state.traceToRoot b) base
    vs.Nodup ∧ 3 ≤ vs.length ∧ Odd vs.length ∧ CycleEdgesTight vs tight := by
  obtain ⟨aHead, aDistinct, _, aTrail, _⟩ := AlternatingForestState.traceToRoot_spec valid
    (x := a) (by simp [aOuter])
  obtain ⟨bHead, bDistinct, _, bTrail, _⟩ := AlternatingForestState.traceToRoot_spec valid
    (x := b) (by simp [bOuter])
  have aChain := aTrail.imp (fun _ _ h => h.1)
  have bChain := bTrail.imp (fun _ _ h => h.1)
  obtain ⟨_, baseOuter⟩ := common_base_outer valid ancestor aHead bHead aOuter bOuter aChain bChain
  obtain ⟨baseInA, beforeB, afterB, splitB, _⟩ := firstSharedAncestor_eq_some_iff.mp ancestor
  have baseInB : base ∈ state.traceToRoot b := splitB.symm ▸ List.mem_append_right beforeB (by simp)
  have aEven := trace_before_outer_even valid baseInA aOuter baseOuter aHead aDistinct aChain
  have bEven := trace_before_outer_even valid baseInB bOuter baseOuter bHead bDistinct bChain
  exact contractionCycle_spec ancestor aDistinct bDistinct aHead bHead different aEven bEven tight
    (aTrail.imp fun _ _ h => Sym2.eq_swap ▸ h.2) (bTrail.imp fun _ _ h => Sym2.eq_swap ▸ h.2) closing

theorem chain_next_before_last {α : Type*} {R : α → α → Prop} {last : α}
    (before : List α) (chain : (before ++ [last]).IsChain R) :
    ∀ x ∈ before, ∃ y ∈ before ++ [last], R x y := by
  induction before with
  | nil => simp
  | cons first rest ih =>
    change (first :: (rest ++ [last])).IsChain R at chain
    intro x hx
    rcases List.mem_cons.mp hx with equal | later
    · subst x
      have nonempty : rest ++ [last] ≠ [] := by simp
      let y := (rest ++ [last]).head nonempty
      have starts : (rest ++ [last]).head? = some y := List.head?_eq_some_head nonempty
      exact ⟨y, List.mem_cons_of_mem _ (List.mem_of_head? starts), chain.rel_head? (by simp [starts])⟩
    · obtain ⟨y, present, next⟩ := ih chain.tail x later
      exact ⟨y, List.mem_cons_of_mem _ present, next⟩

private theorem chain_prev_of_ne_first {α : Type*} {R : α → α → Prop} {trace : List α}
    {first v : α} (head : trace.head? = some first) (chain : trace.IsChain R)
    (inside : v ∈ trace) (later : v ≠ first) : ∃ x ∈ trace, R x v := by
  obtain ⟨tail, shape⟩ := List.head?_eq_some_iff.mp head
  have reversed : (tail.reverse ++ [first]).IsChain (fun a b => R b a) := by
    rw [← List.reverse_cons, List.isChain_reverse]
    exact shape ▸ chain
  have inTail : v ∈ tail := (List.mem_cons.mp (shape ▸ inside)).resolve_left later
  obtain ⟨x, found, previous⟩ := chain_next_before_last tail.reverse reversed v (List.mem_reverse.mpr inTail)
  have before : x ∈ (first :: tail).reverse := by simpa only [List.reverse_cons] using found
  exact ⟨x, shape.symm ▸ List.mem_reverse.mp before, previous⟩

private theorem chain_last_le_rank {α : Type*} (rank : α → ℕ) (last : α)
    (before : List α) (chain : (before ++ [last]).IsChain (fun u v => rank v ≤ rank u)) :
    ∀ x ∈ before ++ [last], rank last ≤ rank x := by
  induction before with
  | nil => simp
  | cons first rest ih =>
    change (first :: (rest ++ [last])).IsChain (fun u v => rank v ≤ rank u) at chain
    intro x hx
    rcases List.mem_cons.mp hx with equal | later
    · subst x
      have nonempty : rest ++ [last] ≠ [] := by simp
      let y := (rest ++ [last]).head nonempty
      have starts : (rest ++ [last]).head? = some y := List.head?_eq_some_head nonempty
      exact (ih chain.tail y (List.mem_of_head? starts)).trans (chain.rel_head? (by simp [starts]))
    · exact ih chain.tail x later

theorem trace_leg_valid {α : Type*} [DecidableEq α] {state : AlternatingForestState α}
    {mate : α → Option α} {tight : α → α → Prop} (valid : state.valid mate tight)
    {trace : List α} {first base : α} (baseMem : base ∈ trace) {firstParent : Option α}
    (firstOuter : state.role first = .outer firstParent) (head : trace.head? = some first)
    (distinct : trace.Nodup) (chain : trace.IsChain (fun u v => (state.role u).parent = some v)) :
    let leg := traceBefore base trace ++ [base]
    (∀ x ∈ leg, state.depth base ≤ state.depth x) ∧
    (∀ x ∈ leg, x ≠ base → ∀ p, (state.role x).parent = some p → p ∈ leg) ∧
    (∀ x ∈ leg, ∀ p, state.role x = .inner p → ∀ y, mate x = some y → y ∈ leg) := by
  obtain ⟨before, after, split⟩ := List.append_of_mem baseMem
  have outside : base ∉ before := fun present =>
    (List.nodup_append.mp (split ▸ distinct)).2.2 base present base (by simp) rfl
  have beforeEq : traceBefore base trace = before := by rw [split, traceBefore_eq outside]
  have decomp : trace = (before ++ [base]) ++ after := by simpa [List.append_assoc] using split
  have original : ((before ++ [base]) ++ after).IsChain (fun u v => (state.role u).parent = some v) := decomp ▸ chain
  have legChain := original.left_of_append
  have starts : (before ++ [base]).head? = some first := by
    simpa only [split, List.head?_append, List.head?_cons] using head
  dsimp only
  rw [beforeEq]
  refine ⟨chain_last_le_rank state.depth base before ?_, ?_, ?_⟩
  · refine legChain.imp fun u v link => ?_
    have marked : state.role u ≠ .unlabelled := by
      intro idle
      simp [idle, AlternatingForestRole.parent] at link
    have validParent := AlternatingForestState.parent_valid valid marked
    rw [link] at validParent
    exact validParent.2.1.le
  · intro x hx different p parent
    have prior : x ∈ before := (List.mem_append.mp hx).resolve_right (by simpa using different)
    obtain ⟨next, nextIn, chosen⟩ := chain_next_before_last before legChain x prior
    exact Option.some.inj (chosen.symm.trans parent) ▸ nextIn
  · intro x hx p inner y matched
    have later : x ≠ first := by
      intro equal
      have impossible := firstOuter.symm.trans (equal ▸ inner)
      cases impossible
    obtain ⟨previous, prior, incoming⟩ := chain_prev_of_ne_first starts legChain hx later
    rcases parent_step_roles valid incoming with ⟨_, _, _, matePrevious⟩ | ⟨_, _, outer⟩
    · exact Option.some.inj (matePrevious.symm.trans matched) ▸ prior
    · have impossible := inner.symm.trans outer
      cases impossible

/-- The two extracted branches supply the closure and rank facts needed to apply the
contraction operation to the existing search forest. -/
theorem alternatingForest_contractFromEdge {n : ℕ} {state : AlternatingForestState (Fin n)}
    {mate : Fin n → Option (Fin n)} {tight tight' : Fin n → Fin n → Prop}
    (valid : state.valid mate tight) {a b base : Fin n} {aParent bParent : Option (Fin n)}
    (aOuter : state.role a = .outer aParent) (bOuter : state.role b = .outer bParent)
    (ancestor : state.commonAncestor a b = some base)
    (preservesEdges : let cycle := (contractionCycle (state.traceToRoot a) (state.traceToRoot b) base).toFinset
      ∀ x y, tight x y → tight' (blossomRepresentative cycle base x) (blossomRepresentative cycle base y)) :
    (state.contract (contractionCycle (state.traceToRoot a) (state.traceToRoot b) base).toFinset base).valid mate tight' := by
  let cycle := (contractionCycle (state.traceToRoot a) (state.traceToRoot b) base).toFinset
  let leftLeg := traceBefore base (state.traceToRoot a) ++ [base]
  let rightLeg := traceBefore base (state.traceToRoot b) ++ [base]
  obtain ⟨aHead, aDistinct, _, aTrail, _⟩ := AlternatingForestState.traceToRoot_spec valid (x := a) (by simp [aOuter])
  obtain ⟨bHead, bDistinct, _, bTrail, _⟩ := AlternatingForestState.traceToRoot_spec valid (x := b) (by simp [bOuter])
  have aChain := aTrail.imp (fun _ _ h => h.1)
  have bChain := bTrail.imp (fun _ _ h => h.1)
  obtain ⟨_, baseOuter⟩ := common_base_outer valid ancestor aHead bHead aOuter bOuter aChain bChain
  obtain ⟨baseInA, beforeB, afterB, splitB, _⟩ := firstSharedAncestor_eq_some_iff.mp ancestor
  have baseInB : base ∈ state.traceToRoot b := splitB.symm ▸ List.mem_append_right beforeB (by simp)
  have left := trace_leg_valid valid baseInA aOuter aHead aDistinct aChain
  have right := trace_leg_valid valid baseInB bOuter bHead bDistinct bChain
  have membership (x : Fin n) : x ∈ cycle ↔ x ∈ leftLeg ∨ x ∈ rightLeg := by
    simp only [cycle, leftLeg, rightLeg, contractionCycle, List.mem_toFinset, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, List.mem_reverse]
    tauto
  refine AlternatingForestState.contract_valid valid cycle base baseOuter ?_ ?_ ?_ preservesEdges
  · intro x hx
    exact ((membership x).mp hx).elim (left.1 x) (right.1 x)
  · intro x hx different p parent
    rcases (membership x).mp hx with aSide | bSide
    · exact (membership p).mpr (Or.inl (left.2.1 x aSide different p parent))
    · exact (membership p).mpr (Or.inr (right.2.1 x bSide different p parent))
  · intro x hx p inner y matched
    rcases (membership x).mp hx with aSide | bSide
    · exact (membership y).mpr (Or.inl (left.2.2 x aSide p inner y matched))
    · exact (membership y).mpr (Or.inr (right.2.2 x bSide p inner y matched))

end VehicleRoutingSurvey.Routing
end RppSource_AlternatingContractionParity

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

/-- If a dual slot is enabled at one representative, the scan shifts it just once. -/
theorem iterateBlossomDuals_only_row (s : ArithmeticState) {n i : ℕ}
    (inside : i < n) (present : blossomNodeAt s i ≠ 0) (marked : blossomRoleAt s i ≠ 0)
    (unique : ∀ j < n, j ≠ i → blossomNodeAt s j ≠ 0 →
      blossomRoleAt s j ≠ 0 → blossomNodeAt s i ≠ blossomNodeAt s j) :
    iterateBlossomDuals s n (s.nr 75 + blossomNodeAt s i) = blossomDualAfterDelta s i := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases last : i = n
    · subst n
      have earlier := iterateBlossomDuals_keeps_address s i (s.nr 75 + blossomNodeAt s i)
        (fun j hj node role => by
          have different := unique j (Nat.lt.step hj) hj.ne node role
          exact fun h => different (Nat.add_left_cancel h))
      simp only [iterateBlossomDuals, modifyBlossomDualAt_with_real, present, marked, false_or, if_false,
        Function.update_self]
      change (if blossomRoleAt s i ≤ 1 then iterateBlossomDuals s i (s.nr 75 + blossomNodeAt s i) + s.rr 1
        else iterateBlossomDuals s i (s.nr 75 + blossomNodeAt s i) - s.rr 1) = _
      rw [earlier]
      rfl
    · have prev := ih (by omega) (fun j hj => unique j (Nat.lt.step hj))
      by_cases skip : blossomNodeAt s n = 0 ∨ blossomRoleAt s n = 0
      · simpa only [iterateBlossomDuals, modifyBlossomDualAt_with_real, if_pos skip] using prev
      · push_neg at skip
        have different := unique n (Nat.lt_succ_self _) (Ne.symm last) skip.1 skip.2
        have address : s.nr 75 + blossomNodeAt s i ≠ s.nr 75 + blossomNodeAt s n :=
          fun h => different (Nat.add_left_cancel h)
        simpa only [iterateBlossomDuals, modifyBlossomDualAt_with_real, skip.1, skip.2, false_or, if_false,
          Function.update_of_ne address] using prev



private theorem MatchingSearchDualMemory.advanced_effective {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    (before : MatchingSearchDualMemory part forest s) (positive : 0 < k) (v : Fin k) :
    advancedEffectiveMemory s (s.nr 62 + v.val) =
      effectiveVertexPotential state.cuts
        (fun x => state.potential x + s.rr 1 * forestVertexDirection part.blocks (part.dualLabel forest positive) x)
        (fun B => state.cutDual B + s.rr 1 * forestCutDirection part.blocks (part.dualLabel forest positive) B) v := by
  have within : s.nr 62 ≤ s.nr 62 + v.val ∧ s.nr 62 + v.val < s.nr 62 + s.nr 55 := by
    rw [before.dimension]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left v.isLt _⟩
  rw [effectiveVertexPotential_shift _ _ _ _ _ (Finset.mem_univ v), part.dualLabel_block,
    advancedEffectiveMemory, if_pos within, Nat.add_sub_cancel_left, effectivePotentialAfterDelta,
    effectiveRoleAt, before.reps, (before.roles _).1, before.effective]
  cases (forest.role (part.representative v)) <;>
    norm_num [alternatingRoleCode, AlternatingForestRole.dualDirection, sub_eq_add_neg]

theorem MatchingSearchDualMemory.advanced_effective_table {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s t : ArithmeticState}
    (before : MatchingSearchDualMemory part forest s) (positive : 0 < k)
    (after : t.rm = iterateBlossomDuals {s with rm := advancedEffectiveMemory s} (s.nr 55))
    (base : t.nr 62 = s.nr 62) (v : Fin k) :
    t.rm (t.nr 62 + v.val) = effectiveVertexPotential state.cuts
      (fun x => state.potential x + s.rr 1 * forestVertexDirection part.blocks (part.dualLabel forest positive) x)
      (fun B => state.cutDual B + s.rr 1 * forestCutDirection part.blocks (part.dualLabel forest positive) B) v := by
  rw [after, base, iterateBlossomDuals_keeps_address]
  · exact before.advanced_effective positive v
  · intro i _ _ _
    change s.nr 62 + v.val ≠ s.nr 75 + blossomNodeAt s i
    have h := v.isLt
    have sep := before.separated
    omega

private theorem MatchingSearchDualMemory.nodeAt_eq_iff {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    (before : MatchingSearchDualMemory part forest s) {B : Finset (Fin k)} (inCuts : B ∈ state.cuts)
    (v : Fin k) : blossomNodeAt s v = before.node B ↔
      part.representative v = v ∧ (part.blocks.block v).card ≠ 1 ∧ part.blocks.block v = B := by
  rw [before.top]
  by_cases live : part.representative v = v ∧ (part.blocks.block v).card ≠ 1
  · rw [if_pos live]
    have cut := part.blocks.cut_mem (Finset.mem_univ v) live.2
    exact ⟨fun equal => ⟨live.1, live.2, before.nodeInjective cut inCuts equal⟩,
      fun h => congrArg before.node h.2.2⟩
  · rw [if_neg live]
    exact ⟨fun equal => (before.nodeNonzero B inCuts equal.symm).elim,
      fun h => (live ⟨h.1, h.2.1⟩).elim⟩

/-- A top-level cut changes by its representative's label. Hidden cuts retain
their dual value because they have no row in the top-level table. -/
theorem MatchingSearchDualMemory.advanced_cut_table {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s t : ArithmeticState}
    (before : MatchingSearchDualMemory part forest s) (positive : 0 < k)
    (after : t.rm = iterateBlossomDuals {s with rm := advancedEffectiveMemory s} (s.nr 55))
    (base : t.nr 75 = s.nr 75) {B : Finset (Fin k)} (inCuts : B ∈ state.cuts) :
    t.rm (t.nr 75 + before.node B) = state.cutDual B +
      s.rr 1 * forestCutDirection part.blocks (part.dualLabel forest positive) B := by
  let seed := {s with rm := advancedEffectiveMemory s}
  let address := s.nr 75 + before.node B
  have seedValue : seed.rm address = state.cutDual B := by
    have outside : ¬ (s.nr 62 ≤ address ∧ address < s.nr 62 + s.nr 55) := by
      rw [before.dimension]
      have sep := before.separated
      dsimp [address]
      omega
    simpa only [seed, advancedEffectiveMemory, if_neg outside, address] using before.cutValues B inCuts
  rw [after, base]
  change iterateBlossomDuals seed (s.nr 55) address = _
  by_cases top : B ∈ Finset.univ.image part.blocks.block ∧ B.card ≠ 1
  · obtain ⟨v, _, setEq⟩ := Finset.mem_image.mp top.1
    let r := part.representative v
    have rBlock : part.blocks.block r = B :=
      (part.blocks.same_of_mem (Finset.mem_univ v) (part.inside v)).trans setEq
    have words : blossomNodeAt seed r = before.node B :=
      (before.nodeAt_eq_iff inCuts r).mpr ⟨part.representative_idem v, rBlock.symm ▸ top.2, rBlock⟩
    have rRep : part.representativeOf positive B = r := setEq ▸ part.representativeOf_block positive v
    have rRole : blossomRoleAt seed r = alternatingRoleCode (forest.role r) := (before.roles r).1
    have unique {i : ℕ} (hi : i < s.nr 55) (eqNode : blossomNodeAt seed i = before.node B) : i = r.val := by
      let w : Fin k := ⟨i, before.dimension ▸ hi⟩
      obtain ⟨fixed, _, shape⟩ := (before.nodeAt_eq_iff inCuts w).mp eqNode
      exact congrArg Fin.val (fixed.symm.trans (part.constant w v (shape.trans setEq.symm)))
    rw [forestCutDirection, if_pos top, CompactMatchingPartition.dualLabel, rRep]
    by_cases idle : forest.role r = .unlabelled
    · rw [iterateBlossomDuals_keeps_address, seedValue]
      · simp [idle, AlternatingForestRole.dualDirection]
      · intro i hi _ marked hit
        have eqNode : blossomNodeAt seed i = before.node B :=
          (Nat.add_left_cancel (show s.nr 75 + before.node B = s.nr 75 + blossomNodeAt seed i from hit)).symm
        have same := unique hi eqNode
        rw [same, rRole, idle] at marked
        exact marked rfl
    · have rInside : r.val < s.nr 55 := before.dimension.symm ▸ r.isLt
      have rPresent : blossomNodeAt seed r ≠ 0 := words.trans_ne (before.nodeNonzero B inCuts)
      have rMarked : blossomRoleAt seed r ≠ 0 := by
        rw [rRole]
        cases kind : forest.role r <;> simp_all [alternatingRoleCode]
      have only := iterateBlossomDuals_only_row seed rInside rPresent rMarked (fun i hi other _ _ eqNode =>
        other (unique hi (eqNode.symm.trans words)))
      have addressEq : seed.nr 75 + blossomNodeAt seed r = address := by
        change s.nr 75 + blossomNodeAt seed r = _
        rw [words]
      rw [addressEq] at only
      rw [only, blossomDualAfterDelta, addressEq, seedValue, rRole]
      change (if alternatingRoleCode (forest.role r) ≤ 1 then state.cutDual B + s.rr 1
        else state.cutDual B - s.rr 1) = _
      cases kind : forest.role r <;> simp_all [alternatingRoleCode, AlternatingForestRole.dualDirection, sub_eq_add_neg]
  · rw [forestCutDirection, if_neg top, mul_zero, add_zero, iterateBlossomDuals_keeps_address]
    · exact seedValue
    · intro i hi _ _ hit
      have eqNode : blossomNodeAt seed i = before.node B :=
        (Nat.add_left_cancel (show s.nr 75 + before.node B = s.nr 75 + blossomNodeAt seed i from hit)).symm
      let v : Fin k := ⟨i, before.dimension ▸ hi⟩
      obtain ⟨_, notOne, shape⟩ := (before.nodeAt_eq_iff inCuts v).mp eqNode
      exact top ⟨Finset.mem_image.mpr ⟨v, Finset.mem_univ v, shape⟩, shape ▸ notOne⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingSearchDualRAM

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

/-! matching/MatchingActiveSelection.lean -/
section RppSource_MatchingActiveSelection
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



theorem MatchingCandidateGroup.slot_lt {k : ℕ} (g : MatchingCandidateGroup k) : g.slot < 3 * k := by
  cases g with
  | outer u | incoming u | cut u => have := u.isLt; simp [MatchingCandidateGroup.slot] <;> omega








end VehicleRoutingSurvey.Routing
end RppSource_MatchingActiveSelection

/-! matching/MatchingTypedDispatch.lean -/
section RppSource_MatchingTypedDispatch
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



/-- Interpret the physical event class using the positive rate of the selected
constraint. This identifies the two trace roots or the exposed growth endpoint. -/
theorem matchingEventClass_of_adjustment {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) (blocks : TopLevelMatchingBlocks Finset.univ state.cuts)
    (forest : AlternatingForestState (Fin k)) (rep : Finset (Fin k) → Fin k)
    (cutAt : Fin k → Finset (Fin k)) {s : ArithmeticState} {event : MatchingDualEvent k} {step : ℝ}
    (size : s.nr 55 = k) (encoded : AlternatingForestMemory forest (s.nr 51) s.nm)
    (representatives : ∀ v : Fin k, s.nm (s.nr 57 + v.val) = (rep (blocks.block v)).val)
    (words : MatchingEventRecord cutAt (matchingOriginalGrowthEvent s) event)
    (valid : let label := fun B => (forest.role (rep B)).dualDirection
      MatchingDualAdjustment cost (compactMatchingEdges k) state.cuts state.potential
        (forestVertexDirection blocks label) state.cutDual (forestCutDirection blocks label) ⟨event, step⟩) :
    MatchingEventClassView blocks forest rep cutAt s event := by
  unfold MatchingEventClassView
  let label := fun B => (forest.role (rep B)).dualDirection
  cases event with
  | cut S =>
    obtain ⟨u, ports, setEq⟩ := words
    have decreasing : forestCutDirection blocks label S < 0 := valid.2.2.2.2.1
    obtain ⟨⟨top, nontrivial⟩, parent, inner⟩ :=
      (forestCutDirection_negative_iff blocks (fun B => forest.role (rep B)) S).mp decreasing
    exact ⟨u, ports, setEq, by simp [matchingEventClass, size, ports], top, nontrivial, parent, inner⟩
  | edge e =>
    obtain ⟨u, v, ports, rfl⟩ := words
    have legal : s(u, v) ∈ compactMatchingEdges k := valid.2.2.2.1
    have distinct : u ≠ v := fun same => (mem_compactMatchingEdges_iff.mp legal) (Sym2.mk_isDiag_iff.mpr same)
    have rising : 0 < oddCutDualEdgeValue state.cuts (forestVertexDirection blocks label)
        (forestCutDirection blocks label) s(u, v) := valid.2.2.2.2.1
    rw [forest_edge_slope blocks label (Finset.mem_univ u) (Finset.mem_univ v) distinct] at rising
    have separate : blocks.block u ≠ blocks.block v := by
      intro same
      rw [if_pos same] at rising
      exact (lt_irrefl _ rising).elim
    rw [if_neg separate] at rising
    let i := rep (blocks.block u)
    let j := rep (blocks.block v)
    have leftRead : matchingEventLeftRep s = i.val := by
      simpa [matchingEventLeftRep, ports, i] using representatives u
    have rightRead : matchingEventRightRep s = j.val := by
      simpa [matchingEventRightRep, ports, j] using representatives v
    have left : s.nm (s.nr 51 + i.val) = alternatingRoleCode (forest.role i) := (encoded i).1
    have right : s.nm (s.nr 51 + j.val) = alternatingRoleCode (forest.role j) := (encoded j).1
    have noCut : ¬ s.nr 55 ≤ (matchingOriginalGrowthEvent s).2 := by
      rw [size, ports]
      exact not_le_of_gt v.isLt
    refine ⟨u, v, ports, rfl, separate, leftRead, rightRead, ?_⟩
    change 0 < (forest.role i).dualDirection + (forest.role j).dualDirection at rising
    rcases (risingForestEdge_iff (forest.role i) (forest.role j)).mp rising with
      ⟨⟨p, iOuter⟩, ⟨q, jOuter⟩ | jDormant⟩ | ⟨iDormant, q, jOuter⟩
    · exact Or.inl ⟨by simp [matchingEventClass, noCut, leftRead, rightRead, left, right, iOuter, jOuter, alternatingRoleCode],
        p, q, iOuter, jOuter⟩
    · exact Or.inr ⟨by simp [matchingEventClass, noCut, leftRead, rightRead, left, right, iOuter, jDormant, alternatingRoleCode],
        Or.inl ⟨p, iOuter, jDormant⟩⟩
    · exact Or.inr ⟨by simp [matchingEventClass, noCut, leftRead, rightRead, left, right, iDormant, jOuter, alternatingRoleCode],
        Or.inr ⟨q, iDormant, jOuter⟩⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingTypedDispatch

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



theorem MatchingTopMemberTrees.tree_eq {k : ℕ} {s : ArithmeticState}
    (a b : MatchingTopMemberTrees k s) (v : Fin k) : a.tree v = b.tree v :=
  MatchingMemberTree.eq_of_encoded_rootKeys (a.proper v) (b.proper v) (a.encoded v) (b.encoded v)
    ((a.roots v).trans (b.roots v).symm)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRegistryUnique

/-! matching/MatchingExpansionSelection.lean -/
section RppSource_MatchingExpansionSelection
namespace VehicleRoutingSurvey.Routing



theorem matchingTopCutAt_port {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (positive : 0 < k) {v : Fin k} {B : Finset (Fin k)} (populated : B.Nonempty)
    (found : matchingTopCutAt part v = B) :
    part.representative v = v ∧ part.blocks.block v = B ∧ part.representativeOf positive B = v := by
  have fixed : part.representative v = v := by
    by_contra inactive
    have same := (if_neg inactive : (if part.representative v = v then part.blocks.block v else ∅) = ∅)
    have empty : B = ∅ := found.symm.trans same
    exact (Finset.nonempty_iff_ne_empty.mp populated) empty
  have block : part.blocks.block v = B := by simpa only [matchingTopCutAt, if_pos fixed] using found
  refine ⟨fixed, block, ?_⟩
  rw [← block, part.representativeOf_block, fixed]













end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionSelection

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









end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestAugment

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

/-! matching/MatchingStageCountEncoding.lean -/
section RppSource_MatchingStageCountEncoding
namespace VehicleRoutingSurvey.Routing







theorem MatchingTopMemberTrees.live_registry_ids {k : ℕ} {s : ArithmeticState}
    (record : MatchingTopMemberTrees k s) : matchingLiveRegistryIds k s = record.registryIds := by
  have existsRecord : Nonempty (MatchingTopMemberTrees k s) := ⟨record⟩
  rw [matchingLiveRegistryIds, dif_pos existsRecord]
  unfold MatchingTopMemberTrees.registryIds
  have keys : (fun v => ((Classical.choice existsRecord).tree v).registryIds) =
      (fun v => (record.tree v).registryIds) := by
    funext v
    rw [MatchingTopMemberTrees.tree_eq (Classical.choice existsRecord) record v]
  rw [keys]







/-- Relate the mathematical stage charge to a count depending only on the
actual machine state and the first unused identifier at stage entry. -/
theorem matchingStageCountsFromRAM_eq {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    (dual : MatchingSearchDualMemory part forest s) (positive : 0 < k) (initialNode : ℕ)
    (records : MatchingTopMemberTrees k s) (unique : records.registryIds.Nodup)
    (keys : ∀ n, n ∈ records.registryIds ↔ ∃ B ∈ state.cuts, dual.node B = n) :
    let inherited := state.cuts.filter fun B => dual.node B < initialNode
    matchingStageCountsFromRAM k s initialNode =
      matchingPartitionCounts part.blocks (part.outerBlock forest positive) inherited := by
  intro inherited
  let rep := part.representativeOf positive
  let outer := part.outerBlock forest positive
  let top := (Finset.univ.image part.blocks.block).filter outer
  let actual := (Finset.univ : Finset (Fin k)).filter (fun v => s.nm (s.nr 57 + v.val) = v.val ∧ s.nm (s.nr 51 + v.val) = 1)
  have code (v : Fin k) : s.nm (s.nr 51 + v.val) = alternatingRoleCode (forest.role v) := (dual.roles v).1
  have readLabel (v : Fin k) : s.nm (s.nr 51 + s.nm (s.nr 57 + v.val)) =
      alternatingRoleCode (forest.role (rep (part.blocks.block v))) := by
    rw [dual.reps, code, show rep (part.blocks.block v) = part.representative v from part.representativeOf_block positive v]
  have innerCount : ((Finset.univ : Finset (Fin k)).filter
      (fun v => s.nm (s.nr 51 + s.nm (s.nr 57 + v.val)) ≠ 1)) =
      Finset.univ.filter (fun v => ¬outer (part.blocks.block v)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, readLabel] <;> rfl
  have outerImage : top.image rep = actual := by
    ext u
    change u ∈ top.image rep ↔ u ∈ actual
    constructor
    · intro member
      obtain ⟨B, inTop, same⟩ := Finset.mem_image.mp member
      obtain ⟨inImage, label⟩ := Finset.mem_filter.mp inTop
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp inImage
      have eq : part.representative v = u := (part.representativeOf_block positive v).symm.trans same
      have repFixed : part.representative u = u := eq ▸ part.representative_idem v
      have uOuter : alternatingRoleCode (forest.role u) = 1 := same ▸ label
      simp [actual, dual.reps, code, repFixed, uOuter]
    · intro member
      obtain ⟨_, stable, marked⟩ := Finset.mem_filter.mp member
      have fixed : part.representative u = u := Fin.ext ((dual.reps u).symm.trans stable)
      have name : rep (part.blocks.block u) = u := (part.representativeOf_block positive u).trans fixed
      have uOuter : alternatingRoleCode (forest.role u) = 1 := (code u).symm.trans marked
      refine Finset.mem_image.mpr ⟨part.blocks.block u, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, name⟩
      change alternatingRoleCode (forest.role (rep (part.blocks.block u))) = 1
      rw [name]
      exact uOuter
  have outerInj : Set.InjOn rep (↑top : Set (Finset (Fin k))) := by
    intro B inB C inC same
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp inB).1
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp inC).1
    change part.representativeOf positive (part.blocks.block u) = part.representativeOf positive (part.blocks.block v) at same
    rw [part.representativeOf_block, part.representativeOf_block] at same
    exact part.same_block.mp same
  have innerRegistry : (records.registryIds.filter fun id => decide (id < initialNode)).toFinset = inherited.image dual.node := by
    ext id
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, keys, Finset.mem_image, inherited, Finset.mem_filter]
    constructor
    · rintro ⟨⟨B, member, rfl⟩, small⟩
      exact ⟨B, ⟨member, small⟩, rfl⟩
    · rintro ⟨B, ⟨member, small⟩, rfl⟩
      exact ⟨⟨B, member, rfl⟩, small⟩
  have inheritedCount : (records.registryIds.filter fun id => decide (id < initialNode)).length = inherited.card := by
    rw [← List.toFinset_card_of_nodup (unique.filter _), innerRegistry]
    apply Finset.card_image_of_injOn
    intro B left C right same
    exact dual.nodeInjective (Finset.mem_filter.mp left).1 (Finset.mem_filter.mp right).1 same
  have outerCount : actual.card = top.card := by rw [← outerImage, Finset.card_image_of_injOn outerInj]
  unfold matchingStageCountsFromRAM matchingPartitionCounts
  rw [innerCount, records.live_registry_ids, inheritedCount, outerCount]


end VehicleRoutingSurvey.Routing
end RppSource_MatchingStageCountEncoding

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

/-- The guard is preserved by appending one fresh cycle at the current
allocation cursor and leaving all older headers alone. -/
theorem MatchingCycleRecordOrder.append {s t : ArithmeticState} (order : MatchingCycleRecordOrder s)
    (scratch : matchingRebaseScratchEnd t = matchingRebaseScratchEnd s)
    (cursor : t.nr 76 = s.nr 76 + 1) (extended : s.nr 68 ≤ t.nr 68)
    (priorStart : ∀ i, 0 < i → i < s.nr 76 → matchingCycleRecordStart t i = matchingCycleRecordStart s i)
    (priorEnd : ∀ i, 0 < i → i < s.nr 76 → matchingCycleRecordEnd t i = matchingCycleRecordEnd s i)
    (start : matchingCycleRecordStart t (s.nr 76) = s.nr 68)
    (fits : matchingCycleRecordEnd t (s.nr 76) ≤ t.nr 68) : MatchingCycleRecordOrder t := by
  have oldCursor := order.cursor
  refine ⟨scratch.symm ▸ order.scratch.trans extended, by omega, ?_, ?_⟩
  · intro i positive inRange
    by_cases added : i = s.nr 76
    · subst i
      rw [scratch, start]
      exact ⟨order.scratch, fits⟩
    · have earlier : i < s.nr 76 := by omega
      rw [scratch, priorStart i positive earlier, priorEnd i positive earlier]
      exact ⟨(order.bounded i positive earlier).1, (order.bounded i positive earlier).2.trans extended⟩
  · intro left right positive before inRange
    have earlier : left < s.nr 76 := by omega
    rw [priorEnd left positive earlier]
    by_cases added : right = s.nr 76
    · subst right
      rw [start]
      exact (order.bounded left positive earlier).2
    · have rightEarlier : right < s.nr 76 := by omega
      have rightPositive : 0 < right := positive.trans before
      rw [priorStart right rightPositive rightEarlier]
      exact order.ordered left right positive before rightEarlier


end VehicleRoutingSurvey.Routing
end RppSource_MatchingCycleRecordOrder

/-! matching/MatchingBlossomRegistry.lean -/
section RppSource_MatchingBlossomRegistry
namespace VehicleRoutingSurvey.Routing



theorem matchingBlossomCapacity_enough {k stages events : ℕ}
    (stageCount : stages + stages ≤ k) (eventCount : events ≤ 6 * k * stages) :
    events < matchingBlossomCapacity k := by
  have capacity : events ≤ 3 * (k * k) := by
    calc
      events ≤ 6 * k * stages := eventCount
      _ = (3 * k) * (stages + stages) := by ring
      _ ≤ (3 * k) * k := Nat.mul_le_mul_left _ stageCount
      _ = 3 * (k * k) := Nat.mul_assoc _ _ _
  simpa only [matchingBlossomCapacity, Nat.lt_succ_iff] using capacity















end VehicleRoutingSurvey.Routing
end RppSource_MatchingBlossomRegistry

/-! matching/MatchingRegistryBudget.lean -/
section RppSource_MatchingRegistryBudget
namespace VehicleRoutingSurvey.Routing





theorem MatchingRegistryBudget.keeps {k stage : ℕ} {s t : ArithmeticState} {before after : MatchingStageCounts}
    (budget : MatchingRegistryBudget k stage s before) (cutoff : t.nr 39 = s.nr 39)
    (cursor : t.nr 76 = s.nr 76) (counts : after = before) : MatchingRegistryBudget k stage t after := by
  refine ⟨cutoff.trans_le budget.cutoff, ?_, cutoff.trans_le (budget.cutoff_le_cursor.trans_eq cursor.symm)⟩
  rw [cutoff,cursor,counts]
  exact budget.allowance

theorem MatchingRegistryBudget.can_allocate {k stage : ℕ} {s : ArithmeticState} {counts : MatchingStageCounts}
    (budget : MatchingRegistryBudget k stage s counts) (searching : stage < k / 2) (credit : 0 < counts.credit) :
    s.nr 76 < matchingBlossomCapacity k := by
  have cut := budget.cutoff
  have remaining := budget.allowance
  have next : 6 * k * (stage + 1) = 6 * k * stage + 6 * k := by rw [Nat.mul_succ]
  have under : s.nr 76 ≤ 6 * k * (stage + 1) := by omega
  exact matchingBlossomCapacity_enough (stages := stage + 1) (by omega) under

theorem MatchingRegistryBudget.advance {k stage charge : ℕ} {s t : ArithmeticState}
    {before after : MatchingStageCounts} (budget : MatchingRegistryBudget k stage s before)
    (transition : MatchingStageTransition before charge after) (cutoff : t.nr 39 = s.nr 39)
    (monotone : s.nr 76 ≤ t.nr 76) (allocated : t.nr 76 ≤ s.nr 76 + 1) :
    MatchingRegistryBudget k stage t after := by
  have old := budget.allowance
  have spend := transition.charge_le
  have positive := transition.charge_pos
  exact ⟨cutoff.trans_le budget.cutoff, by omega, cutoff.trans_le (budget.cutoff_le_cursor.trans monotone)⟩




end VehicleRoutingSurvey.Routing
end RppSource_MatchingRegistryBudget

/-! matching/MatchingLiveCycleSameMemory.lean -/
section RppSource_MatchingLiveCycleSameMemory
namespace VehicleRoutingSurvey.Routing

/-- The two counted-loop snapshots use private registers. The physical
cycle, membership map bounds, and every original endpoint remain readable. -/
def MatchingLiveCycleMemory.sameMemory {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    {e : MatchingLiveCycle state node B} {s t : ArithmeticState} (stored : MatchingLiveCycleMemory e s)
    (words : t.nm = s.nm) (ports : ∀ r ∈ ([55,77,78,79,80] : List ℕ), t.nr r = s.nr r) :
    MatchingLiveCycleMemory e t := by
  have fixed (r : ℕ) (used : r ∈ ([55,77,78,79,80] : List ℕ) := by decide) := ports r used
  let a := matchingRebaseNodeState s (node B)
  let b := matchingRebaseNodeState t (node B)
  have regs (r : ℕ) (used : r ∈ ([55,77,78,79,80] : List ℕ) := by decide) : b.nr r = a.nr r := by
    have away : r ≠ 22 := by simp at used; omega
    simpa [a, b, matchingRebaseNodeState, Function.update_of_ne away] using fixed r used
  have same : b.nm = a.nm := words
  have root : b.nr 22 = a.nr 22 := by simp [a, b, matchingRebaseNodeState]
  have scratch : outsideMatchingMemberScratch b = outsideMatchingMemberScratch a := by
    funext address
    simp only [outsideMatchingMemberScratch, regs 55, regs 79, regs 80]
  have old : MatchingMemberRoot a e.tree := stored.members
  have members : MatchingMemberRoot b e.tree := by
    refine ⟨?_, ?_, ?_, ?_, old.unique, ?_, ?_⟩
    · rw [root]; exact old.proper
    · rw [root, same, regs 77, regs 78]; exact old.encoded
    · rw [root, same, regs 77, regs 78, scratch]; exact old.readable
    · rw [root, same, regs 77, regs 80, regs 55]; exact old.above
    · rw [regs 55]; exact old.valid
    · rw [regs 79, regs 55, regs 80]; exact old.separated
  refine ⟨members, ⟨?_, ?_⟩⟩
  · rw [words, fixed 78]; exact stored.rows.length
  · intro i
    simpa only [matchingCycleRecordStart, fixed 77, words] using stored.rows.records i


end VehicleRoutingSurvey.Routing
end RppSource_MatchingLiveCycleSameMemory

/-! matching/MatchingRefreshRows.lean -/
section RppSource_MatchingRefreshRows
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096



def matchingRefreshTableRegisters : List ℕ := [20, 21, 51, 54, 55, 57, 58, 59, 60, 61, 62, 65, 66]

theorem MatchingRefreshInput.keeps {k : ℕ} {s t : ArithmeticState} {rep : Fin k → Fin k}
    {role : Fin k → ℕ} {cost : Fin k → Fin k → ℝ} {effective : Fin k → ℝ}
    (input : MatchingRefreshInput s rep role cost effective) (memory : CacheMemoryFrame s t)
    (fixed : ∀ r ∈ matchingRefreshTableRegisters, t.nr r = s.nr r) : MatchingRefreshInput t rep role cost effective := by
  have port (r : ℕ) (used : r ∈ matchingRefreshTableRegisters := by decide) : t.nr r = s.nr r := fixed r used
  have rates : s.nr 59 ≤ s.nr 60 := by have h := input.layout.slacksBefore; omega
  have pair : s.nr 59 ≤ s.nr 66 := by
    have a := input.layout.slacksBefore
    have b := input.layout.ratesBefore
    omega
  have layout : MatchingCacheLayout k t := by
    refine ⟨(port 55).trans input.layout.dimension, (port 61).trans input.layout.rows, ?_, ?_, ?_, ?_⟩
    · rw [port 58, port 61, port 54]; exact input.layout.idsBefore
    · rw [port 54, port 61, port 65]; exact input.layout.recordsBefore
    · rw [port 59, port 61, port 60]; exact input.layout.slacksBefore
    · rw [port 60, port 61, port 66]; exact input.layout.ratesBefore
  refine ⟨layout, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [port 21, port 58]; exact input.offsetsBefore
  · rw [port 57, port 58]; exact input.representativesBefore
  · rw [port 51, port 58]; exact input.rolesBefore
  · rw [port 20, port 59]; exact input.metricBefore
  · rw [port 62, port 59]; exact input.effectiveBefore
  · intro j
    rw [port 21, memory.natural _ (by have a := input.offsetsBefore; have b := j.isLt; omega)]
    exact input.offsets j
  · intro j
    rw [port 57, memory.natural _ (by have a := input.representativesBefore; have b := j.isLt; omega)]
    exact input.representatives j
  · intro j
    rw [port 51, memory.natural _ (by have a := input.rolesBefore; have b := j.isLt; omega)]
    exact input.roles j
  · intro i j
    have next := Nat.mul_le_mul_left k (Nat.succ_le_of_lt i.isLt)
    rw [Nat.mul_succ] at next
    have slot : k * i.val + j.val < k*k := by have h := j.isLt; omega
    have room : s.nr 20 + k*i.val + j.val < s.nr 59 := by have h := input.metricBefore; omega
    rw [port 20, memory.real _ room rates pair]
    exact input.metric i j
  · intro j
    have room : s.nr 62 + j.val < s.nr 59 := by have a := input.effectiveBefore; have b := j.isLt; omega
    rw [port 62, memory.real _ room rates pair]
    exact input.potentials j











end VehicleRoutingSurvey.Routing
end RppSource_MatchingRefreshRows

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

/-! matching/AlternatingForestAncestorRAM.lean -/
section RppSource_AlternatingForestAncestorRAM
namespace VehicleRoutingSurvey.Routing

















private theorem traceBefore_eq_take_of_nodup {k : ℕ} {trail : List (Fin k)} {v : Fin k}
    (distinct : trail.Nodup) {i : ℕ} (inside : i < trail.length) (value : trail[i] = v) :
    traceBefore v trail = trail.take i := by
  have shape : trail.take i ++ (v :: trail.drop (i + 1)) = trail := by
    rw [← value, ← List.drop_eq_getElem_cons inside, List.take_append_drop]
  have absent : v ∉ trail.take i := by
    intro member
    have clean := List.nodup_append.mp (shape.symm ▸ distinct)
    exact clean.2.2 v member v (by simp) rfl
  conv_lhs => rw [← shape]
  rw [traceBefore_eq absent]

/-- In the contraction case the register lengths delimit the exact two
legs expected by `contractionCycle`. -/
theorem ForestTraceSplit.traceBefore {k : ℕ} {left right : List (Fin k)} {v : Fin k} {li ri : ℕ}
    (split : ForestTraceSplit left right (some v) li ri)
    (leftDistinct : left.Nodup) (rightDistinct : right.Nodup) :
    traceBefore v left = left.take li ∧ traceBefore v right = right.take ri := by
  obtain ⟨insideLeft, insideRight, atLeft, atRight⟩ := split.positions
  exact ⟨traceBefore_eq_take_of_nodup leftDistinct insideLeft atLeft,
    traceBefore_eq_take_of_nodup rightDistinct insideRight atRight⟩

end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestAncestorRAM

/-! matching/MatchingRegistryWitnessFrame.lean -/
section RppSource_MatchingRegistryWitnessFrame
namespace VehicleRoutingSurvey.Routing

theorem MatchingRegistryBudget.allocated_fits {k stage n : ℕ} {s : ArithmeticState} {counts : MatchingStageCounts}
    (budget : MatchingRegistryBudget k stage s counts) (searching : stage < k/2) (live : n < s.nr 76) :
    n < matchingBlossomCapacity k := by
  apply matchingBlossomCapacity_enough (stages := stage+1) (by omega)
  rw [Nat.mul_succ]
  have low := budget.cutoff
  have hi := budget.allowance
  omega






end VehicleRoutingSurvey.Routing
end RppSource_MatchingRegistryWitnessFrame

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

/-! matching/MatchingFreshCutOuter.lean -/
section RppSource_MatchingFreshCutOuter
namespace VehicleRoutingSurvey.Routing







/-- Registration adds one outer blossom and transports every older fresh cut. -/
theorem MatchingFreshCutOuter.register {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state next : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {merged : CompactMatchingPartition next} {forest after : AlternatingForestState (Fin k)}
    {oldNode node : Finset (Fin k) → ℕ} {cutoff : ℕ}
    (before : MatchingFreshCutOuter part forest oldNode cutoff) (added : Finset (Fin k))
    (cuts : next.cuts = insert added state.cuts)
    (same : ∀ B ∈ state.cuts, B ≠ added → node B = oldNode B)
    (registered : ∀ v ∈ added, (after.role (merged.representative v)).outerTag = true)
    (outer : ∀ v, (forest.role (part.representative v)).outerTag = true →
      (after.role (merged.representative v)).outerTag = true) :
    MatchingFreshCutOuter merged after node cutoff := by
  intro B present fresh v member
  by_cases isNew : B = added
  · exact registered v (isNew ▸ member)
  · have old : B ∈ state.cuts := (Finset.mem_insert.mp (cuts ▸ present)).resolve_left isNew
    exact outer v (before B old (same B old isNew ▸ fresh) v member)



end VehicleRoutingSurvey.Routing
end RppSource_MatchingFreshCutOuter

/-! matching/MatchingContractionDualSnapshot.lean -/
section RppSource_MatchingContractionDualSnapshot
namespace VehicleRoutingSurvey.Routing



theorem matchingContractionDualSnapshot_cache {s : ArithmeticState} {a : ℕ}
    (effective : s.nr 62 + s.nr 55 ≤ a) (cutDual : a < s.nr 75) :
    (matchingContractionDualSnapshot s).rm a = s.rm a := by
  change iterateBlossomDuals {s with rm := advancedEffectiveMemory s} (s.nr 55) a = _
  rw [iterateBlossomDuals_keeps_address _ _ _ (fun i _ _ _ => by
    change a ≠ s.nr 75 + blossomNodeAt s i
    omega)]
  simp [advancedEffectiveMemory, not_lt_of_ge effective]




/-- The contraction prefix's cache region excludes both dual arrays. -/
theorem MatchingContractionPrefixView.dualSnapshot {s t : ArithmeticState}
    (view : MatchingContractionPrefixView s t) :
    MatchingContractionPrefixView (matchingContractionDualSnapshot s) t :=
  ⟨⟨view.writer.allocation⟩, view.absorbedCount, view.freshCount, view.absorbed, view.fresh, view.cacheNatural,
    fun a low high => (view.cacheReal a low high).trans (matchingContractionDualSnapshot_cache (s := s) low high).symm,
    view.representative, view.topNodes, view.cycleMask, view.forest⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionDualSnapshot

/-! matching/MatchingLiveCyclesSameNodes.lean -/
section RppSource_MatchingLiveCyclesSameNodes
namespace VehicleRoutingSurvey.Routing

def MatchingLiveCycle.changeIds {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {old new : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    (entry : MatchingLiveCycle state old B) (same : new = old) : MatchingLiveCycle state new B :=
  ⟨entry.base, entry.tree, entry.ports, entry.geometry, entry.arity, entry.keys,
    entry.owner, by rw [same]; exact entry.childNode, entry.descendants, entry.internal, entry.matchedRow⟩

/-- A warm search changes the forest labels. Each previously allocated
cycle remains available under its own ID at the new memory state. -/
def MatchingLiveCycles.sameNodes {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    {part : CompactMatchingPartition state} {before after : AlternatingForestState (Fin k)} {s t : ArithmeticState}
    {old : MatchingSearchDualMemory part before s} {new : MatchingSearchDualMemory part after t}
    {oldReg : MatchingRegistryView old} (live : MatchingLiveCycles oldReg) (newReg : MatchingRegistryView new)
    (ids : new.node = old.node) (trees : newReg.trees.tree = oldReg.trees.tree)
    (physical : ∀ B h, MatchingLiveCycleMemory (live.entry B h) t) : MatchingLiveCycles newReg := by
  let e (B : Finset (Fin k)) (h : B ∈ state.cuts) := (live.entry B h).changeIds ids
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro B h
    refine ⟨?_, ?_⟩
    · change MatchingMemberRoot (matchingRebaseNodeState t (new.node B)) (live.entry B h).tree
      rw [ids]
      exact (physical B h).members
    · change MatchingNodeCycleRows t (new.node B) (live.entry B h).geometry.cycle (live.entry B h).geometry.edges
      rw [ids]
      exact (physical B h).rows
  · intro p h fixed
    obtain ⟨base, tree⟩ := live.top p h fixed
    exact ⟨base, (congrFun trees p).trans (by simpa only [ids] using! tree)⟩
  · intro B h job listed sub child
    obtain ⟨C, hc, id, data, row, block⟩ := live.child B h job listed sub child
    exact ⟨C, hc, (congrFun ids C).trans id, data, row, block⟩
  · intro B h n member
    simpa only [MatchingTopMemberTrees.registryIds, trees] using live.ids B h n member


end VehicleRoutingSurvey.Routing
end RppSource_MatchingLiveCyclesSameNodes

/-! matching/MatchingLiveCycleRegion.lean -/
section RppSource_MatchingLiveCycleRegion
namespace VehicleRoutingSurvey.Routing

/-- An archive can be transported across writes at any addresses disjoint
from its headers and records. The same frame covers the recursive member
tree encoding and the two original endpoint words used for expansion. -/
def MatchingLiveCycleMemory.onRegion {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    {e : MatchingLiveCycle state node B} {s t : ArithmeticState} (memory : MatchingLiveCycleMemory e s)
    {region : ℕ → Prop}
    (coverage : (MatchingMemberTree.blossom 0 (node B) e.tree .nil).readable s.nm (s.nr 77) (s.nr 78) region)
    (ports : ∀ r ∈ ([55,77,78,79,80] : List ℕ), t.nr r = s.nr r)
    (natural : ∀ a, region a → t.nm a = s.nm a) : MatchingLiveCycleMemory e t := by
  have fixed (r : ℕ) (used : r ∈ ([55,77,78,79,80] : List ℕ) := by decide) := ports r used
  let root := MatchingMemberTree.blossom 0 (node B) e.tree .nil
  have words : root.readable s.nm (s.nr 77) (s.nr 78) region := coverage
  let a := matchingRebaseNodeState s (node B)
  let b := matchingRebaseNodeState t (node B)
  have old : MatchingMemberRoot a e.tree := memory.members
  have reg (r : ℕ) (allowed : r ∈ ([55,77,78,79,80] : List ℕ) := by decide) : b.nr r = a.nr r := by
    have away : r ≠ 22 := by simp at allowed; omega
    simpa [a,b,matchingRebaseNodeState,Function.update_of_ne away] using fixed r allowed
  have common : outsideMatchingMemberScratch b = outsideMatchingMemberScratch a := by
    funext x; simp only [outsideMatchingMemberScratch, reg 79, reg 80, reg 55]
  have before : root.readable s.nm (s.nr 77) (s.nr 78) (outsideMatchingMemberScratch a) := by
    simpa only [root,a,matchingRebaseNodeState,Function.update_self,
      Function.update_of_ne (by decide : 77 ≠ 22),Function.update_of_ne (by decide : 78 ≠ 22)] using old.readable
  have encoding : root.encoded s.nm (s.nr 77) (s.nr 78) := by
    simpa [root,a,matchingRebaseNodeState] using old.encoded
  have lower : root.recordsAbove s.nm (s.nr 77) (s.nr 80+3*s.nr 55) := by
    simpa [root,a,matchingRebaseNodeState] using old.above
  have members : MatchingMemberRoot b e.tree := by
    have id : b.nr 22 = a.nr 22 := by simp [a,b,matchingRebaseNodeState]
    refine ⟨by rw [id]; exact old.proper, ?_, ?_, ?_, old.unique, by rw [reg 55]; exact old.valid,
      by rw [reg 79,reg 55,reg 80]; exact old.separated⟩
    · simpa [root,b,matchingRebaseNodeState,fixed 77,fixed 78] using
        (MatchingMemberTree.encoded_congr encoding words natural)
    · rw [common]
      simpa only [root,b,matchingRebaseNodeState,Function.update_self,
        Function.update_of_ne (by decide : 77 ≠ 22),Function.update_of_ne (by decide : 78 ≠ 22),fixed 77,fixed 78] using
        (MatchingMemberTree.readable_after_move (tree := root) (MatchingMemberTree.readableAnd (tree := root) words before) natural)
    · simpa [root,b,matchingRebaseNodeState,fixed 77,fixed 80,fixed 55] using
        (MatchingMemberTree.recordsAbove_after_move words lower natural)
  have start : matchingCycleRecordStart t (node B) = matchingCycleRecordStart s (node B) := by
    rw [matchingCycleRecordStart,fixed 77]
    exact natural _ words.1
  refine ⟨members, ⟨?_, ?_⟩⟩
  · rw [fixed 78,natural _ words.2.1]
    exact memory.rows.length
  · intro i
    let addr := matchingCycleRecordStart s (node B)+4*i.val
    have within : i.val < e.tree.arity := e.arity.symm ▸ i.isLt
    have byte (w : ℕ) (bound : w < 4) : t.nm (addr+w) = s.nm (addr+w) :=
      natural _ (words.2.2.1 i.val within w bound)
    have first : t.nm addr = s.nm addr := byte 0 (by decide)
    have cell : matchingCycleChildAt t.nm addr = matchingCycleChildAt s.nm addr := by
      simp only [matchingCycleChildAt,first,byte 1 (by decide),byte 2 (by decide),byte 3 (by decide)]
    simpa only [start, show matchingCycleChildAt t.nm (matchingCycleRecordStart s (node B) + 4*i.val) = _ from cell]
      using memory.rows.records i

end VehicleRoutingSurvey.Routing
end RppSource_MatchingLiveCycleRegion

/-! matching/MatchingDispatchTraceFrame.lean -/
section RppSource_MatchingDispatchTraceFrame
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

private theorem matchingTraceKeepsDictionary {k id : ℕ} {s t : ArithmeticState}
    (cutAt : Fin k → Finset (Fin k)) (layout : MatchingCacheLayout k s)
    (dict : t.nr 54 = s.nr 54) (bounded : id ≤ s.nr 61)
    (keep : ∀ a < s.nr 65, t.nm a = s.nm a) :
    decodeMatchingDictionaryEvent k cutAt t id = decodeMatchingDictionaryEvent k cutAt s id := by
  by_cases empty : id = 0
  · simp [decodeMatchingDictionaryEvent, empty]
  · have top := layout.recordsBefore
    have first := keep (s.nr 54 + ((id-1) + (id-1))) (by omega)
    have second := keep (s.nr 54 + ((id-1) + (id-1)) + 1) (by omega)
    simp only [decodeMatchingDictionaryEvent, dict, first, second]

private theorem matchingTraceKeepsRows {k : ℕ} {s t : ArithmeticState}
    (cutAt : Fin k → Finset (Fin k)) (layout : MatchingCacheLayout k s)
    (regs : ∀ r ∈ matchingRefreshTableRegisters, t.nr r = s.nr r)
    (real : t.rm = s.rm) (keep : ∀ a < s.nr 65, t.nm a = s.nm a)
    (valid : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i) :
    ∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧
      readMatchingCandidate cutAt t i = readMatchingCandidate cutAt s i := by
  intro i inside
  have floor := layout.idsBefore
  have ceil := layout.recordsBefore
  have words : t.nm (t.nr 58+i) = s.nm (s.nr 58+i) := by
    rw [regs 58 (by decide)]
    exact keep _ (by omega)
  have id : s.nm (s.nr 58+i) ≤ s.nr 61 := by
    rcases valid i inside with clear | ⟨row, _⟩
    · omega
    · omega
  have event := matchingTraceKeepsDictionary cutAt layout (regs 54 (by decide)) id keep
  exact ⟨by simpa only [MatchingCandidateRowValid, words, event] using valid i inside,
    by simp only [readMatchingCandidate, words, event, real, regs 59 (by decide), regs 60 (by decide)]⟩

private theorem matchingTraceKeepsBuckets {k : ℕ} {s t : ArithmeticState}
    (nodes : s.nr 74 = s.nr 65 + 2*(k*k))
    (pair : t.nr 65 = s.nr 65) (value : t.nr 66 = s.nr 66)
    (real : t.rm = s.rm) (keep : ∀ a < s.nr 74, t.nm a = s.nm a) :
    ∀ i < k*k, MatchingPairBucketValid k t i = MatchingPairBucketValid k s i ∧
      readMatchingPairBucket (k := k) t i = readMatchingPairBucket (k := k) s i := by
  intro i inside
  have first := keep (s.nr 65 + (i+i)) (by omega)
  have second := keep (s.nr 65 + (i+i) + 1) (by omega)
  exact ⟨by simp only [MatchingPairBucketValid, pair, first, second],
    by simp only [readMatchingPairBucket, pair, value, first, second, real]⟩

private def outsideMatchingTrace (k : ℕ) (s : ArithmeticState) (a : ℕ) : Prop :=
  a < s.nr 83 ∨ s.nr 83+3*k ≤ a

private theorem MatchingMemberTree.traceFootprint {k stage : ℕ} {original s : ArithmeticState}
    (tree : MatchingMemberTree) (storage : MatchingStageStorage k original s)
    (order : MatchingCycleRecordOrder s) {counts : MatchingStageCounts}
    (budget : MatchingRegistryBudget k stage s counts) (searching : stage < k/2)
    (bounds : ∀ n ∈ tree.registryIds, 0 < n ∧ n < s.nr 76) :
    tree.readable s.nm (s.nr 77) (s.nr 78) (outsideMatchingTrace k s) := by
  have headers := storage.lengths
  have trace := storage.traceLeft
  have right := storage.traceRight
  have marks := storage.traceMarks
  have witnesses := storage.witnesses
  have records := storage.records
  have promotion := storage.promotion
  have mask := storage.mask
  have map := storage.memberMap
  have stack := storage.memberStack
  induction tree with
  | nil => trivial
  | leaf _ rest ih => exact ih bounds
  | blossom _ n child rest ih tail =>
    have allocation := bounds n (by simp [MatchingMemberTree.registryIds])
    have capacity := budget.allocated_fits searching allocation.2
    have low := (order.bounded n allocation.1 allocation.2).1
    unfold matchingRebaseScratchEnd matchingCycleRecordStart at low
    refine ⟨.inl (by omega), .inl (by omega), ?_,
      ih (fun id h => bounds id (by simp [MatchingMemberTree.registryIds,h])),
      tail (fun id h => bounds id (by simp [MatchingMemberTree.registryIds,h]))⟩
    intro i _ w _
    exact .inr (by omega)

private def MatchingRegistryView.afterTrace {k stage : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {original s t : ArithmeticState}
    {old : MatchingSearchDualMemory part forest s} {new : MatchingSearchDualMemory part forest t}
    (registry : MatchingRegistryView old) (storage : MatchingStageStorage k original s)
    (order : MatchingCycleRecordOrder s) {counts : MatchingStageCounts}
    (budget : MatchingRegistryBudget k stage s counts) (searching : stage < k/2)
    (ids : new.node = old.node) (headers : t.nr 77 = s.nr 77) (lengths : t.nr 78 = s.nr 78)
    (cursor : t.nr 76 = s.nr 76) (pairs : t.nr 65 = s.nr 65)
    (top : ∀ v : Fin k, blossomNodeAt t v = blossomNodeAt s v)
    (held : ∀ a, outsideMatchingTrace k s a → t.nm a = s.nm a) : MatchingRegistryView new := by
  have area (v : Fin k) := (registry.trees.tree v).traceFootprint storage order budget searching
    (fun n inside => by
      have key := (registry.keys n).mp (List.mem_flatMap.mpr ⟨v, List.mem_finRange v, inside⟩)
      obtain ⟨B, present, rfl⟩ := key
      exact ⟨Nat.pos_of_ne_zero (old.nodeNonzero B present), registry.allocated B present⟩)
  let trees : MatchingTopMemberTrees k t := {
    tree := registry.trees.tree
    roots v := by
      change (registry.trees.tree v).rootKeys =
        (if blossomNodeAt t v = 0 then [] else [MatchingMemberTree.rootKey v.val (blossomNodeAt t v)])
      rw [top]
      exact registry.trees.roots v
    proper := registry.trees.proper
    encoded v := by
      rw [headers, lengths]
      exact MatchingMemberTree.encoded_congr (registry.trees.encoded v) (area v) held }
  refine ⟨trees, ?_, registry.unique, ?_, ?_, registry.nontrivial, registry.laminar, registry.nested⟩
  · intro v
    rw [headers, lengths, pairs]
    exact MatchingMemberTree.readable_after_move (tree := registry.trees.tree v)
      (MatchingMemberTree.readableAnd (tree := registry.trees.tree v) (area v) (registry.readable v)) held
  · intro n
    change n ∈ registry.trees.registryIds ↔ _
    rw [ids]
    exact registry.keys n
  · intro B present
    rw [ids, cursor]
    exact registry.allocated B present

set_option maxRecDepth 16384 in
/-- Outer tracing writes only the three scratch arrays. The selected event,
its cache rows, parent witnesses, and the allocated cycle archive survive. -/
noncomputable def MatchingDispatchState.afterTrace {k i : ℕ} {cost : Fin k → Fin k → ℝ}
    {original s t : ArithmeticState} (before : MatchingDispatchState cost original i s)
    (searching : i < k/2) (winner : s.nr 1 ≤ s.nr 61)
    (natural : ∀ a, a < s.nr 83 ∨ s.nr 83+3*k ≤ a → t.nm a = s.nm a)
    (real : t.rm = s.rm) (realRegs : t.rr = s.rr) (id : t.nr 1 = s.nr 1)
    (regs : ∀ r, r = 9 ∨ r = 20 ∨ r = 21 ∨ r = 39 ∨ (50 ≤ r ∧ r ≤ 90) ∨ 100 ≤ r →
      t.nr r = s.nr r) : MatchingDispatchState cost original i t := by
  let chosen := before.selected
  have port (r : ℕ) (safe : r = 9 ∨ r = 20 ∨ r = 21 ∨ r = 39 ∨
      (50 ≤ r ∧ r ≤ 90) ∨ 100 ≤ r := by decide) : t.nr r = s.nr r := regs r safe
  have tables (r : ℕ) (used : r ∈ matchingRefreshTableRegisters) : t.nr r = s.nr r :=
    port r (by simp [matchingRefreshTableRegisters] at used; omega)
  have traces := before.storage.traceLeft
  have right := before.storage.traceRight
  have marks := before.storage.traceMarks
  have witnessBase := before.storage.witnesses
  have headerOrder := before.storage.lengths
  have startOrder := before.storage.starts
  have nodes := before.storage.nodes
  have mates := before.storage.warm.matesBefore
  have rep := before.storage.warm.representativesAfter
  have candidates := before.storage.warm.candidatesAfter
  have buckets := before.storage.warm.pairsAfter
  have traceEnd : s.nr 90 = s.nr 83+3*k := by omega
  have nodeEnd : s.nr 74+k ≤ s.nr 83 := by omega
  have low (a : ℕ) (within : a < s.nr 83) : t.nm a = s.nm a := natural a (.inl within)
  have high (a : ℕ) (outside : s.nr 90 ≤ a) : t.nm a = s.nm a :=
    natural a (.inr (traceEnd ▸ outside))
  have read := chosen.reads.keeps (t := t)
    ⟨fun a h => low a (by omega), fun a _ _ _ => congrFun real a⟩ tables
  have primal : CompactMatchingPrimalDualMemory before.state original t := {
    dimension := read.layout.dimension
    oddMap := (port 56).trans chosen.primal.oddMap
    mateAbove := by rw [port 50]; exact chosen.primal.mateAbove
    mate v := by
      have index := v.isLt
      rw [port 50, low _ (by omega)]
      exact chosen.primal.mate v
    saved r h := (port r (by omega)).trans (chosen.primal.saved r h)
    natural a h := (low a (by have bound := chosen.primal.mateAbove; omega)).trans (chosen.primal.natural a h)
    real a h := (congrFun real a).trans (chosen.primal.real a h) }
  have topNode (v : Fin k) : blossomNodeAt t v = blossomNodeAt s v := by
    have index := v.isLt
    simpa only [blossomNodeAt, port 74] using low (s.nr 74+v.val) (by omega)
  let dual : MatchingSearchDualMemory before.part before.forest t := {
    dimension := read.layout.dimension
    separated := by rw [port 62, port 75]; exact chosen.dual.separated
    reps := read.representatives
    roles := by
      intro v
      rw [port 51]
      have index := v.isLt
      obtain ⟨label, parent, depth⟩ := chosen.dual.roles v
      exact ⟨(low _ (by omega)).trans label, (low _ (by omega)).trans parent,
        (low _ (by omega)).trans depth⟩
    effective := read.potentials
    node := chosen.dual.node
    nodeNonzero := chosen.dual.nodeNonzero
    nodeInjective := chosen.dual.nodeInjective
    cutValues B h := by rw [port 75, real]; exact chosen.dual.cutValues B h
    top v := (topNode v).trans (chosen.dual.top v) }
  let registry := chosen.registry.afterTrace (new := dual) before.storage before.order before.budget searching
    rfl (port 77) (port 78) (port 76) (port 65) topNode natural
  have words (v : Fin k) : matchingForestWitnessAt t.nm (t.nr 90) v.val =
      matchingForestWitnessAt s.nm (s.nr 90) v.val := by
    simp only [matchingForestWitnessAt, forestWitnessAddress, port 90,
      high (s.nr 90+(v.val+v.val)) (by omega), high (s.nr 90+(v.val+v.val)+1) (by omega)]
  have endpointWords : matchingOriginalGrowthEvent t = matchingOriginalGrowthEvent s := by
    have room := chosen.reads.layout.recordsBefore
    have rowCount := chosen.reads.layout.rows
    have dim := before.positive
    have fst := low (s.nr 54+((s.nr 1-1)+(s.nr 1-1))) (by omega)
    have snd := low (s.nr 54+((s.nr 1-1)+(s.nr 1-1))+1) (by omega)
    simp only [matchingOriginalGrowthEvent, id, port 54, fst, snd]
  have event : MatchingEventRecord (matchingTopCutAt before.part) (matchingOriginalGrowthEvent t) chosen.event :=
    endpointWords.symm ▸ chosen.chosen
  have delta : t.rr 1 = s.rr 1 := congrFun realRegs 1
  have clock : t.rr 15 = s.rr 15 := congrFun realRegs 15
  have shift := delta.symm ▸ chosen.adjustment
  have kind := matchingEventClass_of_adjustment before.state before.part.blocks before.forest
    (before.part.representativeOf before.positive) (matchingTopCutAt before.part)
    read.layout.dimension dual.roles
    (fun v => by rw [before.part.representativeOf_block]; exact dual.reps v) event shift
  have rows := matchingTraceKeepsRows (matchingTopCutAt before.part) chosen.reads.layout tables real
    (fun a h => low a (by omega)) chosen.valid
  have keys := matchingTraceKeepsBuckets nodes (port 65) (port 66) real (fun a h => low a (by omega))
  have pairIndex (a b : Fin k) : k*a.val+b.val < k*k := by
    have length := Nat.mul_le_mul_left k (Nat.succ_le_of_lt a.isLt)
    rw [Nat.mul_succ] at length
    have index := b.isLt
    omega
  let picked : MatchingChosenStage before.part before.forest before.positive
      (matchingTopCutAt before.part) original t := {
    event := chosen.event
    chosen := event
    kind := kind
    adjustment := shift
    primal := primal
    dual := dual
    registry := registry
    reads := read
    witnesses := by
      intro child parent link
      obtain ⟨a,b,ab,parentAt,childAt,tight⟩ := chosen.witnesses link
      exact ⟨a,b,(words child).trans ab,parentAt,childAt,tight⟩
    links := chosen.links.advance rfl words
    pairs := {
      valid i h := (keys i h).1.symm ▸ chosen.pairs.valid i h
      least a b different first last := by
        rw [clock, (keys _ (pairIndex a b)).2]
        exact chosen.pairs.least a b different first last
      inactive a b off := (keys _ (pairIndex a b)).2.trans (chosen.pairs.inactive a b off) }
    valid i hi := (rows i (port 61 ▸ hi)).1
    least g := by
      rw [delta, (rows g.slot (chosen.reads.layout.rows.symm ▸ g.slot_lt)).2]
      exact chosen.least g }
  let cycles : MatchingLiveCycles picked.registry := before.cycles.sameNodes picked.registry rfl rfl
    (fun B h => by
      apply (before.cycles.memory B h).onRegion (region := outsideMatchingTrace k s) _
        (fun r used => port r (by simp at used; omega)) natural
      apply MatchingMemberTree.traceFootprint _ before.storage before.order before.budget searching
      intro n member
      have within : n = chosen.dual.node B ∨ n ∈ (before.cycles.entry B h).tree.registryIds := by
        simpa only [MatchingMemberTree.registryIds, List.mem_cons, List.not_mem_nil, List.mem_append, or_false]
          using member
      have live : n ∈ chosen.registry.trees.registryIds := by
        rcases within with same | nested
        · exact (chosen.registry.keys n).mpr ⟨B,h,same.symm⟩
        · exact before.cycles.ids B h n nested
      obtain ⟨C,hC,rfl⟩ := (chosen.registry.keys n).mp live
      exact ⟨Nat.pos_of_ne_zero (chosen.dual.nodeNonzero C hC), chosen.registry.allocated C hC⟩)
  have header (r n : ℕ) (table : r = 77 ∨ r = 78) (allocated : n < s.nr 76) :
      t.nm (s.nr r+n) = s.nm (s.nr r+n) := by
    have fits := before.budget.allocated_fits searching allocated
    rcases table with rfl | rfl <;> exact low _ (by omega)
  have start (n : ℕ) (allocated : n < s.nr 76) :
      matchingCycleRecordStart t n = matchingCycleRecordStart s n := by
    simp only [matchingCycleRecordStart, port 77, header 77 n (.inl rfl) allocated]
  have order := before.order.transport (t := t)
    (by simp only [matchingRebaseScratchEnd, port 80, port 55]) (port 76) (port 68)
    (fun n _ h => start n h) (fun n _ h => by
      simp only [matchingCycleRecordEnd, start n h, port 78, header 78 n (.inr rfl) h])
  have storage := before.storage.keeps (t := t) (fun r used =>
    port r (by simp [matchingFixedStorageRegisters] at used; omega))
  have counts : matchingStageCountsFromRAM k t (t.nr 39) = matchingStageCountsFromRAM k s (s.nr 39) := by
    rw [matchingStageCountsFromRAM_eq dual before.positive _ registry.trees registry.unique registry.keys,
      matchingStageCountsFromRAM_eq chosen.dual before.positive _ chosen.registry.trees chosen.registry.unique chosen.registry.keys,
      port 39]
  have budget := before.budget.keeps (port 39) (port 76) counts
  exact ⟨before.state, before.part, before.forest, before.positive, before.count, before.top, before.internal,
    before.search, picked, cycles, storage, order, (port 39).symm ▸ before.fresh, budget, (port 9).trans before.one⟩



theorem MatchingDispatchState.afterTrace_counts {k i : ℕ} {cost : Fin k → Fin k → ℝ}
    {original s t : ArithmeticState} (before : MatchingDispatchState cost original i s)
    (searching : i < k/2) (winner : s.nr 1 ≤ s.nr 61)
    (natural : ∀ a, a < s.nr 83 ∨ s.nr 83+3*k ≤ a → t.nm a = s.nm a)
    (real : t.rm = s.rm) (realRegs : t.rr = s.rr) (id : t.nr 1 = s.nr 1)
    (regs : ∀ r, r = 9 ∨ r = 20 ∨ r = 21 ∨ r = 39 ∨ (50 ≤ r ∧ r ≤ 90) ∨ 100 ≤ r →
      t.nr r = s.nr r) :
    matchingStageCountsFromRAM k t (t.nr 39) = matchingStageCountsFromRAM k s (s.nr 39) := by
  let picked := before.afterTrace searching winner natural real realRegs id regs
  rw [matchingStageCountsFromRAM_eq picked.selected.dual picked.positive _ picked.selected.registry.trees
        picked.selected.registry.unique picked.selected.registry.keys,
      matchingStageCountsFromRAM_eq before.selected.dual before.positive _ before.selected.registry.trees
        before.selected.registry.unique before.selected.registry.keys,
      regs 39 (by decide)]
  rfl


end VehicleRoutingSurvey.Routing
end RppSource_MatchingDispatchTraceFrame

/-! matching/MatchingLiveCycleTransport.lean -/
section RppSource_MatchingLiveCycleTransport
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Retain a cycle's owners, current bases, and ordered original witnesses
as the outside cut family or the dual point changes. -/
noncomputable def MatchingLiveCycle.reindex {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state next : CompactMatchingPrimalDual k cost} {node nextNode : Finset (Fin k) → ℕ}
    {B : Finset (Fin k)} (e : MatchingLiveCycle state node B)
    (childLive : ∀ p ∈ e.ports.ports, (e.ports.block p).card ≠ 1 → e.ports.block p ∈ next.cuts.erase B)
    (childIds : ∀ p ∈ e.ports.ports, (e.ports.block p).card ≠ 1 → nextNode (e.ports.block p) = node (e.ports.block p))
    (descend : ∀ C ∈ next.cuts.erase B, C ⊆ B → ∃ p ∈ e.ports.ports, C ⊆ e.ports.block p)
    (unchanged : next.edges = state.edges)
    (tight : ∀ i, oddCutDualEdgeValue next.cuts next.potential next.cutDual
      s((e.geometry.edges i).1,(e.geometry.edges i).2) = edgeCost cost s((e.geometry.edges i).1,(e.geometry.edges i).2)) :
    MatchingLiveCycle next nextNode B := by
  let ports : MatchingExpansionChildPorts next B :=
    ⟨e.ports.ports,e.ports.block,e.ports.owner,e.ports.containsPort,e.ports.subset,e.ports.covered,e.ports.unique,childLive⟩
  let g := e.geometry
  let geometry : MatchingExpansionGeometry ports e.tree e.base := {
    members := ⟨g.members.assignment,g.members.absent⟩
    cycle := g.cycle
    edges := g.edges
    baseSlot := g.baseSlot
    children := g.children
    distinct := g.distinct
    odd := g.odd
    rotate := g.rotate
    atBase := g.atBase
    ports := g.ports
    source := g.source
    target := g.target
    tight := tight
    matched := by
      intro a b on
      obtain ⟨ab,ba⟩ := g.matched a b on
      exact ⟨next.partialMate_some_iff.mpr (unchanged.symm ▸ state.partialMate_some_iff.mp ab),
        next.partialMate_some_iff.mpr (unchanged.symm ▸ state.partialMate_some_iff.mp ba)⟩ }
  refine ⟨e.base,e.tree,ports,geometry,e.arity,e.keys,e.owner,?_,descend,?_,?_⟩
  · intro job listed p rep
    have inPorts := (e.owner job listed p rep).1
    by_cases single : (e.ports.block p).card = 1
    · simpa only [ports,if_pos single] using e.childNode job listed p rep
    · simpa only [ports,if_neg single,childIds p inPorts single] using e.childNode job listed p rep
  · simpa only [matchingCycleInterior,unchanged] using e.internal
  · intro i p q matched
    exact e.matchedRow i (state.partialMate_some_iff.mpr (unchanged ▸ next.partialMate_some_iff.mp matched))

theorem MatchingLiveCycle.internalEdge {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)} (e : MatchingLiveCycle state node B)
    (size : 2 ≤ e.geometry.cycle.length) (i : Fin e.geometry.cycle.length) :
    (e.geometry.edges i).1 ∈ B ∧ (e.geometry.edges i).2 ∈ B ∧ (e.geometry.edges i).1 ≠ (e.geometry.edges i).2 := by
  let g := e.geometry
  let j : Fin g.cycle.length := ⟨(i.val+1)%g.cycle.length,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
  have indexed (h : Fin g.cycle.length) : g.cycle.get h ∈ e.ports.ports := by
    rw [g.ports, List.mem_toFinset]
    exact List.getElem_mem h.isLt
  have source := g.source i
  have target : (g.edges i).2 ∈ e.ports.block (g.cycle.get j) := g.target i
  refine ⟨e.ports.subset _ (indexed i) source,e.ports.subset _ (indexed j) target,?_⟩
  intro equal
  have samePorts := (e.ports.unique _ (indexed i) _ source).symm.trans
    ((congrArg e.ports.owner equal).trans (e.ports.unique _ (indexed j) _ target))
  have sameIndex : i.val = j.val := (List.Nodup.getElem_inj_iff g.distinct).mp samePorts
  have within : i.val < g.cycle.length := i.isLt
  change i.val = (i.val+1)%g.cycle.length at sameIndex
  by_cases last : i.val + 1 = g.cycle.length
  · rw [last,Nat.mod_self] at sameIndex
    change 2 ≤ g.cycle.length at size
    omega
  · rw [Nat.mod_eq_of_lt (show i.val+1 < g.cycle.length by omega)] at sameIndex
    omega

/-- All recorded originals still lie inside the same top on a dual step.
Their slope is therefore zero, for every descendant, regardless of its base. -/
theorem MatchingLiveCycle.tightAfterDual {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    {part : CompactMatchingPartition state} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    (e : MatchingLiveCycle state node B) (size : 2 ≤ e.geometry.cycle.length)
    (same : ∀ u ∈ B, ∀ v ∈ B, part.blocks.block u = part.blocks.block v)
    {forest : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop}
    (search : CompactMatchingSearchForest part forest mate tight) (positive : 0 < k)
    (internal : state.InternalCuts) (bound : DualBound (MatchingDualEvent k))
    (adjustment : MatchingDualAdjustment cost (compactMatchingEdges k) state.cuts state.potential
      (forestVertexDirection part.blocks (part.dualLabel forest positive)) state.cutDual
      (forestCutDirection part.blocks (part.dualLabel forest positive)) bound) :
    let next := state.advanceSearch part search positive internal bound adjustment
    ∀ i, oddCutDualEdgeValue next.cuts next.potential next.cutDual s((e.geometry.edges i).1,(e.geometry.edges i).2) =
      edgeCost cost s((e.geometry.edges i).1,(e.geometry.edges i).2) := by
  intro next i
  obtain ⟨a,b,different⟩ := e.internalEdge size i
  change oddCutDualEdgeValue state.cuts (fun v => state.potential v + bound.amount * _)
    (fun C => state.cutDual C + bound.amount * _) _ = _
  rw [oddCutDualEdgeValue_shift, forest_edge_slope part.blocks _ (Finset.mem_univ _) (Finset.mem_univ _) different,
    if_pos (same _ a _ b), mul_zero, add_zero]
  exact e.geometry.tight i

end VehicleRoutingSurvey.Routing
end RppSource_MatchingLiveCycleTransport

/-! matching/MatchingLiveCyclesAdvance.lean -/
section RppSource_MatchingLiveCyclesAdvance
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- All stored cycle rows remain tight at the advanced dual point: both
original endpoints of each such edge lie inside a common old top block.
The update writes only real memory, so every archived natural row survives. -/
noncomputable def MatchingLiveCycles.advanceDual {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s t : ArithmeticState}
    {prior : MatchingSearchDualMemory part forest s} {oldReg : MatchingRegistryView prior}
    (live : MatchingLiveCycles oldReg) {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop}
    (search : CompactMatchingSearchForest part forest mate tight) (positive : 0 < k)
    (internal : state.InternalCuts) (bound : DualBound (MatchingDualEvent k))
    (step : MatchingDualAdjustment cost (compactMatchingEdges k) state.cuts state.potential
      (forestVertexDirection part.blocks (part.dualLabel forest positive)) state.cutDual
      (forestCutDirection part.blocks (part.dualLabel forest positive)) bound)
    {nextDual : MatchingSearchDualMemory (part.advanceSearch search positive internal bound step) forest t}
    (registry : MatchingRegistryView nextDual) (ids : nextDual.node = prior.node)
    (trees : registry.trees.tree = oldReg.trees.tree)
    (natural : t.nm = s.nm) (ports : ∀ r ∈ ([55,77,78,79,80] : List ℕ), t.nr r = s.nr r) :
    MatchingLiveCycles registry := by
  let next := state.advanceSearch part search positive internal bound step
  let entry (B : Finset (Fin k)) (h : B ∈ state.cuts) : MatchingLiveCycle next nextDual.node B :=
    let e := live.entry B h
    e.reindex e.ports.live (fun p _ _ => congrFun ids (e.ports.block p)) e.descendants rfl
      (e.tightAfterDual (e.arity ▸ (live.memory B h).members.proper.2.1)
        (oldReg.nested B h) search positive internal bound step)
  refine ⟨entry,?_,?_,?_,?_⟩
  · intro B h
    have stored := (live.memory B h).sameMemory natural ports
    have id := congrFun ids B
    refine ⟨?_,?_⟩
    · change MatchingMemberRoot (matchingRebaseNodeState t (nextDual.node B)) (live.entry B h).tree
      rw [id]
      exact stored.members
    · change MatchingNodeCycleRows t (nextDual.node B) (live.entry B h).geometry.cycle (live.entry B h).geometry.edges
      rw [id]
      exact stored.rows
  · intro p belongs fixed
    obtain ⟨base,tree⟩ := live.top p belongs fixed
    refine ⟨base,?_⟩
    change registry.trees.tree p = .blossom p.val (nextDual.node (part.blocks.block p)) (live.entry _ belongs).tree .nil
    rw [trees,ids,tree] <;> rfl
  · intro B h job within sub child
    obtain ⟨C,belongs,id,tree,base,block⟩ := live.child B h job within sub child
    exact ⟨C,belongs,(congrFun ids C).trans id,tree,base,block⟩
  · intro B h n listed
    change n ∈ (List.finRange k).flatMap fun v => (registry.trees.tree v).registryIds
    rw [trees]
    exact live.ids B h n listed

end VehicleRoutingSurvey.Routing
end RppSource_MatchingLiveCyclesAdvance

/-! matching/MatchingContractionCycleOrder.lean -/
section RppSource_MatchingContractionCycleOrder
namespace VehicleRoutingSurvey.Routing

def contractionLegPoint {α : Type*} (leg : List α) (base : α) (i : ℕ) (inside : i ≤ leg.length) : α :=
  (leg ++ [base])[i]'(by simp <;> omega)

theorem contractionLegPoint_last {α : Type*} (leg : List α) (base : α) :
    contractionLegPoint leg base leg.length le_rfl = base := by
  simp [contractionLegPoint,List.getElem_append_right (le_refl leg.length)]

theorem contractionLegPoint_before {α : Type*} (leg : List α) (base : α) {i : ℕ} (before : i < leg.length) :
    contractionLegPoint leg base i before.le = leg[i] := by
  simp only [contractionLegPoint,List.getElem_append_left before]

theorem contractionLeg_traced {k : ℕ} {forest : AlternatingForestState (Fin k)}
    {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop} (valid : forest.valid mate tight)
    {x base : Fin k} (label : forest.role x ≠ .unlabelled) (baseIn : base ∈ forest.traceToRoot x) :
    let leg := traceBefore base (forest.traceToRoot x)
    contractionLegPoint leg base 0 (Nat.zero_le _) = x ∧
      ∀ i (before : i < leg.length), (forest.role (contractionLegPoint leg base i before.le)).parent =
        some (contractionLegPoint leg base (i+1) before) := by
  intro leg
  obtain ⟨head,distinct,_,chain,_⟩ := AlternatingForestState.traceToRoot_spec valid label
  obtain ⟨pre,rest,eq⟩ := List.append_of_mem baseIn
  have noBase : base ∉ pre := fun h => (List.nodup_append.mp (eq ▸ distinct)).2.2 base h base (by simp) rfl
  have beforeEq : leg = pre := by simp only [leg,eq,traceBefore_eq noBase]
  have split : forest.traceToRoot x = (pre ++ [base]) ++ rest := by simpa only [List.append_assoc,List.singleton_append] using eq
  rw [beforeEq]
  constructor
  · have starts : (pre ++ [base]).head? = some x := by simpa only [eq,List.head?_append,List.head?_cons] using head
    have len : 0 < (pre ++ [base]).length := by simp
    rw [List.head?_eq_getElem?,List.getElem?_eq_getElem len] at starts
    exact Option.some.inj starts
  · intro i hi
    exact (List.isChain_iff_getElem.mp (split ▸ chain).left_of_append i (by simp <;> omega)).1



@[simp] theorem contractionCycleOrder_length {α : Type*} (left right : List α) (base : α) :
    (contractionCycleOrder left right base).length = left.length + right.length + 1 := by
  simp [contractionCycleOrder,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem contractionCycleOrder_left {α : Type*} (left right : List α) (base : α)
    {i : ℕ} (within : i ≤ left.length) :
    (contractionCycleOrder left right base)[i]'(by simp <;> omega) = contractionLegPoint left base i within := by
  rcases lt_or_eq_of_le within with h | rfl
  · rw [contractionLegPoint_before _ _ h]
    exact List.getElem_append_left h
  · rw [contractionLegPoint_last]
    simp [contractionCycleOrder,List.getElem_append_right (le_refl left.length)]

theorem contractionCycleOrder_right {α : Type*} (left right : List α) (base : α)
    {i : ℕ} (start : left.length ≤ i) (within : i ≤ left.length + right.length) :
    (contractionCycleOrder left right base)[i]'(by simp <;> omega) =
      contractionLegPoint right base (left.length + right.length - i) (by omega) := by
  have view : contractionCycleOrder left right base = left ++ (right ++ [base]).reverse := by
    simp [contractionCycleOrder]
  simp only [view,List.getElem_append_right start,List.getElem_reverse,contractionLegPoint]
  apply getElem_congr_idx
  simp only [List.length_append,List.length_singleton]
  omega

/-- Exact location and rotation of the newly allocated base. -/
theorem contractionCycleOrder_base {α : Type*} (left right : List α) (base : α) :
    (contractionCycleOrder left right base).rotate left.length = base :: (right.reverse ++ left) ∧
      (contractionCycleOrder left right base)[left.length]'(by simp <;> omega) = base := by
  constructor
  · simpa only [contractionCycleOrder,List.cons_append] using List.rotate_append_length_eq left (base :: right.reverse)
  · exact (contractionCycleOrder_left left right base le_rfl).trans (contractionLegPoint_last _ _)

theorem contractionCycleOrder_perm {α : Type*} (left right : List α) (base : α) :
    (contractionCycleOrder left right base).Perm (base :: (left ++ right)) := by
  have rotated := (List.rotate_perm (contractionCycleOrder left right base) left.length).symm
  rw [(contractionCycleOrder_base left right base).1] at rotated
  exact rotated.trans (.cons base (((List.reverse_perm right).append_right left).trans List.perm_append_comm))

/-- The trace begins at each triggering endpoint, even if that endpoint is
itself the common base and its exclusive leg is empty. -/
theorem contractionCycleOrder_endpoints {k : ℕ} {forest : AlternatingForestState (Fin k)}
    {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop} (valid : forest.valid mate tight)
    {a b base : Fin k} (aLabel : forest.role a ≠ .unlabelled) (bLabel : forest.role b ≠ .unlabelled)
    (ancestor : forest.commonAncestor a b = some base) :
    let left := traceBefore base (forest.traceToRoot a)
    let right := traceBefore base (forest.traceToRoot b)
    a ∈ contractionCycleOrder left right base ∧ b ∈ contractionCycleOrder left right base := by
  intro left right
  obtain ⟨baseAtA, before, _, split, _⟩ := firstSharedAncestor_eq_some_iff.mp ancestor
  have baseAtB : base ∈ forest.traceToRoot b := split.symm ▸ List.mem_append_right before (by simp)
  have endpoint (x : Fin k) (live : forest.role x ≠ .unlabelled) (shared : base ∈ forest.traceToRoot x) :
      x = base ∨ x ∈ traceBefore base (forest.traceToRoot x) := by
    let leg := traceBefore base (forest.traceToRoot x)
    have starts := (contractionLeg_traced valid live shared).1
    have occurrence : contractionLegPoint leg base 0 (Nat.zero_le _) ∈ leg ++ [base] :=
      List.getElem_mem (by simp)
    have member : x ∈ leg ++ [base] := starts ▸ occurrence
    simpa only [leg, List.mem_append, List.mem_singleton, or_comm] using member
  have order (x : Fin k) : x ∈ contractionCycleOrder left right base ↔ x ∈ base :: (left ++ right) :=
    (contractionCycleOrder_perm left right base).mem_iff
  exact ⟨(order a).mpr (List.mem_cons.mpr ((endpoint a aLabel baseAtA).imp id (List.mem_append_left right))),
    (order b).mpr (List.mem_cons.mpr ((endpoint b bLabel baseAtB).imp id (List.mem_append_right left)))⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionCycleOrder

/-! matching/MatchingContractionTrace.lean -/
section RppSource_MatchingContractionTrace
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

private theorem compactMatchingTightSymmetric {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) :
    Std.Symm part.tightBetween :=
  ⟨fun _ _ ⟨u,v,first,second,tight⟩ => ⟨v,u,second,first,Sym2.eq_swap ▸ tight⟩⟩

private theorem forestTrace_prefixWords {n : ℕ} {memory : ℕ → ℕ} {base : ℕ} {trail : List (Fin n)}
    (encoded : ForestTraceArray memory base trail) {length : ℕ} (bound : length ≤ trail.length) :
    (List.range length).map (fun i => memory (base + i)) = (trail.take length).map Fin.val := by
  have count : (trail.take length).length = length := by rw [List.length_take, Nat.min_eq_left bound]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, count]
  · intro i hi hj
    have indexed : i < length := by simpa using hi
    have within : i < trail.length := indexed.trans_le bound
    simp only [List.getElem_map, List.getElem_range, List.getElem_take]
    exact encoded i within

/-- A resolved contraction supplies the typed legs from the actual trace arrays,
their compact-index validity, and the exact cycle-size bound needed by the handler. -/
theorem MatchingResolvedOuter.contractionTrace {n : ℕ} {forest : AlternatingForestState (Fin n)}
    {u v base : Fin n} {uParent vParent : Option (Fin n)} {scratch : ℕ} {s t : ArithmeticState}
    (traces : MatchingResolvedOuter forest u v scratch s t)
    {mate : Fin n → Option (Fin n)} {tight : Sym2 (Fin n) → Prop}
    (valid : forest.valid mate (fun a b => tight s(a, b)))
    (different : u ≠ v) (uOuter : forest.role u = .outer uParent) (vOuter : forest.role v = .outer vParent)
    (closing : tight s(v, u)) (ancestor : forest.commonAncestor u v = some base) :
    t.nr 12 = base.val ∧ t.nr 13 + t.nr 14 + 1 ≤ n ∧
      (∀ i < t.nr 13, t.nm (t.nr 83 + i) < n) ∧ (∀ i < t.nr 14, t.nm (t.nr 84 + i) < n) ∧
      (List.range (t.nr 13)).map (fun i => t.nm (t.nr 83 + i)) =
        (traceBefore base (forest.traceToRoot u)).map Fin.val ∧
      (List.range (t.nr 14)).map (fun i => t.nm (t.nr 84 + i)) =
        (traceBefore base (forest.traceToRoot v)).map Fin.val := by
  have witness : t.nr 12 = base.val := by rw [traces.shared, ancestor] <;> rfl
  have split := traces.split
  rw [ancestor] at split
  obtain ⟨leftIn, rightIn, _, _⟩ := split.positions
  obtain ⟨_, leftNodup, _, _, _⟩ := AlternatingForestState.traceToRoot_spec valid (x := u) (by simp [uOuter])
  obtain ⟨_, rightNodup, _, _, _⟩ := AlternatingForestState.traceToRoot_spec valid (x := v) (by simp [vOuter])
  obtain ⟨leftLeg, rightLeg⟩ := split.traceBefore leftNodup rightNodup
  obtain ⟨nd, _, _, _⟩ := alternatingForest_contractionCycle valid different uOuter vOuter closing ancestor
  have upper : (contractionCycle (forest.traceToRoot u) (forest.traceToRoot v) base).length ≤ n := by
    simpa using nd.length_le_card
  simp only [contractionCycle, leftLeg, rightLeg, List.length_append, List.length_reverse, List.length_singleton, List.length_cons,
    List.length_take, Nat.min_eq_left leftIn.le, Nat.min_eq_left rightIn.le] at upper
  have leftBase := traces.registers 83 (by decide)
  have rightBase := traces.registers 84 (by decide)
  refine ⟨witness, by omega, ?_, ?_, ?_, ?_⟩
  · intro i inside
    have full := inside.trans leftIn
    rw [leftBase, traces.left i full]
    exact (forest.traceToRoot u)[i].isLt
  · intro i inside
    have full := inside.trans rightIn
    rw [rightBase, traces.right i full]
    exact (forest.traceToRoot v)[i].isLt
  · rw [leftBase, leftLeg]
    exact forestTrace_prefixWords traces.left leftIn.le
  · rw [rightBase, rightLeg]
    exact forestTrace_prefixWords traces.right rightIn.le

/-- The executable trace's two legs identify a simple odd cycle of current
representatives. The closing edge is tight on the quotient after its dual step. -/
theorem CompactMatchingSearchForest.contractionCycleFacts {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    (search : CompactMatchingSearchForest part forest state.partialMate part.tightBetween)
    (links : MatchingForestLinkMemory part forest s)
    {a b base : Fin k} {pa pb : Option (Fin k)}
    (different : a ≠ b) (aOuter : forest.role a = .outer pa) (bOuter : forest.role b = .outer pb)
    (closing : part.tightBetween a b) (ancestor : forest.commonAncestor a b = some base) :
    let left := traceBefore base (forest.traceToRoot a)
    let right := traceBefore base (forest.traceToRoot b)
    let cycle := contractionCycleOrder left right base
    cycle.Nodup ∧ 3 ≤ cycle.length ∧ Odd cycle.length ∧
      (∀ p ∈ cycle.toFinset, part.representative p = p) ∧
      (∃ p, forest.role base = .outer p) ∧
      (∀ p ∈ left ++ right, forest.role p ≠ .unlabelled) ∧
      (∃ u ∈ cycle.toFinset, ∃ v ∈ cycle.toFinset, u ≠ v ∧
        alternatingRoleCode (forest.role u) = 1 ∧ alternatingRoleCode (forest.role v) = 1) := by
  intro left right cycle
  letI sym := compactMatchingTightSymmetric part
  obtain ⟨distinct, size, parity, _⟩ := alternatingForest_contractionCycle
    (tight := fun e => e ∈ Sym2.fromRel sym) search.valid different aOuter bOuter
    (Std.Symm.symm (r := part.tightBetween) a b closing) ancestor
  obtain ⟨baseOuter, labelled⟩ := alternatingForest_contractionLabels search.valid aOuter bOuter ancestor
  obtain ⟨aAt,bAt⟩ := contractionCycleOrder_endpoints search.valid (by simp [aOuter]) (by simp [bOuter]) ancestor
  refine ⟨distinct, size, parity, ?_, baseOuter, labelled, a, List.mem_toFinset.mpr aAt,
    b, List.mem_toFinset.mpr bAt, different, by simp [aOuter, alternatingRoleCode], by simp [bOuter, alternatingRoleCode]⟩
  intro p member
  have onLeg := List.mem_cons.mp ((contractionCycleOrder_perm left right base).mem_iff.mp (List.mem_toFinset.mp member))
  have label : forest.role p ≠ .unlabelled := by
    rcases onLeg with rfl | onLeg
    · obtain ⟨prior, outer⟩ := baseOuter
      simp [outer]
    · exact labelled p onLeg
  exact Classical.byContradiction fun different => label (links.inactive p different)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionTrace

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

/-! matching/MatchingContractionPrefixReads.lean -/
section RppSource_MatchingContractionPrefixReads
namespace VehicleRoutingSurvey.Routing

/-- The two cache slabs lie between the low forest/dual tables and the high
blossom/trace tables in the physical workspace. -/
structure MatchingContractionCacheLocation (k : ℕ) (s : ArithmeticState) : Prop where
  representativesBefore : s.nr 57+k ≤ s.nr 58
  parentsBefore : s.nr 52+k ≤ s.nr 58
  nodesAfter : s.nr 65+2*(k*k) ≤ s.nr 74
  startsAfter : s.nr 65+2*(k*k) ≤ s.nr 77
  countsAfter : s.nr 65+2*(k*k) ≤ s.nr 78
  scratchAfter : s.nr 65+2*(k*k) ≤ s.nr 86
  effectiveBefore : s.nr 62+k ≤ s.nr 59
  dualAfter : s.nr 66+k*k ≤ s.nr 75

theorem MatchingContractionPrefixView.cacheReads {k : ℕ} {s t : ArithmeticState}
    (view : MatchingContractionPrefixView s t) (layout : MatchingCacheLayout k s)
    (location : MatchingContractionCacheLocation k s)
    (ports : ∀ r ∈ ([54,58,59,60,65,66] : List ℕ), t.nr r = s.nr r)
    (cutAt : Fin k → Finset (Fin k)) (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i) :
    (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i = readMatchingCandidate cutAt s i) ∧
    (∀ i < k*k, MatchingPairBucketValid k t i = MatchingPairBucketValid k s i ∧
      readMatchingPairBucket (k := k) t i = readMatchingPairBucket (k := k) s i) := by
  obtain ⟨reps,parents,nodes,starts,counts,scratch,effective,duals⟩ := location
  have size := layout.dimension
  have ids := layout.idsBefore
  have records := layout.recordsBefore
  have slacks := layout.slacksBefore
  have rates := layout.ratesBefore
  have natural (a : ℕ) (lo : s.nr 58 ≤ a) (hi : a < s.nr 65+2*(k*k)) : t.nm a = s.nm a := by
    apply view.cacheNatural <;> omega
  have real (a : ℕ) (lo : s.nr 59 ≤ a) (hi : a < s.nr 66+k*k) : t.rm a = s.rm a := by
    apply view.cacheReal <;> omega
  have reg (r : ℕ) (mem : r ∈ ([54,58,59,60,65,66] : List ℕ) := by decide) := ports r mem
  constructor
  · intro i hi
    have idEq : t.nm (t.nr 58+i) = s.nm (s.nr 58+i) := by rw [reg 58, natural _ (by omega) (by omega)]
    have kind := rows i hi
    rcases kind with off | ⟨own,e,decoded⟩
    · simp [MatchingCandidateRowValid, readMatchingCandidate, idEq, off, decodeMatchingDictionaryEvent]
    · have record (j : ℕ) (limit : j ≤ 1) :
          t.nm (s.nr 54+(i+i)+j) = s.nm (s.nr 54+(i+i)+j) := natural _ (by omega) (by omega)
      have first : t.nm (s.nr 54+(i+i)) = s.nm (s.nr 54+(i+i)) := by simpa using record 0 (by decide)
      have lookup : decodeMatchingDictionaryEvent k cutAt t (i+1) = decodeMatchingDictionaryEvent k cutAt s (i+1) := by
        simp only [decodeMatchingDictionaryEvent, reg 54, Nat.add_sub_cancel, first, record 1 (by decide)]
      refine ⟨Or.inr ⟨idEq.trans own, e, ?_⟩, ?_⟩
      · simpa only [idEq,own,lookup] using (show decodeMatchingDictionaryEvent k cutAt s (s.nm (s.nr 58+i)) = some e from decoded)
      · simp only [readMatchingCandidate, idEq, own, lookup, reg 59, reg 60,
          real _ (show s.nr 59 ≤ s.nr 59+i by omega) (show s.nr 59+i < s.nr 66+k*k by omega),
          real _ (show s.nr 59 ≤ s.nr 60+i by omega) (show s.nr 60+i < s.nr 66+k*k by omega)]
  · intro i hi
    have first := natural (s.nr 65+(i+i)) (by omega) (by omega)
    have second := natural (s.nr 65+(i+i)+1) (by omega) (by omega)
    have score := real (s.nr 66+i) (by omega) (by omega)
    constructor <;> simp only [MatchingPairBucketValid, readMatchingPairBucket, reg 65, reg 66, first, second, score]

/-- The contraction cache repair sees the new representative, role and
effective-potential rows, with the original distance matrix and row offsets. -/
theorem MatchingRefreshInput.contractionPrefix {k : ℕ} {s t : ArithmeticState} {cost : Fin k → Fin k → ℝ}
    {oldRep : Fin k → Fin k} {oldRole : Fin k → ℕ} {oldEffective : Fin k → ℝ}
    (input : MatchingRefreshInput s oldRep oldRole cost oldEffective)
    {rep : Fin k → Fin k} {role : Fin k → ℕ} {effective : Fin k → ℝ}
    (ports : ∀ r ∈ matchingRefreshTableRegisters, t.nr r = s.nr r)
    (offsetEnd : s.nr 21 + k ≤ s.nr 51) (metricEnd : s.nr 20 + k*k ≤ s.nr 62)
    (natural : ∀ a < s.nr 51, t.nm a = s.nm a) (real : ∀ a < s.nr 62, t.rm a = s.rm a)
    (reps : ∀ v : Fin k, t.nm (t.nr 57+v.val) = (rep v).val)
    (roles : ∀ v : Fin k, t.nm (t.nr 51+v.val) = role v)
    (potentials : ∀ v : Fin k, t.rm (t.nr 62+v.val) = effective v) :
    MatchingRefreshInput t rep role cost effective := by
  have port (r : ℕ) (listed : r ∈ matchingRefreshTableRegisters := by decide) := ports r listed
  have layout : MatchingCacheLayout k t :=
    ⟨(port 55).trans input.layout.dimension, (port 61).trans input.layout.rows,
      by simpa only [port 58, port 61, port 54] using input.layout.idsBefore,
      by simpa only [port 54, port 61, port 65] using input.layout.recordsBefore,
      by simpa only [port 59, port 61, port 60] using input.layout.slacksBefore,
      by simpa only [port 60, port 61, port 66] using input.layout.ratesBefore⟩
  refine ⟨layout, by simpa only [port 21, port 58] using input.offsetsBefore,
    by simpa only [port 57, port 58] using input.representativesBefore,
    by simpa only [port 51, port 58] using input.rolesBefore,
    by simpa only [port 20, port 59] using input.metricBefore,
    by simpa only [port 62, port 59] using input.effectiveBefore,
    ?_, reps, roles, ?_, potentials⟩
  · intro v
    have below := (Nat.add_lt_add_left v.isLt (s.nr 21)).trans_le offsetEnd
    rw [port 21, natural _ below]
    exact input.offsets v
  · intro i j
    have row := Nat.mul_le_mul_left k (Nat.succ_le_of_lt i.isLt)
    rw [Nat.mul_succ] at row
    have next := j.isLt
    rw [port 20, real _ (by omega)]
    exact input.metric i j

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionPrefixReads

/-! matching/MatchingContractionWrittenRows.lean -/
section RppSource_MatchingContractionWrittenRows
namespace VehicleRoutingSurvey.Routing



/-- The three physical sequences form a single indexed cycle whose rows and
both headers can be recovered after the entire writer returns. -/
theorem matchingContractionWrittenRows {s t : ArithmeticState} {ticks : ℕ}
    (run : BlockRuns writeMatchingContractionCycle ticks s t) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (headers : s.nr 77 + s.nr 76 < s.nr 78)
    (allocated : s.nr 78 + s.nr 76 < s.nr 68) (safe : MatchingCycleReadSafety (matchingCycleRecordReference s)) :
    matchingCycleRecordStart t (s.nr 76) = s.nr 68 ∧
    t.nm (t.nr 78 + s.nr 76) = matchingCycleChildCount s ∧
    ∀ i < matchingCycleChildCount s,
      matchingCycleChildAt t.nm (matchingCycleRecordStart t (s.nr 76)+4*i) = matchingContractionWrittenChild s i := by
  obtain ⟨out,_,_,observed,_,_,bytes,_,fixed,outputs⟩ := writeMatchingContractionCycle_spec s entry running one
  have eq := (observed.same_exit run).2
  subst out
  have start : matchingCycleRecordStart t (s.nr 76) = s.nr 68 := by
    rw [matchingCycleRecordStart, fixed 77 (by decide), bytes _ (by omega)]
    simp [startMatchingCycleNat, Function.update_of_ne (show s.nr 77+s.nr 76 ≠ s.nr 78+s.nr 76 by omega)]
  have count : t.nm (t.nr 78 + s.nr 76) = matchingCycleChildCount s := by
    rw [fixed 78 (by decide), bytes _ allocated]
    simp [startMatchingCycleNat]
  obtain ⟨left,center,right⟩ := outputs safe
  refine ⟨start,count,?_⟩
  intro i hi
  rw [start]
  by_cases onLeft : i < s.nr 13
  · simpa only [matchingContractionWrittenChild,if_pos onLeft] using left i onLeft
  by_cases middle : i = s.nr 13
  · subst i
    simpa only [matchingContractionWrittenChild,if_neg (Nat.lt_irrefl _),if_pos rfl,if_true] using center
  · let j := i - (s.nr 13+1)
    have size : i < s.nr 13+s.nr 14+1 := hi
    have bj : j < s.nr 14 := by dsimp [j]; omega
    have index : s.nr 13+1+j = i := by dsimp [j]; omega
    simpa only [matchingContractionWrittenChild,if_neg onLeft,if_neg middle,index,j] using right j bj

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionWrittenRows

/-! matching/MatchingContractionStorage.lean -/
section RppSource_MatchingContractionStorage
namespace VehicleRoutingSurvey.Routing

set_option maxHeartbeats 1600000 in
theorem MatchingStageStorage.contractionLayout {k : ℕ} {original s : ArithmeticState}
    (storage : MatchingStageStorage k original s) (order : MatchingCycleRecordOrder s)
    (space : s.nr 76 < matchingBlossomCapacity k) (effective : s.nr 62+k ≤ s.nr 59)
    (size : s.nr 13+s.nr 14+1 ≤ k) (base : s.nr 12 < k)
    (left : ∀ i < s.nr 13, s.nm (s.nr 83+i) < k) (right : ∀ i < s.nr 14, s.nm (s.nr 84+i) < k)
    (reps : ∀ i < k, originalTopRepresentative s i < k) : MatchingContractionLayout s := by
  obtain ⟨warm,_,nodes,duals,starts,lengths,trace,rightBase,traceMark,witness,rows,promotion,mask,member,stack,_⟩ := storage
  obtain ⟨dim,_,parents,depths,mate,representatives,candidates,dict,pairs,rates,keys,offsets⟩ := warm
  have arena := order.scratch
  change s.nr 80+5*s.nr 55 ≤ s.nr 68 at arena
  constructor <;> first | omega | (intro j hj; simpa only [dim] using left j hj) |
    (intro j hj; simpa only [dim] using right j hj) | (intro j hj; simpa only [dim] using reps j (dim ▸ hj)) |
    (constructor <;> first | omega | (constructor <;> omega))

theorem MatchingStageStorage.contractionCacheLocation {k : ℕ} {original s : ArithmeticState}
    (storage : MatchingStageStorage k original s) (effective : s.nr 62+k ≤ s.nr 59) :
    MatchingContractionCacheLocation k s := by
  obtain ⟨warm,_,nodes,duals,starts,lengths,trace,right,marks,witness,rows,_,_,_,_,_⟩ := storage
  obtain ⟨_,_,parents,_,_,rep,candidate,_,_,_,_,_⟩ := warm
  constructor <;> omega

/-- Starting the new record only writes the two reserved header cells. All
input trace words, child pointers and original-edge witnesses survive that write. -/
theorem MatchingStageStorage.contractionReference {k : ℕ} {original s : ArithmeticState}
    (storage : MatchingStageStorage k original s) (order : MatchingCycleRecordOrder s)
    (space : s.nr 76 < matchingBlossomCapacity k) (size : s.nr 13+s.nr 14+1 ≤ k) (base : s.nr 12 < k)
    (left : ∀ i < s.nr 13, s.nm (s.nr 83+i) < k) (right : ∀ i < s.nr 14, s.nm (s.nr 84+i) < k) :
    let r := matchingCycleRecordReference s
    MatchingCycleReadSafety r ∧
      (∀ i < s.nr 13, leftCycleRepresentativeAt r i = s.nm (s.nr 83+i)) ∧
      (∀ i < s.nr 14, rightCycleRepresentativeAt r i = s.nm (s.nr 84+i)) ∧
      (∀ v : Fin k, matchingForestWitnessAt r.nm (r.nr 90) v.val = matchingForestWitnessAt s.nm (s.nr 90) v.val) ∧
      (∀ v : Fin k, r.nm (s.nr 74+v.val) = s.nm (s.nr 74+v.val)) := by
  intro r
  obtain ⟨warm,_,nodes,duals,starts,lengths,first,second,mark,witness,rows,promotion,mask,member,stack,_⟩ := storage
  have dim := warm.size
  have arena := order.scratch
  change s.nr 80+5*s.nr 55 ≤ s.nr 68 at arena
  have safe (addr : ℕ) (h : addr < s.nr 77 ∨ s.nr 78+s.nr 76 < addr) : r.nm addr = s.nm addr := by
    simp only [r,matchingCycleRecordReference,startMatchingCycleNat,
      Function.update_of_ne (by omega : addr ≠ s.nr 77+s.nr 76),Function.update_of_ne (by omega : addr ≠ s.nr 78+s.nr 76)]
  have l (i : ℕ) (_ : i < s.nr 13) : leftCycleRepresentativeAt r i = s.nm (s.nr 83+i) := by
    change r.nm (s.nr 83+i) = _
    exact safe _ (.inr (by omega))
  have q (i : ℕ) (_ : i < s.nr 14) : rightCycleRepresentativeAt r i = s.nm (s.nr 84+i) := by
    change r.nm (s.nr 84+i) = _
    exact safe _ (.inr (by omega))
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_⟩,l,q,?_,?_⟩
  · change s.nr 83+s.nr 13 ≤ s.nr 68; omega
  · change s.nr 84+s.nr 14 ≤ s.nr 68; omega
  · change s.nr 74+s.nr 55 ≤ s.nr 68; omega
  · change s.nr 90+2*s.nr 55 ≤ s.nr 68; omega
  · intro i hi; rw [l i hi]; exact dim.symm ▸ left i hi
  · intro i hi; rw [q i hi]; exact dim.symm ▸ right i hi
  · exact dim.symm ▸ base
  · intro v
    have h1 := safe (forestWitnessAddress (s.nr 90) v.val) (.inr (by unfold forestWitnessAddress; omega))
    have h2 := safe (forestWitnessAddress (s.nr 90) v.val+1) (.inr (by unfold forestWitnessAddress; omega))
    change (r.nm (forestWitnessAddress (s.nr 90) v.val),r.nm (forestWitnessAddress (s.nr 90) v.val+1)) = _
    rw [h1,h2]
    rfl
  · intro v
    exact safe _ (.inl (by have bound := v.isLt; omega))

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionStorage

/-! matching/MatchingContractionCycleEdges.lean -/
section RppSource_MatchingContractionCycleEdges
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



theorem ContractionCycleEdgeWords.reverse {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    {part : CompactMatchingPartition state} {src dst : Fin k} {words : ℕ × ℕ}
    (edge : ContractionCycleEdgeWords part src dst words) : ContractionCycleEdgeWords part dst src words.swap := by
  obtain ⟨a,b,atWords,source,target,value,matched⟩ := edge
  refine ⟨b,a,by simp [atWords],target,source,Sym2.eq_swap ▸ value,?_⟩
  intro flip
  have pair := matched (state.partialMate_some_iff.mpr (Sym2.eq_swap ▸ state.partialMate_some_iff.mp flip))
  exact ⟨pair.2,pair.1⟩

theorem MatchingForestOriginalWitnesses.contractionWords {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    (witnesses : MatchingForestOriginalWitnesses part forest s) (links : MatchingForestLinkMemory part forest s)
    {tight : Fin k → Fin k → Prop} (valid : forest.valid state.partialMate tight)
    {child parent : Fin k} (link : (forest.role child).parent = some parent) :
    ContractionCycleEdgeWords part parent child (matchingForestWitnessAt s.nm (s.nr 90) child.val) := by
  obtain ⟨a,b,atWords,source,target,value⟩ := witnesses link
  refine ⟨a,b,atWords,source,target,value,?_⟩
  intro matched
  rcases parent_step_roles valid link with ⟨_,outer,_,_⟩ | ⟨_,inner,_⟩
  · have eq := atWords.symm.trans (links.matched outer)
    exact ⟨Fin.ext (congrArg Prod.fst eq),Fin.ext (congrArg Prod.snd eq)⟩
  · have row := valid child
    rw [inner] at row
    exact (row.2.1 (state.partialMate_some_iff.mpr (Sym2.eq_swap ▸ state.partialMate_some_iff.mp matched))).elim

/-- The triggering edge joins distinct outer vertices, which cannot be mates
of each other in a valid alternating forest. -/
theorem contractionClosingEdgeWords {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    {part : CompactMatchingPartition state} {forest : AlternatingForestState (Fin k)}
    {tight : Fin k → Fin k → Prop} (valid : forest.valid state.partialMate tight)
    {a b src dst : Fin k} {pa pb : Option (Fin k)} (source : part.representative a = src)
    (target : part.representative b = dst) (outer : forest.role src = .outer pa) (other : forest.role dst = .outer pb)
    (value : oddCutDualEdgeValue state.cuts state.potential state.cutDual s(a,b) = edgeCost cost s(a,b)) :
    ContractionCycleEdgeWords part src dst (a.val,b.val) := by
  refine ⟨a,b,rfl,source,target,value,?_⟩
  intro matched
  have role := valid src
  rw [outer] at role
  cases pa with
  | none =>
    rw [show state.partialMate src = none from role] at matched
    cases matched
  | some parent =>
    obtain ⟨⟨q,inner⟩,mateSrc,_,_,_⟩ := role
    have eq := Option.some.inj (mateSrc.symm.trans matched)
    have impossible := (eq ▸ inner).symm.trans other
    cases impossible

private def contractionRowWords (r : MatchingCycleChild) : ℕ × ℕ := (r.endpointA,r.endpointB)

/-- All three parts of the append program produce the requested forward
cycle. The left leg traverses child-to-parent, the right leg traverses
parent-to-child, and the last row uses the selected original edge. -/
theorem matchingContractionWrittenChild_geometry {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state} {s : ArithmeticState}
    {forest : AlternatingForestState (Fin k)} {tight : Fin k → Fin k → Prop} (valid : forest.valid state.partialMate tight)
    (left right : List (Fin k)) (base : Fin k)
    (leftLength : s.nr 13 = left.length) (rightLength : s.nr 14 = right.length) (atBase : s.nr 12 = base.val)
    (leftWords : ∀ i (hi : i < left.length), leftCycleRepresentativeAt (matchingCycleRecordReference s) i = left[i].val)
    (rightWords : ∀ i (hi : i < right.length), rightCycleRepresentativeAt (matchingCycleRecordReference s) i = right[i].val)
    (leftLink : ∀ i (hi : i < left.length), (forest.role (contractionLegPoint left base i hi.le)).parent =
      some (contractionLegPoint left base (i+1) hi))
    (rightLink : ∀ i (hi : i < right.length), (forest.role (contractionLegPoint right base i hi.le)).parent =
      some (contractionLegPoint right base (i+1) hi))
    (witnesses : MatchingForestOriginalWitnesses part forest (matchingCycleRecordReference s))
    (links : MatchingForestLinkMemory part forest (matchingCycleRecordReference s))
    (closing : ContractionCycleEdgeWords part (contractionLegPoint right base 0 (Nat.zero_le _))
      (contractionLegPoint left base 0 (Nat.zero_le _)) (s.nr 93,s.nr 92)) :
    let cycle := contractionCycleOrder left right base
    matchingCycleChildCount s = cycle.length ∧
      ∀ i : Fin cycle.length, let row := matchingContractionWrittenChild s i.val
        let src := cycle.get i
        let dst := cycle.get ⟨(i.val+1) % cycle.length,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
        row.representative = src.val ∧ row.node = (matchingCycleRecordReference s).nm (s.nr 74+src.val) ∧
          ContractionCycleEdgeWords part src dst (row.endpointA,row.endpointB) := by
  intro cycle
  let r := matchingCycleRecordReference s
  have len : cycle.length = left.length+right.length+1 := contractionCycleOrder_length _ _ _
  refine ⟨by simp only [matchingCycleChildCount,leftLength,rightLength,len],?_⟩
  intro i row src dst
  have within : i.val ≤ left.length+right.length := by have h := i.isLt; omega
  by_cases before : i.val < left.length
  · have curr : src = contractionLegPoint left base i.val before.le := contractionCycleOrder_left _ _ _ before.le
    have noWrap : i.val+1 < cycle.length := by omega
    have following : dst = contractionLegPoint left base (i.val+1) before := by
      dsimp only [dst,List.get_eq_getElem]
      simp only [Nat.mod_eq_of_lt noWrap]
      exact contractionCycleOrder_left _ _ _ before
    have code : row = leftCycleRecordAt r i.val := by
      simp only [row,matchingContractionWrittenChild,leftLength,if_pos before,r]
    have repr : leftCycleRepresentativeAt r i.val = src.val := by
      rw [curr,contractionLegPoint_before _ _ before]
      exact leftWords _ before
    have edge := (witnesses.contractionWords links valid (leftLink _ before)).reverse
    rw [← curr,← following] at edge
    simp only [code,leftCycleRecordAt,repr]
    exact ⟨True.intro,rfl,edge⟩
  · let j := left.length+right.length-i.val
    have onRight : left.length ≤ i.val := by omega
    have bounded : j ≤ right.length := by dsimp [j]; omega
    have curr : src = contractionLegPoint right base j bounded := contractionCycleOrder_right _ _ _ onRight within
    let nextWords := if j = 0 then (s.nr 93,s.nr 92)
      else matchingForestWitnessAt r.nm (r.nr 90) (rightCycleRepresentativeAt r (j-1))
    have data : row.representative = src.val ∧ row.node = r.nm (s.nr 74+src.val) ∧
        contractionRowWords row = nextWords := by
      by_cases center : i.val = left.length
      · have atEnd : j = right.length := by dsimp [j]; omega
        have repr : src = base := by simpa only [atEnd,contractionLegPoint_last] using curr
        have code : row = commonCycleRecord r := by
          simp only [row,matchingContractionWrittenChild,leftLength,if_neg before,if_pos center,r]
        simp [code,commonCycleRecord,contractionRowWords,repr,nextWords,atEnd,r,matchingCycleRecordReference,atBase,rightLength]
      · have shorter : j < right.length := by dsimp [j]; omega
        have index : s.nr 14 - ((i.val - (s.nr 13+1)) + 1) = j := by dsimp [j]; omega
        have code : row = rightCycleRecordAt r (i.val-(s.nr 13+1)) := by
          simp only [row,matchingContractionWrittenChild,leftLength,if_neg before,if_neg center,r]
        have repr : rightCycleRepresentativeAt r j = src.val := by
          rw [curr,contractionLegPoint_before _ _ shorter]
          exact rightWords _ shorter
        have idx : r.nr 14 - ((i.val-(s.nr 13+1))+1) = j := index
        simp only [code,rightCycleRecordAt,contractionRowWords,idx,repr,nextWords]
        exact ⟨True.intro,rfl,rfl⟩
    refine ⟨data.1,data.2.1,?_⟩
    change ContractionCycleEdgeWords part src dst (contractionRowWords row)
    rw [data.2.2,curr]
    by_cases last : j = 0
    · have endIndex : i.val+1 = cycle.length := by dsimp [j] at last; omega
      have following : dst = contractionLegPoint left base 0 (Nat.zero_le _) := by
        dsimp only [dst,List.get_eq_getElem]
        simp only [endIndex,Nat.mod_self]
        exact contractionCycleOrder_left _ _ _ (Nat.zero_le _)
      rw [following]
      simpa only [nextWords,last,if_pos rfl] using! closing
    · have noWrap : i.val+1 < cycle.length := by dsimp [j] at last; omega
      have smaller : j-1 < right.length := by omega
      have index : left.length+right.length-(i.val+1) = j-1 := by dsimp [j]; omega
      have following : dst = contractionLegPoint right base (j-1) smaller.le := by
        dsimp only [dst,List.get_eq_getElem]
        simp only [Nat.mod_eq_of_lt noWrap]
        simpa only [index] using (contractionCycleOrder_right left right base (i := i.val+1)
          (by omega) (by omega))
      have one : j-1+1 = j := by omega
      have link : (forest.role right[j-1]).parent = some (contractionLegPoint right base j bounded) := by
        simpa only [one,contractionLegPoint_before _ _ smaller] using! rightLink (j-1) smaller
      have edge := witnesses.contractionWords links valid link
      have nextRep : rightCycleRepresentativeAt r (j-1) = right[j-1].val := rightWords _ smaller
      simpa only [nextWords,if_neg last,nextRep,following,contractionLegPoint_before _ _ smaller] using edge

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionCycleEdges

/-! matching/MatchingContractionPartition.lean -/
section RppSource_MatchingContractionPartition
namespace VehicleRoutingSurvey.Routing











theorem CompactMatchingPartition.contract_representative {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (cycle : Finset (Fin k)) (base : Fin k) (baseIn : base ∈ cycle)
    (fixed : ∀ v ∈ cycle, part.representative v = v) (odd : Odd cycle.card)
    (covered : ∀ c ∈ cycle, c ≠ base → c ∈ state.covered) (v : Fin k) :
    (part.contract cycle base baseIn fixed odd covered).representative v =
      blossomRepresentative cycle base (part.representative v) := rfl

theorem CompactMatchingPartition.contract_block {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (cycle : Finset (Fin k)) (base : Fin k) (baseIn : base ∈ cycle)
    (fixed : ∀ v ∈ cycle, part.representative v = v) (odd : Odd cycle.card)
    (covered : ∀ c ∈ cycle, c ≠ base → c ∈ state.covered) (v : Fin k) :
    (part.contract cycle base baseIn fixed odd covered).blocks.block v =
      if part.representative v ∈ cycle then part.contractCut cycle else part.blocks.block v := by
  change (if part.blocks.block v ∈ cycle.image part.blocks.block then part.contractCut cycle else part.blocks.block v) = _
  simp only [part.mem_contractionChildren cycle fixed]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionPartition

/-! matching/MatchingContractionCycleMates.lean -/
section RppSource_MatchingContractionCycleMates
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Starting immediately after the new base, the physical cycle lists the right
leg in reverse and then the left leg. Its consecutive pairs are the matched
forest links in those legs, in both orientations. -/
theorem alternatingForest_contractionRotationMates {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {forest : AlternatingForestState (Fin k)}
    {tight : Fin k → Fin k → Prop} (valid : forest.valid state.partialMate tight)
    {a b base : Fin k} {pa pb : Option (Fin k)} (aOuter : forest.role a = .outer pa)
    (bOuter : forest.role b = .outer pb) (ancestor : forest.commonAncestor a b = some base) :
    let left := traceBefore base (forest.traceToRoot a)
    let right := traceBefore base (forest.traceToRoot b)
    ∀ u v, s(u,v) ∈ alternatingEdges (right.reverse ++ left) →
      state.partialMate u = some v ∧ state.partialMate v = some u := by
  obtain ⟨⟨p,baseOuter⟩,_⟩ := alternatingForest_contractionLabels valid aOuter bOuter ancestor
  have leg {x : Fin k} {q : Option (Fin k)} (outer : forest.role x = .outer q)
      (member : base ∈ forest.traceToRoot x) :
      let before := traceBefore base (forest.traceToRoot x)
      before.length % 2 = 0 ∧ ∀ e ∈ alternatingEdges before, e ∈ state.edges := by
    intro before
    obtain ⟨head,distinct,_,chain,_⟩ := AlternatingForestState.traceToRoot_spec valid (x := x) (by simp [outer])
    have parents := chain.imp fun _ _ h => h.1
    have even := trace_before_outer_even valid member outer baseOuter head distinct parents
    obtain ⟨pre,post,eq⟩ := List.append_of_mem member
    have noBase : base ∉ pre := fun h => (List.nodup_append.mp (eq ▸ distinct)).2.2 base h base (by simp) rfl
    have preEq : before = pre := by simp only [before,eq,traceBefore_eq noBase]
    have pairs := trace_pairs_in_matching valid (M := state.edges) (fun _ _ m => state.partialMate_some_iff.mp m)
      (forest.traceToRoot x) (fun v hv => ⟨q,(show x = v from by simpa only [head,Option.mem_some_iff] using hv) ▸ outer⟩) parents
    refine ⟨even,?_⟩
    intro e he
    apply pairs
    have parity : pre.length % 2 = 0 := preEq ▸ even
    rw [eq,alternatingEdges_append_even _ _ parity]
    exact List.mem_append_left _ (preEq ▸ he)
  obtain ⟨inA,pre,after,split,_⟩ := firstSharedAncestor_eq_some_iff.mp ancestor
  have inB : base ∈ forest.traceToRoot b := split.symm ▸ List.mem_append_right pre (by simp)
  obtain ⟨_,pairsA⟩ := leg aOuter inA
  obtain ⟨even,pairsB⟩ := leg bOuter inB
  intro left right u v he
  have revEven : right.reverse.length % 2 = 0 := by simpa only [List.length_reverse] using even
  rw [alternatingEdges_append_even _ _ revEven,alternatingEdges_reverse_even _ even] at he
  have edge : s(u,v) ∈ state.edges := (List.mem_append.mp he).elim (fun h => pairsB _ (List.mem_reverse.mp h)) (pairsA _)
  exact ⟨state.partialMate_some_iff.mpr edge,state.partialMate_some_iff.mpr (Sym2.eq_swap ▸ edge)⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionCycleMates

/-! matching/MatchingContractionTraceMates.lean -/
section RppSource_MatchingContractionTraceMates
namespace VehicleRoutingSurvey.Routing

/-- Every nonbase child on the traced cycle has its matched partner on the same
cycle, distinct from the base. This is the matching retained by contraction. -/
theorem alternatingForest_contractionMates {n : ℕ} {state : AlternatingForestState (Fin n)}
    {mate : Fin n → Option (Fin n)} {tight : Fin n → Fin n → Prop} (valid : state.valid mate tight)
    {a b base : Fin n} {pa pb : Option (Fin n)} (aOuter : state.role a = .outer pa) (bOuter : state.role b = .outer pb)
    (ancestor : state.commonAncestor a b = some base) :
    let cycle := (contractionCycle (state.traceToRoot a) (state.traceToRoot b) base).toFinset
    ∀ x ∈ cycle, x ≠ base → ∃ y ∈ cycle, y ≠ base ∧ mate x = some y := by
  intro cycle
  obtain ⟨⟨baseParent,baseRole⟩,_⟩ := alternatingForest_contractionLabels valid aOuter bOuter ancestor
  have leg {first : Fin n} {p : Option (Fin n)} (outer : state.role first = .outer p)
      (baseIn : base ∈ state.traceToRoot first) (x : Fin n) (inLeg : x ∈ traceBefore base (state.traceToRoot first)) :
      ∃ y ∈ traceBefore base (state.traceToRoot first) ++ [base], y ≠ base ∧ mate x = some y := by
    obtain ⟨start,noDup,_,chain,_⟩ := AlternatingForestState.traceToRoot_spec valid (x := first) (by simp [outer])
    have links := chain.imp (fun _ _ h => h.1)
    have legFacts := trace_leg_valid valid baseIn outer start noDup links
    obtain ⟨before,after,splitTrace⟩ := List.append_of_mem baseIn
    have noBase : base ∉ before := fun h => (List.nodup_append.mp (splitTrace ▸ noDup)).2.2 base h base (by simp) rfl
    have preEq : traceBefore base (state.traceToRoot first) = before := by rw [splitTrace,traceBefore_eq noBase]
    have combined : state.traceToRoot first = (before ++ [base]) ++ after := by simpa [List.append_assoc] using splitTrace
    rw [preEq] at inLeg legFacts ⊢
    have inside := List.mem_append_left [base] inLeg
    obtain ⟨parent,atParent,link⟩ := chain_next_before_last before ((combined ▸ links).left_of_append) x inLeg
    rcases parent_step_roles valid link with ⟨q,kind,parentKind,_⟩ | ⟨q,kind,parentKind⟩
    · have facts := valid x
      rw [kind] at facts
      refine ⟨parent,atParent,?_,facts.2.1⟩
      intro eq
      have conflict := (eq ▸ parentKind).symm.trans baseRole
      cases conflict
    · have facts := valid x
      rw [kind] at facts
      obtain ⟨child,paired,childRole⟩ := facts.2.2.1
      refine ⟨child,legFacts.2.2 x inside parent kind child paired,?_,paired⟩
      intro eq
      have rank := valid child
      rw [childRole] at rank
      have strict := rank.2.2.2.2
      rw [eq] at strict
      exact (not_lt_of_ge (legFacts.1 x inside)) strict
  have contains (x : Fin n) : x ∈ cycle ↔ x = base ∨ x ∈ traceBefore base (state.traceToRoot a) ∨ x ∈ traceBefore base (state.traceToRoot b) := by
    simp only [cycle,contractionCycle,List.mem_toFinset,List.mem_append,List.mem_cons,List.mem_reverse]
    tauto
  obtain ⟨leftIn,br,after,splitRight,_⟩ := firstSharedAncestor_eq_some_iff.mp ancestor
  have rightIn : base ∈ state.traceToRoot b := splitRight.symm ▸ List.mem_append_right br (by simp)
  intro x hx different
  rcases ((contains x).mp hx).resolve_left different with left | right
  · obtain ⟨y,hy,other,paired⟩ := leg aOuter leftIn x left
    refine ⟨y,(contains y).mpr (Or.inr (Or.inl ((List.mem_append.mp hy).resolve_right (by simpa using other)))),other,paired⟩
  · obtain ⟨y,hy,other,paired⟩ := leg bOuter rightIn x right
    refine ⟨y,(contains y).mpr (Or.inr (Or.inr ((List.mem_append.mp hy).resolve_right (by simpa using other)))),other,paired⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionTraceMates

/-! matching/MatchingContractionPrimal.lean -/
section RppSource_MatchingContractionPrimal
namespace VehicleRoutingSurvey.Routing



/-- The old top bases and matched cycle edges furnish the new block's internal
near-perfect matching. Its distinguished base keeps an exterior mate when matched. -/
theorem CompactTopMatching.contract {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    (top : CompactTopMatching part) {cycle : Finset (Fin k)} {base : Fin k} (baseIn : base ∈ cycle)
    (fixed : ∀ v ∈ cycle, part.representative v = v) (odd : Odd cycle.card)
    (pairs : ∀ x ∈ cycle, x ≠ base → ∃ y ∈ cycle, y ≠ base ∧ state.partialMate x = some y) :
    CompactTopMatching (part.contract cycle base baseIn fixed odd (contractionMates_covered pairs)) := by
  let next := part.contract cycle base baseIn fixed odd (contractionMates_covered pairs)
  have rep (v : Fin k) : next.representative v = if part.representative v ∈ cycle then base else part.representative v := rfl
  have block := part.contract_block cycle base baseIn fixed odd (contractionMates_covered pairs)
  have maps (v : Fin k) : part.blocks.block v ⊆ next.blocks.block v := by
    rw [block]
    by_cases merged : part.representative v ∈ cycle
    · rw [if_pos merged]
      intro w hw
      exact (part.mem_contractCut cycle fixed w).mpr
        ((part.same_block.mpr (part.blocks.same_of_mem (Finset.mem_univ v) hw)).symm ▸ merged)
    · rw [if_neg merged]
  change CompactTopMatching next
  constructor
  · intro u v atU away
    have equal := next.blocks.same_of_mem (Finset.mem_univ u) atU
    by_cases atPort : part.representative v = v
    · have newBase : next.representative v ≠ v := fun h => away ((next.constant v u equal).symm.trans h).symm
      have inside : v ∈ cycle := by
        by_contra outside
        exact newBase (by rw [rep,atPort,if_neg outside])
      have apart : v ≠ base := by
        intro same
        exact newBase (by rw [rep,atPort,if_pos inside,same])
      obtain ⟨w,hw,_,matched⟩ := pairs v inside apart
      have member := state.partialMate_some_iff.mp matched
      have wAt : w ∈ next.blocks.block v := by
        rw [block,atPort,if_pos inside]
        exact (part.mem_contractCut cycle fixed w).mpr ((fixed w hw).symm ▸ hw)
      refine ⟨s(v,w),member,Sym2.mem_mk_left _ _,?_⟩
      intro z hz
      rcases Sym2.mem_iff.mp hz with rfl | rfl
      · exact atU
      · exact equal ▸ wAt
    · obtain ⟨e,he,hv,others⟩ := top.interior v v (part.blocks.self_mem v (Finset.mem_univ v)) (Ne.symm atPort)
      exact ⟨e,he,hv,fun z hz => equal ▸ maps v (others z hz)⟩
  · intro u v newFixed paired
    change state.partialMate u = some v at paired
    have oldFixed : part.representative u = u := by
      by_cases merged : part.representative u ∈ cycle
      · have baseEq : base = u := by simpa only [rep,if_pos merged] using newFixed
        exact baseEq ▸ fixed base baseIn
      · simpa only [rep,if_neg merged] using newFixed
    have separate := top.matchedBase oldFixed paired
    have edge := state.partialMate_some_iff.mp paired
    have vFixed := (top.crossing_endpoints edge separate).2
    intro equal
    have same := next.same_block.mpr equal
    rw [rep,rep,oldFixed,vFixed] at same
    by_cases a : u ∈ cycle <;> by_cases b : v ∈ cycle
    · have baseEq : base = u := by simpa only [rep,oldFixed,if_pos a] using newFixed
      have diff : v ≠ base := fun h => separate (congrArg part.blocks.block (baseEq.symm.trans h.symm))
      obtain ⟨w,_,other,reverse⟩ := pairs v b diff
      have backwards := state.partialMate_some_iff.mpr (Sym2.eq_swap ▸ edge : s(v,u) ∈ state.edges)
      exact other ((Option.some.inj (reverse.symm.trans backwards)).trans baseEq.symm)
    · simp only [if_pos a,if_neg b] at same
      exact b (same ▸ baseIn)
    · simp only [if_neg a,if_pos b] at same
      exact a (same.symm ▸ baseIn)
    · simp only [if_neg a,if_neg b] at same
      exact separate (congrArg part.blocks.block same)

/-- The new cut also satisfies the invariant for previously zero-dual blossoms
that may acquire dual mass on a later iteration. -/
theorem contractionInternalCuts {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    (top : CompactTopMatching part) (internal : state.InternalCuts) {cycle : Finset (Fin k)} {base : Fin k}
    (baseIn : base ∈ cycle) (fixed : ∀ v ∈ cycle, part.representative v = v) (odd : Odd cycle.card)
    (pairs : ∀ x ∈ cycle, x ≠ base → ∃ y ∈ cycle, y ≠ base ∧ state.partialMate x = some y) :
    (state.registerCut (part.contractCut cycle) (part.contractCut_odd cycle fixed odd)).InternalCuts := by
  let next := part.contract cycle base baseIn fixed odd (contractionMates_covered pairs)
  have nextTop := top.contract baseIn fixed odd pairs
  have cut : next.blocks.block base = part.contractCut cycle := by
    rw [part.contract_block, fixed base baseIn, if_pos baseIn]
  have keep : next.representative base = base := by
    rw [part.contract_representative, fixed base baseIn,blossomRepresentative,if_pos baseIn]
  apply internal.registerCut
  refine ⟨base,(part.mem_contractCut cycle fixed base).mpr ((fixed base baseIn).symm ▸ baseIn),?_⟩
  intro v hv different
  obtain ⟨e,he,touch,others⟩ := nextTop.interior base v (cut.symm ▸ hv) (keep.symm ▸ different)
  exact ⟨e,he,touch,fun w hw => cut ▸ others w hw⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionPrimal

/-! matching/MatchingContractionCounts.lean -/
section RppSource_MatchingContractionCounts
namespace VehicleRoutingSurvey.Routing

theorem matchingContractionMaskAddresses_mem {n : ℕ} (s : ArithmeticState)
    (left right : List (Fin n)) (base v : Fin n)
    (baseAt : s.nr 12 = base.val)
    (leftAt : (List.range (s.nr 13)).map (fun j => s.nm (s.nr 83 + j)) = left.map Fin.val)
    (rightAt : (List.range (s.nr 14)).map (fun j => s.nm (s.nr 84 + j)) = right.map Fin.val) :
    s.nr 89 + v.val ∈ matchingContractionMaskAddresses s ↔ v ∈ base :: (left ++ right) := by
  have leftValues : (List.range (s.nr 13)).map (fun j => s.nr 89 + s.nm (s.nr 83 + j)) =
      left.map (fun j => s.nr 89 + j.val) := by
    have same := congrArg (List.map (s.nr 89 + ·)) leftAt
    simpa only [List.map_map, Function.comp_def] using same
  have rightValues : (List.range (s.nr 14)).map (fun j => s.nr 89 + s.nm (s.nr 84 + j)) =
      right.map (fun j => s.nr 89 + j.val) := by
    have same := congrArg (List.map (s.nr 89 + ·)) rightAt
    simpa only [List.map_map, Function.comp_def] using same
  rw [matchingContractionMaskAddresses, baseAt, leftValues, rightValues, List.cons_append]
  let f := fun j : Fin n => s.nr 89+j.val
  have injective : Function.Injective f := fun _ _ eq => Fin.ext (Nat.add_left_cancel eq)
  simpa only [List.map_cons, List.map_append, f] using
    (List.mem_map_of_injective injective : f v ∈ (base :: (left ++ right)).map f ↔ v ∈ base :: (left ++ right))



theorem traceOuterRowsAt_eq_filter {n : ℕ} (s : ArithmeticState) {start count : ℕ}
    (trace : List (Fin n)) (outer : Fin n → Prop) [DecidablePred outer]
    (encoded : (List.range count).map (fun j => s.nm (start + j)) = trace.map Fin.val)
    (label : ∀ v : Fin n, s.nm (s.nr 51 + v.val) = 1 ↔ outer v) :
    traceOuterRowsAt s start count = (trace.filter (fun v => decide (outer v))).map Fin.val := by
  have raw : traceOuterRowsAt s start count =
      ((List.range count).map (fun j => s.nm (start + j))).filter (fun v => decide (s.nm (s.nr 51 + v) = 1)) := by
    simp [traceOuterRowsAt, tracedOuterReps, tracedRepresentativeOuter, tracedRepresentative, List.filter_map, Function.comp_def]
  rw [raw, encoded, List.filter_map]
  apply congrArg (List.map Fin.val)
  apply List.filter_congr
  intro v _
  simp [Function.comp_def, label v]





end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionCounts

/-! matching/MatchingContractionPrefixTyped.lean -/
section RppSource_MatchingContractionPrefixTyped
namespace VehicleRoutingSurvey.Routing

def contractionTypedOuterRows {k : ℕ} (forest : AlternatingForestState (Fin k))
    (base : Fin k) (left right : List (Fin k)) : List (Fin k) :=
  base :: (left ++ right).filter (fun v => decide (alternatingRoleCode (forest.role v) = 1))

def contractionTypedFreshOriginals {k : ℕ} (forest : AlternatingForestState (Fin k)) (representative : Fin k → Fin k)
    (base : Fin k) (left right : List (Fin k)) : List (Fin k) :=
  (List.finRange k).filter fun v => decide (representative v ∈ base :: (left ++ right) ∧
    2 ≤ alternatingRoleCode (forest.role (representative v)))

/-- The prefixes encoded in the two scratch arrays are the exact typed vertex
lists from the original forest and compact representative map. -/
theorem MatchingContractionPrefixView.encodedLists {k : ℕ} {s t : ArithmeticState}
    (view : MatchingContractionPrefixView s t) (forest : AlternatingForestState (Fin k))
    (rep : Fin k → Fin k) (base : Fin k) (left right : List (Fin k))
    (size : s.nr 55 = k) (baseAt : s.nr 12 = base.val)
    (leftAt : (List.range (s.nr 13)).map (fun j => s.nm (s.nr 83+j)) = left.map Fin.val)
    (rightAt : (List.range (s.nr 14)).map (fun j => s.nm (s.nr 84+j)) = right.map Fin.val)
    (forestAt : AlternatingForestMemory forest (s.nr 51) s.nm)
    (repAt : ∀ v : Fin k, originalTopRepresentative s v.val = (rep v).val) :
    let absorbed := contractionTypedOuterRows forest base left right
    let fresh := contractionTypedFreshOriginals forest rep base left right
    t.nr 87 = absorbed.length ∧ t.nr 99 = fresh.length ∧
      (∀ j : Fin absorbed.length, t.nm (t.nr 86+j.val) = (absorbed.get j).val) ∧
      (∀ j : Fin fresh.length, t.nm (t.nr 88+j.val) = (fresh.get j).val) := by
  intro absorbed fresh
  let outer := fun v : Fin k => alternatingRoleCode (forest.role v) = 1
  letI : DecidablePred outer := fun v => inferInstanceAs (Decidable (alternatingRoleCode (forest.role v) = 1))
  have outerAt (v : Fin k) : s.nm (s.nr 51+v.val) = 1 ↔ outer v := by rw [(forestAt v).1]
  have absorbedAt : absorbedMatchingOuterRows s = absorbed.map Fin.val := by
    rw [absorbedMatchingOuterRows, traceOuterRowsAt_eq_filter s left outer leftAt outerAt,
      traceOuterRowsAt_eq_filter s right outer rightAt outerAt]
    simp [baseAt, absorbed, contractionTypedOuterRows, outer, List.filter_append]
  have range : (List.finRange k).map Fin.val = List.range k := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  have freshAt : contractionFreshOriginalsBefore s = fresh.map Fin.val := by
    unfold contractionFreshOriginalsBefore
    rw [size, ← range, List.filter_map]
    apply congrArg (List.map Fin.val)
    apply List.filter_congr
    intro v _
    have mask := matchingContractionMaskAddresses_mem s left right base (rep v) baseAt leftAt rightAt
    simp [fresh, contractionTypedFreshOriginals, Function.comp_def, repAt v, mask, (forestAt (rep v)).1]
  have countA : t.nr 87 = absorbed.length := by simpa only [absorbedAt, List.length_map] using view.absorbedCount
  have countF : t.nr 99 = fresh.length := by simpa only [freshAt, List.length_map] using view.freshCount
  refine ⟨countA, countF, ?_, ?_⟩
  · intro j
    have atIndex := view.absorbed j.val (countA.symm ▸ j.isLt)
    rw [absorbedAt, List.getElem?_map, List.getElem?_eq_getElem (by exact j.isLt)] at atIndex
    exact atIndex
  · intro j
    have atIndex := view.fresh j.val (countF.symm ▸ j.isLt)
    rw [freshAt, List.getElem?_map, List.getElem?_eq_getElem (by exact j.isLt)] at atIndex
    exact atIndex

/-- Read the new representatives and live top-node identifiers and the cycle
mask at the structural prefix exit, using the same trace as the cache repair. -/
theorem MatchingContractionPrefixView.typedTopology {k : ℕ} {s t : ArithmeticState}
    (view : MatchingContractionPrefixView s t) (rep : Fin k → Fin k) (base : Fin k)
    (left right : List (Fin k)) (size : s.nr 55 = k) (baseAt : s.nr 12 = base.val)
    (leftAt : (List.range (s.nr 13)).map (fun j => s.nm (s.nr 83+j)) = left.map Fin.val)
    (rightAt : (List.range (s.nr 14)).map (fun j => s.nm (s.nr 84+j)) = right.map Fin.val)
    (repAt : ∀ v : Fin k, originalTopRepresentative s v.val = (rep v).val)
    (parentEnd : s.nr 52+k ≤ s.nr 57) (repEnd : s.nr 57+k ≤ s.nr 74)
    (startAfter : s.nr 74+k ≤ s.nr 77) (countAfter : s.nr 74+k ≤ s.nr 78)
    (repPort : t.nr 57 = s.nr 57) (nodePort : t.nr 74 = s.nr 74) (maskPort : t.nr 89 = s.nr 89) :
    let cycle := (base :: (left ++ right)).toFinset
    (∀ v : Fin k, t.nm (t.nr 57+v.val) = (blossomRepresentative cycle base (rep v)).val) ∧
    (∀ v : Fin k, blossomNodeAt t v.val =
      if v = base then s.nr 76 else if v ∈ cycle then 0 else blossomNodeAt s v.val) ∧
    (∀ v : Fin k, t.nm (t.nr 89+v.val) ≠ 0 ↔ v ∈ cycle) := by
  intro cycle
  have mask (v : Fin k) : s.nr 89+v.val ∈ matchingContractionMaskAddresses s ↔ v ∈ cycle :=
    (matchingContractionMaskAddresses_mem s left right base v baseAt leftAt rightAt).trans List.mem_toFinset.symm
  have indexIn (v : Fin k) : v.val < s.nr 55 := size.symm ▸ v.isLt
  refine ⟨?_,?_,?_⟩
  · intro v
    rw [repPort, view.representative (size.symm ▸ parentEnd) (size.symm ▸ repEnd) _ (indexIn v),
      baseAt, repAt v]
    by_cases inCycle : rep v ∈ cycle <;> simp [blossomRepresentative, mask, inCycle]
  · intro v
    have isBase : v.val = base.val ↔ v = base := ⟨Fin.ext, congrArg Fin.val⟩
    have parentToNode : s.nr 52+s.nr 55 ≤ s.nr 74 := by
      rw [size]
      exact parentEnd.trans ((Nat.le_add_right _ _).trans repEnd)
    have actual := view.topNodes (size.symm ▸ repEnd) parentToNode (size.symm ▸ startAfter)
      (size.symm ▸ countAfter) _ (indexIn v)
    simpa only [blossomNodeAt, nodePort, baseAt, isBase, mask] using actual
  · intro v
    rw [maskPort, view.cycleMask _ (indexIn v)]
    by_cases inCycle : v ∈ cycle <;> simp [mask, inCycle]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionPrefixTyped

/-! matching/MatchingContractionPairGeometry.lean -/
section RppSource_MatchingContractionPairGeometry
namespace VehicleRoutingSurvey.Routing

/-- The exact two physically collected lists partition the merged fiber into old
outer rows and original vertices which acquire the outer label on this step. -/
theorem contractionTypedPairGeometry {k : ℕ} (forest : AlternatingForestState (Fin k))
    (prior : Fin k → Fin k) (base : Fin k) (left right : List (Fin k))
    (idem : ∀ v, prior (prior v) = prior v)
    (outerFixed : ∀ c, alternatingRoleCode (forest.role c) = 1 → prior c = c)
    (baseOuter : alternatingRoleCode (forest.role base) = 1)
    (marked : ∀ c ∈ left ++ right, forest.role c ≠ .unlabelled) :
    let cycle := (base :: (left ++ right)).toFinset
    let next := fun u => blossomRepresentative cycle base (prior u)
    let after := forest.contract cycle base
    MatchingContractionPairGeometry prior next (fun v => alternatingRoleCode (forest.role v))
      (fun v => alternatingRoleCode (after.role v)) base
      (contractionTypedOuterRows forest base left right) (contractionTypedFreshOriginals forest prior base left right) := by
  intro cycle next after
  let old := fun c => alternatingRoleCode (forest.role c)
  let role := fun c => alternatingRoleCode (after.role c)
  have inCycle (v : Fin k) : v ∈ cycle ↔ v = base ∨ v ∈ left ++ right := by
    simp only [cycle, List.mem_toFinset, List.mem_cons]
  have baseIn : base ∈ cycle := (inCycle base).mpr (.inl rfl)
  have encoded (v : Fin k) : role v = if v ∈ cycle ∧ v ≠ base then 0 else old v := by
    by_cases hidden : v ∈ cycle ∧ v ≠ base
    · simp [role, after, AlternatingForestState.contract, hidden, alternatingRoleCode]
    · cases hv : forest.role v <;> simp [role, old, after, AlternatingForestState.contract, hidden, hv, alternatingRoleCode]
  have afterBase : role base = 1 := by simpa [encoded, old] using baseOuter
  have baseFixed : prior base = base := outerFixed base baseOuter
  have outside (c : Fin k) (diff : c ≠ base) (outer : role c = 1) : c ∉ cycle := by
    intro present
    simp [encoded c, present, diff] at outer
  have oldRows (r : Fin k) : r ∈ contractionTypedOuterRows forest base left right ↔ r ∈ cycle ∧ old r = 1 := by
    rw [inCycle]
    simp only [contractionTypedOuterRows, List.mem_cons, List.mem_filter, decide_eq_true_eq, old]
    constructor
    · rintro (rfl | ⟨inside,kind⟩)
      · exact ⟨Or.inl rfl,baseOuter⟩
      · exact ⟨Or.inr inside,kind⟩
    · rintro ⟨(rfl | inside),kind⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨inside,kind⟩
  have newRows (u : Fin k) : u ∈ contractionTypedFreshOriginals forest prior base left right ↔
      prior u ∈ cycle ∧ 2 ≤ old (prior u) := by
    simp only [contractionTypedFreshOriginals, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
      cycle, List.mem_toFinset, old]
  have merged (u : Fin k) : next u = base ↔ prior u ∈ cycle := by
    by_cases included : prior u ∈ cycle
    · simp [next, blossomRepresentative, included]
    · have different : prior u ≠ base := by rintro eq; exact included (eq.symm ▸ baseIn)
      simp [next, blossomRepresentative, included, different]
  refine ⟨(oldRows base).mpr ⟨baseIn,baseOuter⟩, fun r hr => ((oldRows r).mp hr).2, afterBase,
    fun c diff outer hr => outside c diff outer ((oldRows c).mp hr).1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c diff outer
    change role c = 1 at outer
    simpa only [encoded c, and_false, false_and, if_false, outside c diff outer] using outer
  · intro c diff outer u
    have survives := outside c diff outer
    by_cases included : prior u ∈ cycle
    · have other : prior u ≠ c := by rintro eq; exact survives (eq ▸ included)
      simp [next, blossomRepresentative, included, diff.symm, other]
    · simp [next, blossomRepresentative, included]
  · intro u
    rw [merged, oldRows, newRows]
    constructor
    · intro included
      by_cases on : old (prior u) = 1
      · exact Or.inl ⟨included,on⟩
      · have leg : prior u ∈ left ++ right := (inCycle _).mp included |>.resolve_left (by
          intro same
          exact on (same ▸ baseOuter))
        have live := marked (prior u) leg
        have inner : 2 ≤ old (prior u) := by
          cases h : forest.role (prior u) <;> simp_all [old, alternatingRoleCode]
        exact Or.inr ⟨included,inner⟩
    · rintro (h | h) <;> exact h.1
  · intro u wasOuter
    by_cases included : prior u ∈ cycle
    · rw [(merged u).mpr included]
      exact afterBase
    · change role (next u) = 1
      simp only [next, blossomRepresentative, if_neg included, encoded, included, false_and, if_false]
      exact wasOuter
  · intro c outer
    by_cases same : c = base
    · subst c
      rw [(merged base).mpr (baseFixed.symm ▸ baseIn)]
      exact afterBase
    · have survives := outside c same outer
      have oldOuter : old c = 1 := by
        change role c = 1 at outer
        simpa only [encoded c, survives, false_and, if_false] using outer
      have fixed := outerFixed c oldOuter
      simpa only [next, fixed, blossomRepresentative, if_neg survives] using outer
  · intro u
    by_cases included : prior u ∈ cycle
    · have hit := (merged u).mpr included
      rw [hit]
      exact (merged base).mpr (baseFixed.symm ▸ baseIn)
    · simp [next, blossomRepresentative, included, idem]

/-- Every original vertex outside the promoted list keeps its role code. The
newly outer set therefore gives exactly the increment to every incoming row. -/
theorem contractionTypedOriginalRole {k : ℕ} (forest : AlternatingForestState (Fin k))
    (prior : Fin k → Fin k) (base : Fin k) (left right : List (Fin k))
    (baseOuter : alternatingRoleCode (forest.role base) = 1)
    (marked : ∀ c ∈ left ++ right, forest.role c ≠ .unlabelled) (u : Fin k) :
    let cycle := (base :: (left ++ right)).toFinset
    let next := blossomRepresentative cycle base (prior u)
    alternatingRoleCode ((forest.contract cycle base).role next) =
      if u ∈ contractionTypedFreshOriginals forest prior base left right then 1 else alternatingRoleCode (forest.role (prior u)) := by
  intro cycle next
  have code (v : Fin k) : alternatingRoleCode ((forest.contract cycle base).role v) =
      if v ∈ cycle ∧ v ≠ base then 0 else alternatingRoleCode (forest.role v) := by
    by_cases hidden : v ∈ cycle ∧ v ≠ base
    · simp [AlternatingForestState.contract,hidden,alternatingRoleCode]
    · cases h : forest.role v <;> simp [AlternatingForestState.contract,hidden,h,alternatingRoleCode]
  have promoted : u ∈ contractionTypedFreshOriginals forest prior base left right ↔
      prior u ∈ cycle ∧ 2 ≤ alternatingRoleCode (forest.role (prior u)) := by
    simp only [contractionTypedFreshOriginals,cycle,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq,List.mem_toFinset]
  by_cases inside : prior u ∈ cycle
  · have atBase : next = base := by simp [next,blossomRepresentative,inside]
    rw [atBase,code]
    simp only [not_true_eq_false,eq_self,and_false,if_false,baseOuter]
    have live : forest.role (prior u) ≠ .unlabelled := by
      rcases List.mem_cons.mp (List.mem_toFinset.mp inside) with eq | leg
      · rw [eq]
        intro idle; simp [idle,alternatingRoleCode] at baseOuter
      · exact marked _ leg
    cases h : forest.role (prior u) <;> simp_all [promoted,alternatingRoleCode]
  · have stays : next = prior u := by simp [next,blossomRepresentative,inside]
    rw [stays,code]
    simp [inside,promoted]

theorem contractionPairGeometryFromEdge {k : ℕ} (forest : AlternatingForestState (Fin k))
    (prior : Fin k → Fin k) {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop}
    (valid : forest.valid mate tight) (idem : ∀ u, prior (prior u) = prior u)
    (outerFixed : ∀ c, alternatingRoleCode (forest.role c) = 1 → prior c = c)
    {a b base : Fin k} {pa pb : Option (Fin k)} (aOuter : forest.role a = .outer pa)
    (bOuter : forest.role b = .outer pb) (ancestor : forest.commonAncestor a b = some base) :
    let left := traceBefore base (forest.traceToRoot a)
    let right := traceBefore base (forest.traceToRoot b)
    let cycle := (base :: (left ++ right)).toFinset
    let next := fun u => blossomRepresentative cycle base (prior u)
    let after := forest.contract cycle base
    MatchingContractionPairGeometry prior next (fun v => alternatingRoleCode (forest.role v))
      (fun v => alternatingRoleCode (after.role v)) base
      (contractionTypedOuterRows forest base left right) (contractionTypedFreshOriginals forest prior base left right) := by
  obtain ⟨⟨p,outer⟩,marked⟩ := alternatingForest_contractionLabels valid aOuter bOuter ancestor
  exact contractionTypedPairGeometry forest prior base _ _ idem outerFixed (by simp [outer, alternatingRoleCode]) marked

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionPairGeometry

/-! matching/BlossomCreditContraction.lean -/
section RppSource_BlossomCreditContraction
namespace VehicleRoutingSurvey.Routing

/-- A contraction replaces its outer children by one outer block. Every
original vertex in a nonouter child becomes outer during the contraction. -/
theorem matchingPartitionCounts_shrink {k : ℕ} {vertices : Finset (Fin k)}
    {cuts inherited : Finset (Finset (Fin k))} (blocks : TopLevelMatchingBlocks vertices cuts)
    (before after : Finset (Fin k) → Prop) [DecidablePred before] [DecidablePred after]
    {children : Finset (Finset (Fin k))} (top : children ⊆ vertices.image blocks.block)
    (absorbsTwo : 2 ≤ (((vertices.image blocks.block).filter before) ∩ children).card)
    (outerAfter : ∀ v ∈ vertices, after ((blocks.contract children top).block v) ↔
      before (blocks.block v) ∨ blocks.block v ∈ children) :
    let fresh := ((vertices.filter (fun v => ¬before (blocks.block v))) ∩ children.biUnion id).card
    let absorbed := (((vertices.image blocks.block).filter before) ∩ children).card
    MatchingStageTransition (matchingPartitionCounts blocks before inherited) (1 + fresh + absorbed)
      (matchingPartitionCounts (blocks.contract children top) after inherited) := by
  let merged := children.biUnion id
  let contracted := blocks.contract children top
  let oldNonouter := vertices.filter (fun v => ¬before (blocks.block v))
  let newNonouter := vertices.filter (fun v => ¬after (contracted.block v))
  let oldOuter := (vertices.image blocks.block).filter before
  let newOuter := (vertices.image contracted.block).filter after
  have memberIff (v : Fin k) (inside : v ∈ vertices) : v ∈ merged ↔ blocks.block v ∈ children := by
    constructor
    · intro member
      obtain ⟨S, selected, inS⟩ := Finset.mem_biUnion.mp member
      obtain ⟨w, wIn, blockEq⟩ := Finset.mem_image.mp (top selected)
      have own : blocks.block v = S := (blocks.same_of_mem wIn (blockEq.symm ▸ inS)).trans blockEq
      rwa [own]
    · intro selected
      exact Finset.mem_biUnion.mpr ⟨blocks.block v, selected, blocks.self_mem v inside⟩
  have joins (v : Fin k) (selected : blocks.block v ∈ children) : contracted.block v = merged := by
    simp [contracted, merged, TopLevelMatchingBlocks.contract, selected]
  have stays (v : Fin k) (excluded : blocks.block v ∉ children) : contracted.block v = blocks.block v := by
    simp [contracted, TopLevelMatchingBlocks.contract, excluded]
  have partition : newNonouter = oldNonouter \ merged := by
    ext v
    simp only [newNonouter, oldNonouter, Finset.mem_filter, Finset.mem_sdiff]
    by_cases inside : v ∈ vertices
    · have role : after (contracted.block v) ↔ before (blocks.block v) ∨ blocks.block v ∈ children :=
        outerAfter v inside
      simp only [inside, true_and, role, memberIff v inside]
      tauto
    · simp [inside]
  have vertexCounts : oldNonouter.card = newNonouter.card + (oldNonouter ∩ merged).card := by
    rw [partition, Finset.card_sdiff_add_card_inter]
  have absorbedSubset : oldOuter ∩ children ⊆ children := Finset.inter_subset_right
  have atLeastTwo := absorbsTwo.trans (Finset.card_le_card absorbedSubset)
  obtain ⟨S0, chosen⟩ := Finset.card_pos.mp (show 0 < children.card by omega)
  obtain ⟨v0, inside0, block0⟩ := Finset.mem_image.mp (top chosen)
  have selected0 : blocks.block v0 ∈ children := block0.symm ▸ chosen
  have outerPartition : newOuter = insert merged (oldOuter \ children) := by
    ext B
    constructor
    · intro member
      obtain ⟨visible, outer⟩ := Finset.mem_filter.mp member
      obtain ⟨v, inVertices, identifies⟩ := Finset.mem_image.mp visible
      have isOuter := (outerAfter v inVertices).mp (identifies.symm ▸ outer)
      by_cases selected : blocks.block v ∈ children
      · exact Finset.mem_insert.mpr (Or.inl (identifies.symm.trans (joins v selected)))
      · have old : blocks.block v = B := (stays v selected).symm.trans identifies
        have beforeRole : before (blocks.block v) := isOuter.resolve_right selected
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_sdiff.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v, inVertices, old⟩, old ▸ beforeRole⟩,
            old ▸ selected⟩))
    · intro member
      rcases Finset.mem_insert.mp member with equal | elsewhere
      · subst B
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v0, inside0, joins v0 selected0⟩,
          joins v0 selected0 ▸ (outerAfter v0 inside0).mpr (Or.inr selected0)⟩
      · obtain ⟨beforeBlock, outside⟩ := Finset.mem_sdiff.mp elsewhere
        obtain ⟨oldVisible, oldRole⟩ := Finset.mem_filter.mp beforeBlock
        obtain ⟨v, inVertices, identifies⟩ := Finset.mem_image.mp oldVisible
        have excluded : blocks.block v ∉ children := identifies.symm ▸ outside
        have visible : contracted.block v = B := (stays v excluded).trans identifies
        have outer := (outerAfter v inVertices).mpr (Or.inl (identifies.symm ▸ oldRole))
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v, inVertices, visible⟩, visible ▸ outer⟩
  have mergedNew : merged ∉ oldOuter \ children := by
    intro member
    obtain ⟨beforeBlock, outside⟩ := Finset.mem_sdiff.mp member
    obtain ⟨visible, _⟩ := Finset.mem_filter.mp beforeBlock
    obtain ⟨v, inside, identifies⟩ := Finset.mem_image.mp visible
    have visibleInMerged : v ∈ merged := identifies ▸ blocks.self_mem v inside
    exact outside (identifies ▸ (memberIff v inside).mp visibleInMerged)
  have blockCounts : newOuter.card + (oldOuter ∩ children).card = oldOuter.card + 1 := by
    rw [outerPartition, Finset.card_insert_of_notMem mergedNew]
    have counts := Finset.card_sdiff_add_card_inter oldOuter children
    omega
  exact MatchingStageTransition.shrink (oldNonouter ∩ merged).card (oldOuter ∩ children).card
    absorbsTwo vertexCounts blockCounts le_rfl

end VehicleRoutingSurvey.Routing
end RppSource_BlossomCreditContraction

/-! matching/MatchingContractionCredit.lean -/
section RppSource_MatchingContractionCredit
namespace VehicleRoutingSurvey.Routing

/-- The charged lengths are the exact new-outer vertex and absorbed outer
block counts. Inherited blossoms do not change when the fresh ID is allocated. -/
theorem contractionTypedCredit {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    (part : CompactMatchingPartition state) (forest : AlternatingForestState (Fin k)) (positive : 0 < k)
    (left right : List (Fin k)) (base : Fin k) (distinct : (base :: (left ++ right)).Nodup)
    (baseOuter : alternatingRoleCode (forest.role base) = 1)
    (labelled : ∀ p ∈ left ++ right, forest.role p ≠ .unlabelled)
    (inherited : Finset (Finset (Fin k))) :
    let cycle := (base :: (left ++ right)).toFinset
    ∀ (fixed : ∀ p ∈ cycle, part.representative p = p) (odd : Odd cycle.card)
      (covered : ∀ p ∈ cycle, p ≠ base → p ∈ state.covered)
      (two : ∃ a ∈ cycle, ∃ b ∈ cycle, a ≠ b ∧ alternatingRoleCode (forest.role a) = 1 ∧ alternatingRoleCode (forest.role b) = 1),
    let next := part.contract cycle base (by simp [cycle]) fixed odd covered
    let absorbed := contractionTypedOuterRows forest base left right
    let fresh := contractionTypedFreshOriginals forest part.representative base left right
    MatchingStageTransition (matchingPartitionCounts part.blocks (part.outerBlock forest positive) inherited)
      (1+fresh.length+absorbed.length)
      (matchingPartitionCounts next.blocks (next.outerBlock (forest.contract cycle base) positive) inherited) := by
  classical
  intro cycle fixed odd covered two next absorbed fresh
  let before := part.outerBlock forest positive
  let after := next.outerBlock (forest.contract cycle base) positive
  let children := cycle.image part.blocks.block
  let oldOuter := (Finset.univ.image part.blocks.block).filter before
  have top : children ⊆ Finset.univ.image part.blocks.block := Finset.image_mono _ (Finset.subset_univ _)
  have beforeAt (v : Fin k) : before (part.blocks.block v) ↔ alternatingRoleCode (forest.role (part.representative v)) = 1 := by
    simp only [before,CompactMatchingPartition.outerBlock,part.representativeOf_block]
  have masked (v : Fin k) (h : v ∈ cycle) : forest.role v ≠ .unlabelled := by
    rcases List.mem_cons.mp (List.mem_toFinset.mp h) with rfl | leg
    · intro idle; simp [idle,alternatingRoleCode] at baseOuter
    · exact labelled v leg
  have promoted (v : Fin k) : v ∈ fresh ↔ part.representative v ∈ cycle ∧ ¬before (part.blocks.block v) := by
    simp only [fresh,contractionTypedFreshOriginals,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq,
      beforeAt,List.mem_toFinset,cycle]
    by_cases member : part.representative v ∈ base :: (left ++ right)
    · have label := masked _ (List.mem_toFinset.mpr member)
      cases h : forest.role (part.representative v) <;> simp [h,member,alternatingRoleCode] at label ⊢
    · simp [member]
  have freshSet : fresh.toFinset = (Finset.univ.filter (fun v => ¬before (part.blocks.block v))) ∩ children.biUnion id := by
    ext v
    simp only [List.mem_toFinset,promoted,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and]
    change _ ↔ _ ∧ v ∈ part.contractCut cycle
    rw [part.mem_contractCut cycle fixed]
    tauto
  have freshCount : fresh.length = ((Finset.univ.filter (fun v => ¬before (part.blocks.block v))) ∩ children.biUnion id).card := by
    have unique : fresh.Nodup := (List.nodup_finRange k).filter _
    rw [←freshSet,List.toFinset_card_of_nodup unique]
  have absorbedSet : absorbed.toFinset.image part.blocks.block = oldOuter ∩ children := by
    ext B
    constructor
    · intro member
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp member
      have combo : p ∈ cycle ∧ alternatingRoleCode (forest.role p) = 1 := by
        rcases List.mem_cons.mp (List.mem_toFinset.mp hp) with rfl | tail
        · exact ⟨by simp [cycle],baseOuter⟩
        · obtain ⟨member,on⟩ := List.mem_filter.mp tail
          exact ⟨List.mem_toFinset.mpr (List.mem_cons_of_mem _ member),of_decide_eq_true on⟩
      exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
        (beforeAt p).mpr ((fixed p combo.1).symm ▸ combo.2)⟩,Finset.mem_image.mpr ⟨p,combo.1,rfl⟩⟩
    · intro member
      obtain ⟨outer,inside⟩ := Finset.mem_inter.mp member
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp inside
      have on := (beforeAt p).mp (Finset.mem_filter.mp outer).2
      rw [fixed p hp] at on
      refine Finset.mem_image.mpr ⟨p,List.mem_toFinset.mpr ?_,rfl⟩
      rcases List.mem_cons.mp (List.mem_toFinset.mp hp) with rfl | tail
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨tail,decide_eq_true on⟩)
  have absSubset (v : Fin k) (h : v ∈ absorbed.toFinset) : v ∈ cycle := by
    rcases List.mem_cons.mp (List.mem_toFinset.mp h) with rfl | inside
    · simp [cycle]
    · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_filter.mp inside).1)
  have absUnique : absorbed.Nodup := List.nodup_cons.mpr
    ⟨fun h => (List.nodup_cons.mp distinct).1 (List.mem_filter.mp h).1,(List.nodup_cons.mp distinct).2.filter _⟩
  have absorbedCount : absorbed.length = (oldOuter ∩ children).card := by
    rw [←absorbedSet,Finset.card_image_of_injOn,List.toFinset_card_of_nodup absUnique]
    intro p hp q hq eq
    exact (fixed p (absSubset _ hp)).symm.trans ((part.same_block.mpr eq).trans (fixed q (absSubset _ hq)))
  obtain ⟨a,ha,b,hb,different,oa,ob⟩ := two
  have has (p : Fin k) (hp : p ∈ cycle) (outer : alternatingRoleCode (forest.role p) = 1) : part.blocks.block p ∈ oldOuter ∩ children :=
    Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
        (beforeAt p).mpr ((fixed p hp).symm ▸ outer)⟩,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩
  have progress : 1 < (oldOuter ∩ children).card := Finset.one_lt_card.mpr
    ⟨_,has a ha oa,_,has b hb ob,fun eq => different ((fixed a ha).symm.trans ((part.same_block.mpr eq).trans (fixed b hb)))⟩
  rw [freshCount,absorbedCount]
  apply matchingPartitionCounts_shrink part.blocks before after top progress
  intro v _
  change after (next.blocks.block v) ↔ before (part.blocks.block v) ∨ part.blocks.block v ∈ cycle.image part.blocks.block
  simp only [after,CompactMatchingPartition.outerBlock,next.representativeOf_block,beforeAt,part.mem_contractionChildren cycle fixed]
  rw [part.contract_representative]
  have moves := contractionTypedOriginalRole forest part.representative base left right baseOuter labelled v
  change alternatingRoleCode ((forest.contract cycle base).role (blossomRepresentative cycle base (part.representative v))) = _ at moves
  rw [moves]
  split
  · rename_i h
    exact iff_of_true rfl (Or.inr ((promoted v).mp h).1)
  · rename_i h
    have absent := (promoted v).not.mp h
    rw [beforeAt] at absent
    tauto

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionCredit

/-! matching/MatchingContractionRegisteredDual.lean -/
section RppSource_MatchingContractionRegisteredDual
namespace VehicleRoutingSurvey.Routing

/-- A union of at least two distinct current top blocks is a fresh cut. -/
theorem CompactMatchingPartition.contractCut_fresh {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (cycle : Finset (Fin k))
    (fixed : ∀ v ∈ cycle, part.representative v = v) (many : 1 < cycle.card)
    (nested : ∀ S ∈ state.cuts, ∀ u ∈ S, ∀ v ∈ S, part.blocks.block u = part.blocks.block v) :
    part.contractCut cycle ∉ state.cuts := by
  intro old
  obtain ⟨a,ha,b,hb,absurd⟩ := Finset.one_lt_card.mp many
  have contained (p : Fin k) (hp : p ∈ cycle) := (part.mem_contractCut cycle fixed p).mpr ((fixed p hp).symm ▸ hp)
  exact absurd ((fixed a ha).symm.trans ((part.same_block.mpr (nested _ old a (contained a ha) b (contained b hb))).trans (fixed b hb)))

/-- The contraction prefix advances the old dual tables and writes zero only
at the newly allocated node. The retained IDs still have their shifted values. -/
theorem MatchingSearchDualMemory.contractionAdvanceTables {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s t : ArithmeticState}
    (before : MatchingSearchDualMemory part forest s) (positive : 0 < k)
    (effectiveBase : t.nr 62 = s.nr 62) (nodeBase : t.nr 75 = s.nr 75)
    (allocated : ∀ C ∈ state.cuts, before.node C < s.nr 76)
    (writes : t.rm = Function.update
      (iterateBlossomDuals {s with rm := advancedEffectiveMemory s} (s.nr 55))
      (s.nr 75+s.nr 76) 0) :
    let p := fun x => state.potential x + s.rr 1 * forestVertexDirection part.blocks (part.dualLabel forest positive) x
    let z := fun B => state.cutDual B + s.rr 1 * forestCutDirection part.blocks (part.dualLabel forest positive) B
    (∀ v : Fin k, t.rm (t.nr 62+v.val) = effectiveVertexPotential state.cuts p z v) ∧
      (∀ C ∈ state.cuts, t.rm (t.nr 75+before.node C) = z C) ∧
      t.rm (t.nr 75+s.nr 76) = 0 := by
  intro p z
  let advanced := {s with rm := iterateBlossomDuals {s with rm := advancedEffectiveMemory s} (s.nr 55)}
  refine ⟨?_, ?_, ?_⟩
  · intro v
    have below : s.nr 62+v.val < s.nr 75+s.nr 76 :=
      ((Nat.add_lt_add_left v.isLt _).trans_le before.separated).trans_le (Nat.le_add_right _ _)
    rw [effectiveBase, writes, Function.update_of_ne below.ne]
    exact before.advanced_effective_table (t := advanced) positive rfl rfl v
  · intro C present
    have below : s.nr 75+before.node C < s.nr 75+s.nr 76 := Nat.add_lt_add_left (allocated C present) _
    rw [nodeBase, writes, Function.update_of_ne below.ne]
    exact before.advanced_cut_table (t := advanced) positive rfl rfl present
  · rw [nodeBase, writes, Function.update_self]

/-- The committed ID, zero dual, compact top-node map, and surviving older
dual words form the new registered search-dual memory at the current point. -/
noncomputable def contractionRegisteredDual {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (forest : AlternatingForestState (Fin k))
    (cycle : Finset (Fin k)) (base : Fin k) (baseIn : base ∈ cycle) (fixed : ∀ v ∈ cycle, part.representative v = v)
    (odd : Odd cycle.card) (many : 1 < cycle.card) (covered : ∀ v ∈ cycle, v ≠ base → v ∈ state.covered)
    (nested : ∀ S ∈ state.cuts, ∀ u ∈ S, ∀ v ∈ S, part.blocks.block u = part.blocks.block v)
    (s t : ArithmeticState) (old : MatchingSearchDualMemory part forest s)
    (freshId : ℕ) (positive : 0 < freshId) (allocated : ∀ C ∈ state.cuts, old.node C < freshId)
    (dimension : t.nr 55 = k) (separated : t.nr 62+k ≤ t.nr 75)
    (effective : ∀ v : Fin k, t.rm (t.nr 62+v.val) = effectiveVertexPotential state.cuts state.potential state.cutDual v)
    (values : ∀ C ∈ state.cuts, t.rm (t.nr 75+old.node C) = state.cutDual C)
    (atFresh : t.rm (t.nr 75+freshId) = 0)
    (reps : ∀ v : Fin k, t.nm (t.nr 57+v.val) = (blossomRepresentative cycle base (part.representative v)).val)
    (roles : AlternatingForestMemory (forest.contract cycle base) (t.nr 51) t.nm)
    (topIds : ∀ v : Fin k, blossomNodeAt t v.val =
      if v = base then freshId else if v ∈ cycle then 0 else blossomNodeAt s v.val) :
    MatchingSearchDualMemory (part.contract cycle base baseIn fixed odd covered) (forest.contract cycle base) t := by
  classical
  let ids := fun C => if C = part.contractCut cycle then freshId else old.node C
  have fresh : part.contractCut cycle ∉ state.cuts := part.contractCut_fresh cycle fixed many nested
  have oldId {C : Finset (Fin k)} (oldCut : C ∈ state.cuts) : ids C = old.node C :=
    if_neg (show C ≠ part.contractCut cycle from fun eq => fresh (eq ▸ oldCut))
  have freshAt : ids (part.contractCut cycle) = freshId := if_pos rfl
  have size : 1 < (part.contractCut cycle).card := by
    obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp many
    have found (x : Fin k) (hx : x ∈ cycle) : x ∈ part.contractCut cycle :=
      (part.mem_contractCut cycle fixed x).mpr ((fixed x hx).symm ▸ hx)
    exact Finset.one_lt_card.mpr ⟨a,found a ha,b,found b hb,ne⟩
  refine ⟨dimension,separated,reps,roles,?_,ids,?_,?_,?_,?_⟩
  · intro v
    change t.rm _ = effectiveVertexPotential (insert (part.contractCut cycle) state.cuts) state.potential
      (extendBlossomCutDual state.cuts state.cutDual) v
    rw [effectiveVertexPotential_register_cut]
    exact effective v
  · intro C member
    rcases Finset.mem_insert.mp member with newCut | oldCut
    · simpa only [newCut,freshAt] using positive.ne'
    · rw [oldId oldCut]; exact old.nodeNonzero _ oldCut
  · intro C hc D hd eq
    rcases Finset.mem_insert.mp hc with c | c <;> rcases Finset.mem_insert.mp hd with d | d
    · exact c.trans d.symm
    · exact ((allocated D d).ne' (by simpa only [c,freshAt,oldId d] using eq)).elim
    · exact ((allocated C c).ne (by simpa only [d,freshAt,oldId c] using eq)).elim
    · exact old.nodeInjective c d ((oldId c).symm.trans (eq.trans (oldId d)))
  · intro C hc
    change t.rm (t.nr 75+ids C) = extendBlossomCutDual state.cuts state.cutDual C
    rcases Finset.mem_insert.mp hc with newCut | c
    · simpa only [newCut,freshAt,extendBlossomCutDual,if_neg fresh] using atFresh
    · rw [oldId c,extendBlossomCutDual,if_pos c]
      exact values _ c
  · intro v
    rw [topIds v,part.contract_representative,part.contract_block]
    by_cases atBase : v = base
    · subst v
      have nonsingleton : (part.contractCut cycle).card ≠ 1 := Nat.ne_of_gt size
      simpa only [blossomRepresentative,fixed base baseIn,if_pos baseIn,eq_self,if_true,true_and,if_pos nonsingleton]
        using freshAt.symm
    · rw [if_neg atBase]
      by_cases belongs : v ∈ cycle
      · simp [blossomRepresentative,belongs,fixed v belongs,Ne.symm atBase]
      · rw [if_neg belongs,old.top v]
        by_cases absorbed : part.representative v ∈ cycle
        · have inactive : part.representative v ≠ v := fun eq => belongs (eq ▸ absorbed)
          simp [blossomRepresentative,absorbed,inactive,Ne.symm atBase]
        · simp only [blossomRepresentative,if_neg absorbed]
          by_cases active : part.representative v = v ∧ (part.blocks.block v).card ≠ 1
          · rw [if_pos active,if_pos active]
            exact (oldId (part.blocks.cut_mem (Finset.mem_univ v) active.2)).symm
          · simp [active]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionRegisteredDual

/-! matching/MatchingCutGroupMeaning.lean -/
section RppSource_MatchingCutGroupMeaning
namespace VehicleRoutingSurvey.Routing

open Classical in
noncomputable def matchingCutGroupEntry {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (i : Fin k) : Option (DualSlack (MatchingDualEvent k)) :=
  if part.representative i = i ∧ (part.blocks.block i).card ≠ 1 ∧ ∃ p, forest.role i = .inner p then
    some ⟨.cut (part.blocks.block i), state.cutDual (part.blocks.block i), 1⟩ else none

/-- A cut row has at most one candidate. The physical index names its unique
active inner base, and its value is the registered cut dual. -/
theorem matchingCutGroupEntry_mem {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (positive : 0 < k) (i : Fin k) (d : DualSlack (MatchingDualEvent k)) :
    d ∈ matchingSearchSlacks part forest positive ∧
      (MatchingCandidateGroup.cut i).admits part.blocks forest (part.representativeOf positive) d ↔
      matchingCutGroupEntry part forest i = some d := by
  classical
  let label := part.dualLabel forest positive
  let dc := forestCutDirection part.blocks label
  let B := part.blocks.block i
  have inTop : B ∈ Finset.univ.image part.blocks.block := Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have rateAt (fixed : part.representative i = i) (nonsingle : B.card ≠ 1) {p : Fin k}
      (inner : forest.role i = .inner p) : -dc B = 1 := by
    change -(if B ∈ Finset.univ.image part.blocks.block ∧ B.card ≠ 1 then label B else 0) = 1
    rw [if_pos ⟨inTop, nonsingle⟩]
    change -(forest.role (part.representativeOf positive (part.blocks.block i))).dualDirection = 1
    rw [part.representativeOf_block, fixed, inner]
    norm_num [AlternatingForestRole.dualDirection]
  constructor
  · rintro ⟨present, speed, S, shape, port⟩
    change d ∈ _ ++ state.cuts.toList.map (matchingCutSlack state.cutDual dc) at present
    rcases List.mem_append.mp present with edge | cut
    · obtain ⟨e, _, rfl⟩ := List.mem_map.mp edge
      cases shape
    obtain ⟨C, _, rfl⟩ := List.mem_map.mp cut
    have equal : C = S := MatchingDualEvent.cut.inj shape
    subst S
    change -dc C = 1 at speed
    have negative : dc C < 0 := by linarith
    obtain ⟨⟨top, nonsingle⟩, p, inner⟩ := (forestCutDirection_negative_iff part.blocks
      (fun T => forest.role (part.representativeOf positive T)) C).mp negative
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp top
    have ref := (part.representativeOf_block positive v).symm.trans port
    have fixed : part.representative i = i := by rw [← ref]; exact part.representative_idem v
    have block : B = part.blocks.block v := (part.same_block.mp (fixed.trans ref.symm))
    have enabled : part.representative i = i ∧ (part.blocks.block i).card ≠ 1 ∧ ∃ q, forest.role i = .inner q :=
      ⟨fixed, by change B.card ≠ 1; rwa [block], p, port ▸ inner⟩
    rw [matchingCutGroupEntry, if_pos enabled]
    change some (⟨.cut B, state.cutDual B, 1⟩ : DualSlack (MatchingDualEvent k)) =
      some ⟨.cut (part.blocks.block v), state.cutDual (part.blocks.block v), -dc (part.blocks.block v)⟩
    rw [block, speed]
  · unfold matchingCutGroupEntry
    split
    · rename_i h
      intro found
      cases found
      obtain ⟨fixed, nonsingle, p, inner⟩ := h
      have rate := rateAt fixed nonsingle inner
      refine ⟨List.mem_append_right _ (List.mem_map.mpr ⟨B, ?_, ?_⟩), rfl, B, rfl, ?_⟩
      · exact Finset.mem_toList.mpr (part.blocks.cut_mem (Finset.mem_univ i) nonsingle)
      · change (⟨.cut B, state.cutDual B, -dc B⟩ : DualSlack (MatchingDualEvent k)) = ⟨.cut B, state.cutDual B, 1⟩
        rw [rate]
      · exact (part.representativeOf_block positive i).trans fixed
    · intro h
      cases h




/-- Because at most one cut belongs to a row, any cached minimum is exactly
the entry determined by the forest and top partition. -/
theorem matchingCutGroupEntry_of_least {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {i : Fin k}
    {cached : Option (DualSlack (MatchingDualEvent k))}
    (least : LeastSlackEntry ((matchingSearchSlacks part forest positive).filter fun d =>
      @decide _ (Classical.propDecidable ((MatchingCandidateGroup.cut i).admits part.blocks forest
        (part.representativeOf positive) d))) cached) :
    cached = matchingCutGroupEntry part forest i := by
  classical
  cases stored : cached with
  | some d =>
    obtain ⟨present, admitted⟩ := List.mem_filter.mp (least.sound stored)
    exact ((matchingCutGroupEntry_mem part forest positive i d).mp ⟨present, of_decide_eq_true admitted⟩).symm
  | none =>
    cases lookup : matchingCutGroupEntry part forest i with
    | none => rfl
    | some d =>
      obtain ⟨present, admitted⟩ := (matchingCutGroupEntry_mem part forest positive i d).mpr lookup
      obtain ⟨_, hit, _⟩ := least.covers d (List.mem_filter.mpr ⟨present, decide_eq_true admitted⟩)
      rw [stored] at hit
      cases hit


end VehicleRoutingSurvey.Routing
end RppSource_MatchingCutGroupMeaning

/-! matching/MatchingContractionCutMeaning.lean -/
section RppSource_MatchingContractionCutMeaning
namespace VehicleRoutingSurvey.Routing

/-- Contraction clears every old cut row on the cycle. Off the cycle it keeps
the original inner cut and value even when that inner row's parent changes. -/
theorem contractionCutGroupEntry {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    (part : CompactMatchingPartition state) (forest : AlternatingForestState (Fin k)) (cycle : Finset (Fin k))
    (base : Fin k) (baseIn : base ∈ cycle) (fixed : ∀ v ∈ cycle, part.representative v = v) (odd : Odd cycle.card)
    (covered : ∀ c ∈ cycle, c ≠ base → c ∈ state.covered) (baseOuter : ∃ p, forest.role base = .outer p)
    (row : Fin k) :
    let next := part.contract cycle base baseIn fixed odd covered
    matchingCutGroupEntry next (forest.contract cycle base) row =
      if row ∈ cycle then none else matchingCutGroupEntry part forest row := by
  classical
  intro next
  have repr := part.contract_representative cycle base baseIn fixed odd covered row
  have block := part.contract_block cycle base baseIn fixed odd covered row
  have newRep : next.representative row = if part.representative row ∈ cycle then base else part.representative row := repr
  have newBlock : next.blocks.block row = _ := block
  by_cases member : row ∈ cycle
  · rw [if_pos member]
    obtain ⟨p,atBase⟩ := baseOuter
    by_cases atRow : row = base
    · subst row
      simp [matchingCutGroupEntry,AlternatingForestState.contract,atBase]
    · simp [matchingCutGroupEntry,AlternatingForestState.contract,member,atRow]
  · rw [if_neg member]
    by_cases merged : part.representative row ∈ cycle
    · have notBase : base ≠ row := fun eq => member (eq ▸ baseIn)
      have notPort : part.representative row ≠ row := fun eq => member (eq ▸ merged)
      simp [matchingCutGroupEntry,newRep,merged,notBase,notPort]
    · have inner : (∃ p, (forest.contract cycle base).role row = .inner p) ↔ ∃ p, forest.role row = .inner p := by
        cases h : forest.role row <;> simp [AlternatingForestState.contract,member,h]
      simp only [matchingCutGroupEntry,newRep,newBlock,if_neg merged,inner]
      split
      · rename_i enabled
        have live := part.blocks.cut_mem (Finset.mem_univ row) enabled.2.1
        change some (DualSlack.mk (MatchingDualEvent.cut (part.blocks.block row))
          (extendBlossomCutDual state.cuts state.cutDual (part.blocks.block row)) 1) = _
        simp [extendBlossomCutDual,live]
      · rfl



end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionCutMeaning

/-! matching/MatchingExpansionDictionary.lean -/
section RppSource_MatchingExpansionDictionary
namespace VehicleRoutingSurvey.Routing

/-- Decoding the dictionary with a new top-cut map can change only an
already present cut event, at the very port encoded by its first word. -/
theorem matchingDictionary_changeCuts {k : ℕ} (old next : Fin k → Finset (Fin k)) (s : ArithmeticState) (id : ℕ) :
    let before := decodeMatchingDictionaryEvent k old s id
    let after := decodeMatchingDictionaryEvent k next s id
    before = after ∨ ∃ p : Fin k, before = some (.cut (old p)) ∧ after = some (.cut (next p)) := by
  intro before after
  by_cases no : id = 0
  · exact .inl (by simp [before,after,decodeMatchingDictionaryEvent,no])
  by_cases first : s.nm (s.nr 54+((id-1)+(id-1))) < k
  · by_cases second : s.nm (s.nr 54+((id-1)+(id-1))+1) < k
    · exact .inl (by simp only [before,after,decodeMatchingDictionaryEvent,if_neg no,dif_pos first,dif_pos second])
    · by_cases cut : s.nm (s.nr 54+((id-1)+(id-1))+1) = k
      · exact .inr ⟨⟨_,first⟩, by simp only [before,decodeMatchingDictionaryEvent,if_neg no,dif_pos first,dif_neg second,if_pos cut],
          by simp only [after,decodeMatchingDictionaryEvent,if_neg no,dif_pos first,dif_neg second,if_pos cut]⟩
      · exact .inl (by simp only [before,after,decodeMatchingDictionaryEvent,if_neg no,dif_pos first,dif_neg second,if_neg cut])
  · exact .inl (by simp only [before,after,decodeMatchingDictionaryEvent,if_neg no,dif_neg first])

theorem MatchingCandidateRowValid.changeCutMap {k : ℕ} (old next : Fin k → Finset (Fin k))
    {s : ArithmeticState} {i : ℕ} (valid : MatchingCandidateRowValid old s i) : MatchingCandidateRowValid next s i := by
  rcases valid with zero | ⟨id,event,decoded⟩
  · exact .inl zero
  · rcases matchingDictionary_changeCuts old next s (s.nm (s.nr 58+i)) with same | ⟨p,_,found⟩
    · exact .inr ⟨id,event,same.symm.trans decoded⟩
    · exact .inr ⟨id,.cut (next p),found⟩

theorem matchingCandidate_changeCutMap {k : ℕ} (old next : Fin k → Finset (Fin k))
    (s : ArithmeticState) (i : ℕ)
    (survives : ∀ (p : Fin k) (slack rate : ℝ), readMatchingCandidate old s i = some ⟨.cut (old p),slack,rate⟩ →
      next p = old p) : readMatchingCandidate next s i = readMatchingCandidate old s i := by
  rcases matchingDictionary_changeCuts old next s (s.nm (s.nr 58+i)) with same | ⟨p,prior,later⟩
  · simp only [readMatchingCandidate,same]
  · have value : readMatchingCandidate old s i = some ⟨.cut (old p),s.rm (s.nr 59+i),s.rm (s.nr 60+i)⟩ := by
      simp only [readMatchingCandidate,prior,Option.map_some]
    simp only [readMatchingCandidate,prior,later,survives p _ _ value]



end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionDictionary

/-! matching/MatchingExpansionCutMeaning.lean -/
section RppSource_MatchingExpansionCutMeaning
namespace VehicleRoutingSurvey.Routing

/-- Raw edge rows decode identically under either top-cut dictionary. -/
theorem matchingCandidate_changeCutMap_of_edgeGroup {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {s : ArithmeticState}
    (old next : Fin k → Finset (Fin k)) (group : MatchingCandidateGroup k) (edge : ∀ p, group ≠ .cut p)
    (before : LeastSlackEntry ((matchingSearchSlacks part forest positive).filter fun d =>
      @decide _ (Classical.propDecidable (group.admits part.blocks forest (part.representativeOf positive) d)))
      (readMatchingCandidate old s group.slot)) :
    readMatchingCandidate next s group.slot = readMatchingCandidate old s group.slot := by
  classical
  apply matchingCandidate_changeCutMap
  intro p slack rate found
  have allowed := of_decide_eq_true (List.mem_filter.mp (before.sound found)).2
  cases group with
  | outer i =>
    obtain ⟨_,u,v,eq,_⟩ := allowed
    cases eq
  | incoming i =>
    obtain ⟨_,u,eq,_⟩ := allowed
    cases eq
  | cut i => exact (edge i rfl).elim



end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionCutMeaning

/-! matching/MatchingContractionCutMap.lean -/
section RppSource_MatchingContractionCutMap
namespace VehicleRoutingSurvey.Routing

/-- An occupied cut row at the contraction exit still names an old inner
representative outside the cycle. Its dictionary port denotes the same
block before and after contraction. -/
theorem MatchingSearchRows.contractionCutMap {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (positive : 0 < k) (cycle : Finset (Fin k))
    (base : Fin k) (baseIn : base ∈ cycle) (fixed : ∀ v ∈ cycle, part.representative v = v)
    (odd : Odd cycle.card) (covered : ∀ v ∈ cycle, v ≠ base → v ∈ state.covered)
    (baseOuter : ∃ p, forest.role base = .outer p) (s : ArithmeticState) :
    let next := part.contract cycle base baseIn fixed odd covered
    let after := forest.contract cycle base
    MatchingSearchRows next after positive (matchingTopCutAt part) s →
      MatchingSearchRows next after positive (matchingTopCutAt next) s := by
  intro next after rows
  let oldMap := matchingTopCutAt part
  let newMap := matchingTopCutAt next
  refine ⟨rows.layout, rows.count, rows.ids, rows.slacks, rows.rates,
    fun i hi => MatchingCandidateRowValid.changeCutMap oldMap newMap (rows.valid i hi), ?_⟩
  intro g
  have unchanged : readMatchingCandidate newMap s g.slot = readMatchingCandidate oldMap s g.slot := by
    cases g with
    | outer v =>
      exact matchingCandidate_changeCutMap_of_edgeGroup oldMap newMap (.outer v)
        (fun _ eq => by cases eq) (rows.least (.outer v))
    | incoming v =>
      exact matchingCandidate_changeCutMap_of_edgeGroup oldMap newMap (.incoming v)
        (fun _ eq => by cases eq) (rows.least (.incoming v))
    | cut v =>
      apply matchingCandidate_changeCutMap
      intro p slack rate found
      have value := matchingCutGroupEntry_of_least (rows.least (.cut v))
      have survives := contractionCutGroupEntry part forest cycle base baseIn fixed odd covered baseOuter v
      change matchingCutGroupEntry next after v = _ at survives
      change readMatchingCandidate (matchingTopCutAt part) s (MatchingCandidateGroup.cut v).slot = _ at found
      rw [value, survives] at found
      have outside : v ∉ cycle := by
        intro present
        rw [if_pos present] at found
        cases found
      rw [if_neg outside, matchingCutGroupEntry] at found
      have active : part.representative v = v ∧ matchingTopCutAt part p = part.blocks.block v := by
        split at found
        · rename_i enabled
          exact ⟨enabled.1,(MatchingDualEvent.cut.inj (congrArg DualSlack.event (Option.some.inj found))).symm⟩
        · cases found
      have present : (part.blocks.block v).Nonempty := ⟨v,part.blocks.self_mem v (Finset.mem_univ v)⟩
      have port := matchingTopCutAt_port part positive present active.2
      have same : p = v :=
        port.2.2.symm.trans ((part.representativeOf_block positive v).trans active.1)
      subst p
      have unaffected : part.representative v ∉ cycle := by simpa only [active.1] using outside
      have newFixed : next.representative v = v := by
        change blossomRepresentative cycle base (part.representative v) = v
        rw [blossomRepresentative, if_neg unaffected, active.1]
      have newBlock : next.blocks.block v = part.blocks.block v :=
        (part.contract_block cycle base baseIn fixed odd covered v).trans (if_neg unaffected)
      change matchingTopCutAt next v = matchingTopCutAt part v
      simp only [matchingTopCutAt, if_pos newFixed, if_pos active.1, newBlock]
  change LeastSlackEntry _ (readMatchingCandidate newMap s g.slot)
  rw [unchanged]
  exact rows.least g

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionCutMap

/-! matching/MatchingContractionSearchExit.lean -/
section RppSource_MatchingContractionSearchExit
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The forest after contraction retains all surviving tight original parent
witnesses, including edges from a newly absorbed parent to an exterior inner
child. Matched parent links continue to use the exact two live ports. -/
theorem matchingContraction_searchExit {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {a b base : Fin k} {pa pb : Option (Fin k)} {s t : ArithmeticState}
    (old : CompactMatchingSearchForest part forest state.partialMate part.tightBetween)
    (top : CompactTopMatching part) (internal : state.InternalCuts)
    (witnesses : MatchingForestOriginalWitnesses part forest s) (links : MatchingForestLinkMemory part forest s)
    (aOuter : forest.role a = .outer pa) (bOuter : forest.role b = .outer pb) (ancestor : forest.commonAncestor a b = some base)
    (keeps : ∀ v : Fin k, matchingForestWitnessAt t.nm (t.nr 90) v.val = matchingForestWitnessAt s.nm (s.nr 90) v.val)
    (odd : Odd (contractionCycle (forest.traceToRoot a) (forest.traceToRoot b) base).toFinset.card)
    (fixed : ∀ p ∈ (contractionCycle (forest.traceToRoot a) (forest.traceToRoot b) base).toFinset, part.representative p = p) :
    let cycle := (contractionCycle (forest.traceToRoot a) (forest.traceToRoot b) base).toFinset
    let baseIn : base ∈ cycle := by simp [cycle,contractionCycle]
    let pairs := alternatingForest_contractionMates old.valid aOuter bOuter ancestor
    let next := part.contract cycle base baseIn fixed odd (contractionMates_covered pairs)
    let after := forest.contract cycle base
    CompactTopMatching next ∧ (state.registerCut (part.contractCut cycle) (part.contractCut_odd cycle fixed odd)).InternalCuts ∧
      CompactMatchingSearchForest next after state.partialMate next.tightBetween ∧
      MatchingForestOriginalWitnesses next after t ∧ MatchingForestLinkMemory next after t := by
  intro cycle baseIn pairs next after
  let shrink := blossomRepresentative cycle base
  have map (v : Fin k) : next.representative v = shrink (part.representative v) := rfl
  have newValid : after.valid state.partialMate next.tightBetween := by
    apply alternatingForest_contractFromEdge old.valid aOuter bOuter ancestor
    change ∀ x y, part.tightBetween x y → next.tightBetween (shrink x) (shrink y)
    intro x y edge
    obtain ⟨u,v,src,dst,value⟩ := edge
    exact ⟨u,v,(map u).trans (congrArg shrink src),(map v).trans (congrArg shrink dst),by
      change oddCutDualEdgeValue (insert (part.contractCut cycle) state.cuts) state.potential (extendBlossomCutDual state.cuts state.cutDual) s(u,v) = _
      rw [oddCutDualEdgeValue_register_cut]; exact value⟩
  have newTop := top.contract baseIn fixed odd pairs
  have absorbed (v : Fin k) (h : v ∈ cycle ∧ v ≠ base) : after.role v = .unlabelled := by
    simp [after,AlternatingForestState.contract,h]
  have outside (v : Fin k) (alive : after.role v ≠ .unlabelled) : ¬(v ∈ cycle ∧ v ≠ base) :=
    fun h => alive (absorbed v h)
  have retained (v : Fin k) (alive : after.role v ≠ .unlabelled) : shrink v = v := by
    by_cases hv : v ∈ cycle
    · have same : v = base := by by_contra other; exact outside v alive ⟨hv,other⟩
      simp [shrink,blossomRepresentative,hv,same]
    · simp [shrink,blossomRepresentative,hv]
  have getOuter {v : Fin k} {p : Option (Fin k)} (outer : after.role v = .outer p) : forest.role v = .outer p := by
    have live : after.role v ≠ .unlabelled := by simp [outer]
    cases row : forest.role v <;>
      simpa [after,AlternatingForestState.contract,outside v live,row] using outer
  refine ⟨newTop,contractionInternalCuts top internal baseIn fixed odd pairs,⟨newValid,?_,?_⟩,?_,⟨?_,?_⟩⟩
  · intro u v edge separate
    obtain ⟨hu,hv⟩ := newTop.crossing_endpoints edge separate
    rw [hu,hv]
    exact ⟨state.partialMate_some_iff.mpr edge,state.partialMate_some_iff.mpr (Sym2.eq_swap ▸ edge)⟩
  · intro v uncovered
    have oldV := old.exposed v uncovered
    rw [part.exposed_fixed uncovered] at oldV
    have notGone : ¬ (v ∈ cycle ∧ v ≠ base) := fun h => uncovered (contractionMates_covered pairs v h.1 h.2)
    rw [next.exposed_fixed uncovered]
    simp [after,AlternatingForestState.contract,notGone,oldV]
  · intro child parent current
    have childLive : after.role child ≠ .unlabelled := by
      intro idle
      simp [idle,AlternatingForestRole.parent] at current
    have childKept := retained child childLive
    have parentLive : after.role parent ≠ .unlabelled := by
      rcases parent_step_roles newValid current with ⟨_,_,kind,_⟩ | ⟨_,_,kind⟩ <;> simp [kind]
    have oldLink : ∃ q, (forest.role child).parent = some q ∧ shrink q = parent := by
      cases row : forest.role child with
      | unlabelled => simp [after,AlternatingForestState.contract,row,outside child childLive,AlternatingForestRole.parent] at current
      | outer prior =>
        have h : prior = some parent := by simpa [after,AlternatingForestState.contract,row,outside child childLive,AlternatingForestRole.parent] using current
        exact ⟨parent,by simpa [row,AlternatingForestRole.parent] using h,retained parent parentLive⟩
      | inner q =>
        have h : shrink q = parent := by simpa [after,AlternatingForestState.contract,row,outside child childLive,AlternatingForestRole.parent,shrink] using current
        exact ⟨q,by simp [row,AlternatingForestRole.parent],h⟩
    obtain ⟨q,link,qMap⟩ := oldLink
    obtain ⟨u,v,bytes,first,second,edge⟩ := witnesses link
    exact ⟨u,v,(keeps child).trans bytes,(map _).trans ((congrArg shrink first).trans qMap),
      (map _).trans ((congrArg shrink second).trans childKept),by
        change oddCutDualEdgeValue (insert (part.contractCut cycle) state.cuts) state.potential (extendBlossomCutDual state.cuts state.cutDual) s(u,v) = _
        rw [oddCutDualEdgeValue_register_cut]; exact edge⟩
  · intro v different
    by_contra active
    have stay := retained v active
    have nonRep : part.representative v ≠ v := fun h => different ((map _).trans ((congrArg shrink h).trans stay))
    have idle := links.inactive v nonRep
    exact active (by simp [after,AlternatingForestState.contract,outside v active,idle])
  · intro child parent outer
    exact (keeps child).trans (links.matched (getOuter outer))

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionSearchExit

/-! matching/MatchingContractionAllocatedRows.lean -/
section RppSource_MatchingContractionAllocatedRows
namespace VehicleRoutingSurvey.Routing

/-- Decode the new start and count headers, the advanced cursors, old
headers, old arena bytes, and all new records in the exit state of the entire
structural prefix, after the representative/forest tables have changed. -/
theorem MatchingContractionWriterView.allocatedRows {s t : ArithmeticState}
    (observed : MatchingContractionWriterView s t) (safe : MatchingCycleReadSafety (matchingCycleRecordReference s))
    (node : s.nr 74+s.nr 55 ≤ s.nr 77) (parents : s.nr 52+s.nr 55 ≤ s.nr 77) (rep : s.nr 57+s.nr 55 ≤ s.nr 77)
    (headers : s.nr 77+s.nr 76 < s.nr 78) (scratch : s.nr 78+s.nr 76 < s.nr 86)
    (arena : s.nr 89+s.nr 55 ≤ s.nr 68) (sorted : s.nr 86 ≤ s.nr 89)
    (headerPorts : t.nr 77 = s.nr 77 ∧ t.nr 78 = s.nr 78) :
    t.nr 76 = s.nr 76+1 ∧ t.nr 68 = s.nr 68+4*matchingCycleChildCount s ∧
    t.nm (s.nr 74+s.nr 12) = s.nr 76 ∧
    matchingCycleRecordStart t (s.nr 76) = s.nr 68 ∧ t.nm (t.nr 78+s.nr 76) = matchingCycleChildCount s ∧
    (∀ id < s.nr 76, matchingCycleRecordStart t id = matchingCycleRecordStart s id ∧
      t.nm (t.nr 78+id) = s.nm (s.nr 78+id)) ∧
    (∀ addr, s.nr 89+s.nr 55 ≤ addr → addr < s.nr 68 → t.nm addr = s.nm addr) ∧
    ∀ i < matchingCycleChildCount s, matchingCycleChildAt t.nm (s.nr 68+4*i) = matchingContractionWrittenChild s i := by
  obtain ⟨u,w,n,entry,live,one,nm,regs,run,cursor,publish,atBase,_,frame⟩ := observed.allocation
  have port (j : ℕ) (away : j ∉ [0,6,7,10,11,23,81,82] := by decide) : u.nr j = s.nr j := regs _ away
  have count : matchingCycleChildCount u = matchingCycleChildCount s := by simp only [matchingCycleChildCount,port 13,port 14]
  have ref : (matchingCycleRecordReference u).nm = (matchingCycleRecordReference s).nm := by
    simp only [matchingCycleRecordReference,startMatchingCycleNat,port 77,port 78,port 76,port 68,count,nm]
  have reads : MatchingCycleReadSafety (matchingCycleRecordReference u) := by
    obtain ⟨left,right,nodes,edges,leftValid,rightValid,base⟩ := safe
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [matchingCycleRecordReference,port 83,port 13,port 68] using left
    · simpa only [matchingCycleRecordReference,port 84,port 14,port 68] using right
    · simpa only [matchingCycleRecordReference,port 74,port 55,port 68] using nodes
    · simpa only [matchingCycleRecordReference,port 90,port 55,port 68] using edges
    · intro i hi
      change (matchingCycleRecordReference u).nm (u.nr 83+i) < u.nr 55
      rw [ref,port 83,port 55]
      exact leftValid i (by simpa only [matchingCycleRecordReference,port 13] using hi)
    · intro i hi
      change (matchingCycleRecordReference u).nm (u.nr 84+i) < u.nr 55
      rw [ref,port 84,port 55]
      exact rightValid i (by simpa only [matchingCycleRecordReference,port 14] using hi)
    · simpa only [matchingCycleRecordReference,port 12,port 55] using base
  obtain ⟨start,arity,table⟩ := matchingContractionWrittenRows run entry live one
    (by simpa only [port 77,port 76,port 78] using headers) (by rw [port 78,port 76,port 68]; omega) reads
  obtain ⟨z,_,_,writer,_,endAt,earlier,_,outputs⟩ := writeMatchingContractionCycle_bound u entry live one
  have same := (writer.same_exit run).2
  subst z
  have w77 := (outputs 77 (by decide)).trans (port 77)
  have w78 := (outputs 78 (by decide)).trans (port 78)
  have keep (addr : ℕ) (lo : s.nr 77 ≤ addr) (whereAt : addr < s.nr 86 ∨ s.nr 89+s.nr 55 ≤ addr) : t.nm addr = w.nm addr := by
    apply frame <;> simp only [port 74,port 55,port 52,port 57,port 86,port 89] <;> omega
  have old (addr : ℕ) (lo : s.nr 77 ≤ addr) (whereAt : addr < s.nr 86 ∨ s.nr 89+s.nr 55 ≤ addr)
      (past : addr < s.nr 68) (a : addr ≠ s.nr 77+s.nr 76) (b : addr ≠ s.nr 78+s.nr 76) : t.nm addr = s.nm addr := by
    rw [keep addr lo whereAt,earlier _ (by rwa [port 68])]
    simp only [startMatchingCycleNat,port 77,port 78,port 76,Function.update_of_ne a,Function.update_of_ne b,nm]
  refine ⟨publish.trans (congrArg (·+1) (port 76)),cursor.trans (by simpa only [port 68,count] using endAt),
    by simpa only [port 74,port 12,port 76] using atBase,?_,?_,?_,?_,?_⟩
  · change t.nm (t.nr 77+s.nr 76) = _
    rw [headerPorts.1,keep _ (by omega) (.inl (by omega))]
    simpa only [matchingCycleRecordStart,port 76,port 68,w77] using start
  · rw [headerPorts.2,keep _ (by omega) (.inl scratch)]
    simpa only [w78,port 76,count] using arity
  · intro id hi
    simp only [matchingCycleRecordStart,headerPorts.1,headerPorts.2]
    constructor <;> apply old <;> omega
  · intro addr lo hi
    apply old <;> omega
  · intro i hi
    have atRow := table i (count.symm ▸ hi)
    rw [start,port 68] at atRow
    have bytes (j : ℕ) : t.nm (s.nr 68+4*i+j) = w.nm (s.nr 68+4*i+j) := keep _ (by omega) (.inr (by omega))
    have first : t.nm (s.nr 68+4*i) = w.nm (s.nr 68+4*i) := by simpa using bytes 0
    have record : matchingCycleChildAt t.nm (s.nr 68+4*i) = matchingCycleChildAt w.nm (s.nr 68+4*i) := by
      simp only [matchingCycleChildAt,first,bytes 1,bytes 2,bytes 3]
    rw [record,atRow]
    have head : startMatchingCycleNat u = startMatchingCycleNat s := ref
    simp only [matchingContractionWrittenChild,leftCycleRecordAt,commonCycleRecord,rightCycleRecordAt,leftCycleRepresentativeAt,
      rightCycleRepresentativeAt,matchingCycleRecordReference,head,port 12,port 13,port 14,port 74,port 83,port 84,
      port 90,port 92,port 93] <;> rfl

theorem MatchingContractionWriterView.recordOrder {s t : ArithmeticState}
    (observed : MatchingContractionWriterView s t) (safe : MatchingCycleReadSafety (matchingCycleRecordReference s))
    (node : s.nr 74+s.nr 55 ≤ s.nr 77) (parents : s.nr 52+s.nr 55 ≤ s.nr 77) (rep : s.nr 57+s.nr 55 ≤ s.nr 77)
    (headers : s.nr 77+s.nr 76 < s.nr 78) (scratch : s.nr 78+s.nr 76 < s.nr 86)
    (arena : s.nr 89+s.nr 55 ≤ s.nr 68) (sorted : s.nr 86 ≤ s.nr 89)
    (headerPorts : t.nr 77 = s.nr 77 ∧ t.nr 78 = s.nr 78) (rebase : matchingRebaseScratchEnd t = matchingRebaseScratchEnd s)
    (order : MatchingCycleRecordOrder s) : MatchingCycleRecordOrder t := by
  obtain ⟨next,endAt,_,start,arity,prior,_,_⟩ := observed.allocatedRows safe node parents rep headers scratch arena sorted headerPorts
  apply order.append rebase next (by rw [endAt]; omega) (fun i _ earlier => (prior i earlier).1) _ start
  · rw [matchingCycleRecordEnd,start,arity,endAt]
  · intro i _ earlier
    simp only [matchingCycleRecordEnd,(prior i earlier).1,(prior i earlier).2]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionAllocatedRows

/-! matching/MatchingContractionArchiveFrame.lean -/
section RppSource_MatchingContractionArchiveFrame
namespace VehicleRoutingSurvey.Routing





theorem MatchingContractionWriterView.oldArchive {s t : ArithmeticState}
    (observed : MatchingContractionWriterView s t) (safe : MatchingCycleReadSafety (matchingCycleRecordReference s))
    (node : s.nr 74+s.nr 55 ≤ s.nr 77) (parents : s.nr 52+s.nr 55 ≤ s.nr 77) (rep : s.nr 57+s.nr 55 ≤ s.nr 77)
    (headers : s.nr 77+s.nr 76 < s.nr 78) (scratch : s.nr 78+s.nr 76 < s.nr 86)
    (arena : s.nr 89+s.nr 55 ≤ matchingRebaseScratchEnd s) (sorted : s.nr 86 ≤ s.nr 89)
    (headerPorts : t.nr 77 = s.nr 77 ∧ t.nr 78 = s.nr 78) (order : MatchingCycleRecordOrder s) :
    ∀ a, matchingContractionOldArchive s a → t.nm a = s.nm a := by
  obtain ⟨_,_,_,_,_,prior,heap,_⟩ := observed.allocatedRows safe node parents rep headers scratch
    (arena.trans order.scratch) sorted headerPorts
  rintro a (⟨n,h,rfl | rfl⟩ | ⟨lo,hi⟩)
  · simpa only [matchingCycleRecordStart,headerPorts.1] using (prior n h).1
  · simpa only [headerPorts.2] using (prior n h).2
  · exact heap a (arena.trans lo) hi



end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionArchiveFrame

/-! matching/MatchingContractionWitnessFrame.lean -/
section RppSource_MatchingContractionWitnessFrame
namespace VehicleRoutingSurvey.Routing

theorem MatchingContractionPrefixView.witnesses {k : ℕ} {s t : ArithmeticState}
    (view : MatchingContractionPrefixView s t) (dimension : s.nr 55 = k) (pointer : t.nr 90 = s.nr 90)
    (rep : s.nr 57+k ≤ s.nr 90) (parent : s.nr 52+k ≤ s.nr 90) (nodes : s.nr 74+k ≤ s.nr 90)
    (start : s.nr 90+2*k ≤ s.nr 77 ∨ s.nr 77+s.nr 76 < s.nr 90)
    (count : s.nr 90+2*k ≤ s.nr 78 ∨ s.nr 78+s.nr 76 < s.nr 90)
    (scratch : s.nr 90+2*k ≤ s.nr 86) (v : Fin k) :
    matchingForestWitnessAt t.nm (t.nr 90) v.val = matchingForestWitnessAt s.nm (s.nr 90) v.val := by
  have lower := v.isLt
  have first : t.nm (forestWitnessAddress (s.nr 90) v.val) = s.nm (forestWitnessAddress (s.nr 90) v.val) := by
    apply view.cacheNatural <;> unfold forestWitnessAddress <;> omega
  have second : t.nm (forestWitnessAddress (s.nr 90) v.val+1) = s.nm (forestWitnessAddress (s.nr 90) v.val+1) := by
    apply view.cacheNatural <;> unfold forestWitnessAddress <;> omega
  rw [pointer,matchingForestWitnessAt,first,second]
  rfl

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionWitnessFrame

/-! matching/MatchingDispatchContraction.lean -/
section RppSource_MatchingDispatchContraction
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem MatchingDispatchState.contractArm
    {k i : ℕ} {cost : Fin k → Fin k → ℝ} {original s ready : ArithmeticState}
    (before : MatchingDispatchState cost original i s) (searching : i < k/2)
    (symmetric : ∀ u v, cost u v = cost v u) (entry : s.pc = 0) (running : s.halted = false)
    {a b base : Fin k} {pa pb : Option (Fin k)}
    (oldA : before.forest.role (before.part.representative a) = .outer pa)
    (oldB : before.forest.role (before.part.representative b) = .outer pb)
    (separate : before.part.blocks.block a ≠ before.part.blocks.block b)
    (selected : before.selected.event = .edge s(a,b)) (endpoints : (s.nr 92,s.nr 93) = (a.val,b.val))
    (ancestor : before.forest.commonAncestor (before.part.representative a) (before.part.representative b) = some base)
    (traces : MatchingResolvedOuter before.forest (before.part.representative a) (before.part.representative b)
      (s.nr 83) ready s) :
    ∃ t ticks charge, BlockRuns matchingContractionHandlerBlock ticks s t ∧
      t.halted = false ∧ t.nr 33 = s.nr 33 ∧
      Nonempty (MatchingPreparedStage cost original i (matchingStageSnapshot t)) ∧
      MatchingStageTransition (matchingStageCountsFromRAM k s (s.nr 39)) charge
        (matchingStageCountsFromRAM k (matchingStageSnapshot t) ((matchingStageSnapshot t).nr 39)) ∧
      ticks + (34*k+61) ≤ 1024*(k+1)*charge := by
  have stamp := before.budget.cutoff_le_cursor
  let delta : DualBound (MatchingDualEvent k) := ⟨before.selected.event, s.rr 1⟩
  let state := before.state.advanceSearch before.part before.search before.positive before.internal delta before.selected.adjustment
  let part := before.part.advanceSearch before.search before.positive before.internal delta before.selected.adjustment
  let snap := matchingContractionDualSnapshot s
  let forest := before.forest
  obtain ⟨advanced, nodes, trees⟩ :=
    before.selected.contractionDualSnapshot before.search before.internal entry running before.one before.storage
  have top : CompactTopMatching part := ⟨before.top.interior, before.top.matchedBase⟩
  let liveCycles := before.cycles.advanceDual before.search before.positive before.internal delta before.selected.adjustment
    advanced.registry nodes trees rfl (fun _ _ => rfl)
  let leftPort := before.part.representative a
  let rightPort := before.part.representative b
  have distinct : leftPort ≠ rightPort := fun eq => separate (before.part.same_block.mp eq)
  have tight : oddCutDualEdgeValue state.cuts state.potential state.cutDual s(a,b) =
      edgeCost cost s(a,b) := by
    have step := before.selected.adjustment.2.2.2
    rw [selected] at step
    exact step.2.2
  have closing : part.tightBetween leftPort rightPort := ⟨a,b,rfl,rfl,tight⟩
  letI swap : Std.Symm part.tightBetween :=
    ⟨fun _ _ ⟨u,v,first,second,h⟩ => ⟨v,u,second,first,Sym2.eq_swap ▸ h⟩⟩
  obtain ⟨atBase, cycleSize, leftValid, rightValid, leftAt, rightAt⟩ :=
    traces.contractionTrace (tight := fun e => e ∈ Sym2.fromRel swap) advanced.search.valid distinct oldA oldB
      (Std.Symm.symm (r := part.tightBetween) leftPort rightPort closing) ancestor
  let left := traceBefore base (forest.traceToRoot leftPort)
  let right := traceBefore base (forest.traceToRoot rightPort)
  let ordered := contractionCycleOrder left right base
  let cycle := ordered.toFinset
  obtain ⟨unique, many, odd, fixed, baseOuter, labelled, two⟩ :=
    advanced.search.contractionCycleFacts advanced.links distinct oldA oldB closing ancestor
  have card : cycle.card = ordered.length :=
    List.toFinset_card_of_nodup (show ordered.Nodup from unique)
  have oddCard : Odd cycle.card := card ▸ odd
  have longCycle : 3 ≤ ordered.length := many
  have manyCard : 1 < cycle.card := card ▸ (by omega : 1 < ordered.length)
  have baseIn : base ∈ cycle := by simp [cycle, ordered, contractionCycleOrder]
  have sameCycle : cycle = (base :: (left ++ right)).toFinset := by
    ext v
    exact (List.mem_toFinset.trans (contractionCycleOrder_perm left right base).mem_iff).trans List.mem_toFinset.symm
  have mates := alternatingForest_contractionMates advanced.search.valid oldA oldB ancestor
  have covered : ∀ p ∈ cycle, p ≠ base → p ∈ state.covered := contractionMates_covered mates
  let next := part.contract cycle base baseIn fixed oddCard covered
  let after := forest.contract cycle base
  let absorbed := contractionTypedOuterRows forest base left right
  let fresh := contractionTypedFreshOriginals forest part.representative base left right
  let inherited := state.cuts.filter fun B => advanced.dual.node B < s.nr 39
  have baseCode : alternatingRoleCode (forest.role base) = 1 := by
    obtain ⟨p,h⟩ := baseOuter
    simp [forest,h,alternatingRoleCode]
  have transition :
      MatchingStageTransition (matchingPartitionCounts part.blocks (part.outerBlock forest before.positive) inherited)
        (1+fresh.length+absorbed.length)
        (matchingPartitionCounts next.blocks (next.outerBlock after before.positive) inherited) := by
    have nodup : (base :: (left ++ right)).Nodup := (contractionCycleOrder_perm left right base).nodup unique
    have h := contractionTypedCredit part forest before.positive left right base nodup baseCode labelled inherited
      (sameCycle ▸ fixed) (sameCycle ▸ oddCard) (sameCycle ▸ covered) (sameCycle ▸ two)
    have same : ∀ C (member : base ∈ C) (fixed : ∀ p ∈ C, part.representative p = p) (odd : Odd C.card)
        (covered : ∀ p ∈ C, p ≠ base → p ∈ state.covered), cycle = C →
        MatchingStageTransition (matchingPartitionCounts part.blocks (part.outerBlock forest before.positive) inherited)
          (1+fresh.length+absorbed.length)
          (matchingPartitionCounts (part.contract C base member fixed odd covered).blocks
            ((part.contract C base member fixed odd covered).outerBlock (forest.contract C base) before.positive) inherited) →
        MatchingStageTransition (matchingPartitionCounts part.blocks (part.outerBlock forest before.positive) inherited)
          (1+fresh.length+absorbed.length)
          (matchingPartitionCounts next.blocks (next.outerBlock after before.positive) inherited) := by
      intro C member f o c eq H
      subst C
      exact H
    exact same _ (by simp) _ _ _ sameCycle h
  have counts : matchingStageCountsFromRAM k s (s.nr 39) =
      matchingPartitionCounts part.blocks (part.outerBlock forest before.positive) inherited := by
    rw [matchingStageCountsFromRAM_eq before.selected.dual before.positive _
      before.selected.registry.trees before.selected.registry.unique before.selected.registry.keys]
    change _ = matchingPartitionCounts part.blocks (part.outerBlock forest before.positive)
      (state.cuts.filter fun B => advanced.dual.node B < s.nr 39)
    rw [nodes]
    rfl
  have credit : 0 < (matchingStageCountsFromRAM k s (s.nr 39)).credit := by
    rw [counts]
    have spend := transition.charge_le
    omega
  have capacity := before.budget.can_allocate searching credit
  have reps (j : ℕ) (inside : j < k) : originalTopRepresentative s j < k := by
    change s.nm (s.nr 57+j) < k
    rw [show s.nm (s.nr 57+j) = (part.representative ⟨j,inside⟩).val from advanced.dual.reps ⟨j,inside⟩]
    exact (part.representative ⟨j,inside⟩).isLt
  have layout := before.storage.contractionLayout before.order capacity advanced.reads.effectiveBefore
    cycleSize (atBase.symm ▸ base.isLt) leftValid rightValid reps
  have sSize := before.storage.warm.size
  have parentEnd : s.nr 52+s.nr 55 ≤ s.nr 86 := by
    have a := before.storage.warm.parents
    have b := before.storage.warm.representativesAfter
    have c := before.storage.warm.candidatesAfter
    have d := before.storage.warm.pairsAfter
    have e := before.storage.nodes
    have f := before.storage.starts
    have g := before.storage.lengths
    have h := before.storage.traceLeft
    have j := before.storage.traceRight
    have m := before.storage.traceMarks
    have w := before.storage.witnesses
    have r := before.storage.records
    omega
  have nodeEnd : s.nr 74+s.nr 55 ≤ s.nr 86 := by
    have a := before.storage.starts
    have b := before.storage.lengths
    have c := before.storage.traceLeft
    have d := before.storage.traceRight
    have e := before.storage.traceMarks
    have f := before.storage.witnesses
    have h := before.storage.records
    omega
  obtain ⟨u, steps, limit, run, live, _, clock, natural, real, regs, values, see⟩ :=
    matchingContractionStructure_spec s layout entry running before.one
  let headState := {u with pc := 0}
  have view := (see parentEnd nodeEnd).dualSnapshot
  have port (r : ℕ) (safe : r ∉ ([0,6,7,10,11,15,16,17,18,19,23,68,76,81,82,87,99] : List ℕ) := by decide) :
      headState.nr r = snap.nr r := regs r safe
  have ports (r : ℕ) (used : r ∈ matchingRefreshTableRegisters) : headState.nr r = snap.nr r :=
    port r (by simp [matchingRefreshTableRegisters] at used; simp; omega)
  have snapStorage := before.storage.keeps (t := snap) (fun _ _ => rfl)
  have cacheLocation := snapStorage.contractionCacheLocation advanced.reads.effectiveBefore
  have keyLayouts := advanced.reads.layout
  have repAt (v : Fin k) : originalTopRepresentative snap v.val = (part.representative v).val :=
    advanced.dual.reps v
  obtain ⟨countAbsorbed, countFresh, absorbedWords, freshWords⟩ :=
    view.encodedLists forest part.representative base left right sSize atBase leftAt rightAt advanced.dual.roles repAt
  have parentsBefore : snap.nr 52+k ≤ snap.nr 57 := by
    have a := snapStorage.warm.parents
    have b := snapStorage.warm.representativesAfter
    omega
  have repsBefore : snap.nr 57+k ≤ snap.nr 74 := by
    have a := snapStorage.warm.candidatesAfter
    have b := snapStorage.warm.pairsAfter
    have c := snapStorage.nodes
    omega
  have headerOrder : snap.nr 77 ≤ snap.nr 78 := by
    rw [snapStorage.lengths]
    exact Nat.le_add_right _ _
  have topology := view.typedTopology part.representative base left right sSize atBase leftAt rightAt repAt
    parentsBefore repsBefore snapStorage.starts.ge
    (snapStorage.starts.ge.trans headerOrder) (port 57) (port 74) (port 89)
  have representatives : ∀ v : Fin k, headState.nm (headState.nr 57+v.val) = (next.representative v).val := by
    intro v
    change _ = (blossomRepresentative cycle base (part.representative v)).val
    rw [sameCycle]
    exact topology.1 v
  have topNodes (v : Fin k) : blossomNodeAt headState v.val = if v = base then snap.nr 76
      else if v ∈ cycle then 0 else blossomNodeAt snap v.val := by rw [sameCycle]; exact topology.2.1 v
  have marked (v : Fin k) : headState.nm (headState.nr 89+v.val) ≠ 0 ↔ v ∈ cycle := by
    rw [sameCycle]
    exact topology.2.2 v
  have mask (v : Fin k) : snap.nr 89+v.val ∈ matchingContractionMaskAddresses snap ↔ v ∈ cycle := by
    rw [sameCycle, List.mem_toFinset]
    exact matchingContractionMaskAddresses_mem snap left right base v atBase leftAt rightAt
  have roles : AlternatingForestMemory after (headState.nr 51) headState.nm := by
    rw [port 51]
    have endOfForest : snap.nr 53+k ≤ snap.nr 57 := by
      have a := snapStorage.warm.depths
      have b := snapStorage.warm.representativesAfter
      omega
    exact view.forest sSize snapStorage.warm.parents snapStorage.warm.depths endOfForest repsBefore
      forest base cycle atBase advanced.dual.roles mask
  have tables := before.selected.dual.contractionAdvanceTables before.positive (port 62) (port 75)
    before.selected.registry.allocated values
  have lowReal (a : ℕ) (low : a < snap.nr 62) : headState.rm a = snap.rm a :=
    (real a low).trans (matchingEventDualMemory_keeps_prefix s (s.nr 62) a low le_rfl layout.nodeDualAfter).symm
  have offsetsBefore : snap.nr 21+k ≤ snap.nr 51 :=
    snapStorage.warm.offsetsBefore.trans ((Nat.le_add_right _ k).trans snapStorage.warm.matesBefore)
  have reads := advanced.reads.contractionPrefix (t := headState) ports offsetsBefore
    snapStorage.metricBelowInput natural lowReal representatives (fun v => (roles v).1) tables.1
  have caches := view.cacheReads keyLayouts cacheLocation (fun r used => port r (by simp at used ⊢; omega))
    (matchingTopCutAt before.part) advanced.valid
  have buckets : MatchingSearchOuterBuckets headState part.representative (fun v => alternatingRoleCode (forest.role v))
      cost (effectiveVertexPotential state.cuts state.potential state.cutDual) := by
    have pairIndex (a b : Fin k) : k*a.val+b.val < k*k := by
      have h := Nat.mul_le_mul_left k (Nat.succ_le_of_lt a.isLt)
      rw [Nat.mul_succ] at h
      have j := b.isLt
      omega
    refine ⟨fun j h => (caches.2 j h).1.symm ▸ advanced.pairs.valid j h, ?_, ?_⟩
    · intro a b diff first last
      have same : readMatchingPairBucket (k := k) headState (k*a.val+b.val) =
          readMatchingPairBucket (k := k) snap (k*a.val+b.val) := (caches.2 _ (pairIndex a b)).2
      rw [show headState.rr 15 = snap.rr 15 from clock, same]
      exact advanced.pairs.least a b diff first last
    · intro a b off
      exact (caches.2 _ (pairIndex a b)).2.trans (advanced.pairs.inactive a b off)
  classical
  let oldRole := fun v => alternatingRoleCode (forest.role v)
  let newRole := fun v => alternatingRoleCode (after.role v)
  let effective := effectiveVertexPotential state.cuts state.potential state.cutDual
  have oldOuterFixed (v : Fin k) (outer : oldRole v = 1) : part.representative v = v := by
    by_contra different
    have off := advanced.links.inactive v different
    simp [oldRole, forest, off, alternatingRoleCode] at outer
  have shape : MatchingContractionPairGeometry part.representative next.representative
      oldRole newRole base absorbed fresh := by
    change MatchingContractionPairGeometry part.representative
      (fun v => blossomRepresentative cycle base (part.representative v)) oldRole
      (fun v => alternatingRoleCode ((forest.contract cycle base).role v)) base absorbed fresh
    rw [sameCycle]
    exact contractionPairGeometryFromEdge forest part.representative advanced.search.valid
      part.representative_idem oldOuterFixed oldA oldB ancestor
  have changes (v : Fin k) : newRole (next.representative v) =
      if v ∈ fresh then 1 else oldRole (part.representative v) := by
    change alternatingRoleCode ((forest.contract cycle base).role (blossomRepresentative cycle base (part.representative v))) = _
    rw [sameCycle]
    exact contractionTypedOriginalRole forest part.representative base left right baseCode labelled v
  have keptValid (j : ℕ) (within : j < headState.nr 61) :
      MatchingCandidateRowValid (matchingTopCutAt part) headState j :=
    (caches.1 j (port 61 ▸ within)).1
  have keptLeast (g : MatchingCandidateGroup k) :
      LeastSlackEntry (contractionSearchEntries part forest before.positive g)
        (readMatchingCandidate (matchingTopCutAt part) headState g.slot) := by
    have matchRow : readMatchingCandidate (matchingTopCutAt part) headState g.slot =
        readMatchingCandidate (matchingTopCutAt part) snap g.slot :=
      (caches.1 _ (keyLayouts.rows.symm ▸ g.slot_lt)).2
    rw [matchRow]
    exact advanced.least g
  have pairLimit : headState.nr 65+2*(k*k) ≤ headState.nr 86 := by
    rw [port 65, port 86]
    exact cacheLocation.scratchAfter
  have promotionLimit : headState.nr 86 ≤ headState.nr 88 := by
    rw [port 86, port 88]
    have promoted : snap.nr 88 = snap.nr 86+k := snapStorage.promotion
    omega
  have markLimit : headState.nr 58+headState.nr 61 ≤ headState.nr 89 := by
    rw [port 58, port 61, port 89]
    have ids : snap.nr 58+snap.nr 61 ≤ snap.nr 54 := keyLayouts.idsBefore
    have records : snap.nr 54+2*snap.nr 61 ≤ snap.nr 65 := keyLayouts.recordsBefore
    have scratch : snap.nr 65+2*(k*k) ≤ snap.nr 86 := cacheLocation.scratchAfter
    have promotion : snap.nr 88 = snap.nr 86+k := snapStorage.promotion
    have mask : snap.nr 89 = snap.nr 88+k := snapStorage.mask
    omega
  obtain ⟨t, tailTicks, _, tail, tLive, zero, frame, _, tailPorts, rows, refreshed, pairs⟩ :=
    matchingContractionSuffix_searchRows part forest before.positive symmetric advanced.registry.nested
      cycle base baseIn fixed oddCard covered baseOuter headState absorbed fresh (matchingTopCutAt part)
      rfl live ((port 9).trans before.one) ((port 12).trans atBase) countAbsorbed countFresh absorbedWords freshWords
      marked pairLimit (pairLimit.trans promotionLimit) markLimit keptValid keptLeast shape changes reads buckets
  let result := relocateState matchingContractionStructure.length t
  have whole : BlockRuns matchingContractionHandlerBlock (steps+tailTicks) s result := run.append tail
  let final := matchingStageSnapshot result
  have finalPort (r : ℕ) (kept : r ∉ ([0,1,2,3,4,5,6,7,8,10,11,14,15,16,17,18,19,23,24,25,26] : List ℕ) := by decide)
      (safe : r ≠ 30 := by decide) : final.nr r = headState.nr r :=
    (Function.update_of_ne safe _ _).trans (tailPorts r kept)
  have fixedPort (r : ℕ)
      (p : r ∉ ([0,1,2,3,4,5,6,7,8,10,11,14,15,16,17,18,19,23,24,25,26,30,68,76,81,82,87,99] : List ℕ) := by decide) :
      final.nr r = snap.nr r := (finalPort r (by simp at p ⊢; omega) (by simp at p; omega)).trans
    (port r (by simp at p ⊢; omega))
  have finalNatural (a : ℕ) (outside : a < headState.nr 58 ∨ headState.nr 65+2*(k*k) ≤ a) :
      final.nm a = headState.nm a := frame.natural a outside
  have finalReal (a : ℕ) (outside : a < headState.nr 59 ∨ headState.nr 66+k*k ≤ a) :
      final.rm a = headState.rm a := frame.real a outside
  have finalReads := refreshed.keeps (t := final) ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    (fun r h => Function.update_of_ne (by simp [matchingRefreshTableRegisters] at h; omega : r ≠ 30) _ _)
  have finalRowsOld : MatchingSearchRows next after before.positive (matchingTopCutAt part) final :=
    ⟨finalReads.layout, rows.count, rows.ids, rows.slacks, rows.rates, rows.valid, rows.least⟩
  have finalRows := MatchingSearchRows.contractionCutMap part forest before.positive cycle base baseIn fixed oddCard covered baseOuter
    final finalRowsOld
  have finalPairs : MatchingSearchOuterBuckets final next.representative newRole cost effective :=
    ⟨pairs.valid,pairs.least,pairs.inactive⟩
  have snapOrder : MatchingCycleRecordOrder snap := before.order.transport (t := snap) rfl rfl rfl
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  obtain ⟨readReference, refLeft, refRight, refWitness, refNodes⟩ :=
    snapStorage.contractionReference snapOrder capacity cycleSize (atBase.symm ▸ base.isLt) leftValid rightValid
  let reference := matchingCycleRecordReference snap
  have leftLength : snap.nr 13 = left.length := by simpa using! congrArg List.length leftAt
  have rightLength : snap.nr 14 = right.length := by simpa using! congrArg List.length rightAt
  have traceWord (n : ℕ) (words : ℕ → ℕ) (leg : List (Fin k))
      (encoded : (List.range n).map words = leg.map Fin.val) (j : ℕ) (inside : j < leg.length) : words j = leg[j].val := by
    have length : n = leg.length := by simpa using congrArg List.length encoded
    have atIndex := congrArg (fun row : List ℕ => row[j]?) encoded
    simpa only [List.getElem?_map, List.getElem?_range (length ▸ inside), List.getElem?_eq_getElem inside,
      Option.map_some, Option.some.injEq] using atIndex
  have leftWord (j : ℕ) (inside : j < left.length) :
      leftCycleRepresentativeAt reference j = left[j].val := (refLeft j (leftLength.symm ▸ inside)).trans
    (traceWord _ (fun j => snap.nm (snap.nr 83+j)) left leftAt j inside)
  have rightWord (j : ℕ) (inside : j < right.length) :
      rightCycleRepresentativeAt reference j = right[j].val := (refRight j (rightLength.symm ▸ inside)).trans
    (traceWord _ (fun j => snap.nm (snap.nr 84+j)) right rightAt j inside)
  obtain ⟨leftBase, xs, ys, atRightBase, _⟩ := firstSharedAncestor_eq_some_iff.mp ancestor
  have rightBase : base ∈ forest.traceToRoot rightPort := atRightBase.symm ▸ List.mem_append_right xs (by simp)
  obtain ⟨leftHead, leftLinks⟩ := contractionLeg_traced advanced.search.valid (by simp [oldA]) leftBase
  obtain ⟨rightHead, rightLinks⟩ := contractionLeg_traced advanced.search.valid (by simp [forest, rightPort, oldB]) rightBase
  have closingWords : ContractionCycleEdgeWords part (contractionLegPoint right base 0 (Nat.zero_le _))
      (contractionLegPoint left base 0 (Nat.zero_le _)) (snap.nr 93,snap.nr 92) := by
    rw [leftHead, rightHead, show snap.nr 92 = a.val from congrArg Prod.fst endpoints,
      show snap.nr 93 = b.val from congrArg Prod.snd endpoints]
    exact contractionClosingEdgeWords advanced.search.valid rfl rfl oldB oldA (Sym2.eq_swap ▸ tight)
  have witnesses : MatchingForestOriginalWitnesses part forest reference := by
    intro child parent link
    obtain ⟨a,b,word,pa,pb,tight⟩ := advanced.witnesses link
    exact ⟨a,b,(refWitness child).trans word,pa,pb,tight⟩
  obtain ⟨rowCount, rowGeometry⟩ := matchingContractionWrittenChild_geometry advanced.search.valid left right base
    leftLength rightLength atBase leftWord rightWord leftLinks rightLinks witnesses
    (advanced.links.advance rfl refWitness) closingWords
  have nodeBound : snap.nr 74+snap.nr 55 ≤ snap.nr 77 := by rw [show snap.nr 55 = k from sSize]; exact snapStorage.starts.ge
  have parentBound : snap.nr 52+snap.nr 55 ≤ snap.nr 77 := by
    rw [show snap.nr 55 = k from sSize]
    exact parentsBefore.trans ((Nat.le_add_right _ k).trans (repsBefore.trans ((Nat.le_add_right _ k).trans snapStorage.starts.ge)))
  have repBound : snap.nr 57+snap.nr 55 ≤ snap.nr 77 := by
    rw [show snap.nr 55 = k from sSize]
    exact repsBefore.trans ((Nat.le_add_right _ k).trans snapStorage.starts.ge)
  have firstHeader : snap.nr 77+snap.nr 76 < snap.nr 78 := by
    rw [show snap.nr 78 = snap.nr 77+matchingBlossomCapacity k from snapStorage.lengths]
    exact Nat.add_lt_add_left capacity _
  have beforeWitness : snap.nr 78+snap.nr 76 < snap.nr 90 := by
    have start : snap.nr 83 = snap.nr 78+matchingBlossomCapacity k := snapStorage.traceLeft
    have r : snap.nr 84 = snap.nr 83+k := snapStorage.traceRight
    have m : snap.nr 85 = snap.nr 84+k := snapStorage.traceMarks
    have e : snap.nr 90 = snap.nr 85+k := snapStorage.witnesses
    have fits : snap.nr 76 < matchingBlossomCapacity k := capacity
    omega
  have beforeWork : snap.nr 90+2*k ≤ snap.nr 86 := snapStorage.records.ge
  have beforeMask : snap.nr 86 ≤ snap.nr 89 := by
    have a : snap.nr 88 = snap.nr 86+k := snapStorage.promotion
    have b : snap.nr 89 = snap.nr 88+k := snapStorage.mask
    omega
  have beforeArchive : snap.nr 89+snap.nr 55 ≤ matchingRebaseScratchEnd snap := by
    have a : snap.nr 79 = snap.nr 89+k := snapStorage.memberMap
    have b : snap.nr 80 = snap.nr 79+k := snapStorage.memberStack
    unfold matchingRebaseScratchEnd
    omega
  have actualHeaders : u.nr 77 = snap.nr 77 ∧ u.nr 78 = snap.nr 78 := ⟨port 77,port 78⟩
  have clearHeaders : snap.nr 78+snap.nr 76 < snap.nr 86 := beforeWitness.trans_le (by omega)
  obtain ⟨allocated, _, _, rowStart, headerCount, _, _, table⟩ := view.writer.allocatedRows readReference
    nodeBound parentBound repBound firstHeader clearHeaders (beforeArchive.trans snapOrder.scratch) beforeMask actualHeaders
  have oldArchive := view.writer.oldArchive readReference nodeBound parentBound repBound firstHeader clearHeaders
    beforeArchive beforeMask actualHeaders snapOrder
  have afterOrder := view.writer.recordOrder readReference nodeBound parentBound repBound firstHeader clearHeaders
    (beforeArchive.trans snapOrder.scratch) beforeMask actualHeaders
    (by simp only [matchingRebaseScratchEnd, (show u.nr 80 = snap.nr 80 from port 80), (show u.nr 55 = snap.nr 55 from port 55)] <;> rfl)
    snapOrder
  have floor (a : ℕ) (high : snap.nr 74 ≤ a) : headState.nr 65+2*(k*k) ≤ a := by
    rw [port 65,← show snap.nr 74 = snap.nr 65+2*(k*k) from snapStorage.nodes]
    exact high
  have highRead (a : ℕ) (high : snap.nr 74 ≤ a) : final.nm a = u.nm a :=
    finalNatural a (.inr (floor a high))
  have firstBase : snap.nr 74 ≤ snap.nr 77 := (Nat.le_add_right _ _).trans nodeBound
  have secondBase : snap.nr 74 ≤ snap.nr 78 := firstBase.trans headerOrder
  have arenaFloor : snap.nr 74 ≤ matchingRebaseScratchEnd snap := by
    have e : snap.nr 89+snap.nr 55 ≤ matchingRebaseScratchEnd snap := beforeArchive
    have w : snap.nr 90+2*k ≤ snap.nr 86 := beforeWork
    have b : snap.nr 86 ≤ snap.nr 89 := beforeMask
    have h : snap.nr 78+snap.nr 76 < snap.nr 90 := beforeWitness
    omega
  have stableArchive (a : ℕ) (there : matchingContractionOldArchive snap a) : final.nm a = snap.nm a := by
    have high : snap.nr 74 ≤ a := by
      rcases there with ⟨id, _, rfl | rfl⟩ | ⟨lo, _⟩
      · exact firstBase.trans (Nat.le_add_right _ _)
      · exact secondBase.trans (Nat.le_add_right _ _)
      · exact arenaFloor.trans lo
    exact (highRead a high).trans (oldArchive a there)
  have finalTop (v : Fin k) : blossomNodeAt final v.val =
      if v = base then snap.nr 76 else if v ∈ cycle then 0 else blossomNodeAt snap v.val := by
    have same : blossomNodeAt final v.val = blossomNodeAt headState v.val := by
      simpa only [blossomNodeAt, finalPort 74, port 74] using
        highRead (snap.nr 74+v.val) (Nat.le_add_right _ _)
    exact same.trans (topNodes v)
  have finalCount : final.nm (final.nr 78+snap.nr 76) = ordered.length := by
    rw [fixedPort 78, highRead _ (secondBase.trans (Nat.le_add_right _ _)), ← actualHeaders.2, headerCount, rowCount]
  have starts (n : ℕ) : matchingCycleRecordStart final n = matchingCycleRecordStart u n := by
    rw [matchingCycleRecordStart, matchingCycleRecordStart, fixedPort 77, actualHeaders.1,
      highRead _ (firstBase.trans (Nat.le_add_right _ _))]
  have finalOrder := afterOrder.transport (t := final)
    (by simp only [matchingRebaseScratchEnd, finalPort 80, finalPort 55] <;> rfl) (finalPort 76) (finalPort 68)
    (fun id _ _ => starts id) (fun id _ _ => by
      simp only [matchingCycleRecordEnd, starts, finalPort 78]
      exact congrArg (fun n => matchingCycleRecordStart u id + 4*n)
        (highRead _ (by rw [actualHeaders.2]; exact secondBase.trans (Nat.le_add_right _ _))))
  have newStart : matchingCycleRecordStart final (snap.nr 76) = snap.nr 68 :=
    (starts _).trans rowStart
  have finalTable (j : ℕ) (inside : j < ordered.length) :
      matchingCycleChildAt final.nm (matchingCycleRecordStart final (snap.nr 76)+4*j) =
        matchingContractionWrittenChild snap j := by
    rw [newStart]
    have first : snap.nr 74 ≤ snap.nr 68+4*j := arenaFloor.trans (snapOrder.scratch.trans (Nat.le_add_right _ _))
    have held (w : ℕ) : final.nm (snap.nr 68+4*j+w) = u.nm (snap.nr 68+4*j+w) :=
      highRead _ (first.trans (Nat.le_add_right _ _))
    have atZero : final.nm (snap.nr 68+4*j) = u.nm (snap.nr 68+4*j) := highRead _ first
    simp only [matchingCycleChildAt, atZero, held 1, held 2, held 3]
    exact table j (rowCount.symm ▸ inside)
  let cut := part.contractCut cycle
  let nextState := state.registerCut cut (part.contractCut_odd cycle fixed oddCard)
  have freshCut : cut ∉ state.cuts := part.contractCut_fresh cycle fixed manyCard advanced.registry.nested
  have dualFloor (addr : ℕ) (above : snap.nr 75 ≤ addr) : headState.nr 66+k*k ≤ addr := by
    rw [port 66, ← show snap.nr 75 = snap.nr 66+k*k from snapStorage.cutDuals]
    exact above
  have cutValues (C : Finset (Fin k)) (live : C ∈ state.cuts) :
      final.rm (final.nr 75+advanced.dual.node C) = state.cutDual C := by
    rw [finalPort 75]
    have saved := finalReal (headState.nr 75+advanced.dual.node C)
      (.inr (dualFloor _ ((port 75).ge.trans (Nat.le_add_right _ _))))
    exact saved.trans (by
      have same : advanced.dual.node C = before.selected.dual.node C := congrFun nodes C
      rw [same]
      exact tables.2.1 C live)
  have cutZero : final.rm (final.nr 75+snap.nr 76) = 0 := by
    rw [finalPort 75]
    exact (finalReal _ (.inr (dualFloor _ ((port 75).ge.trans (Nat.le_add_right _ _))))).trans tables.2.2
  have separateTables : final.nr 62+k ≤ final.nr 75 := by
    rw [fixedPort 62, fixedPort 75]
    exact advanced.dual.separated
  have finalRoles : AlternatingForestMemory after (final.nr 51) final.nm := by
    rw [finalPort 51]
    intro v
    have index := v.isLt
    have props := roles v
    have lower (a : ℕ) (under : a < headState.nr 51+3*k) : final.nm a = headState.nm a := by
      have rep : snap.nr 51+3*k ≤ snap.nr 57 := snapStorage.warm.representativesAfter
      have cand : snap.nr 57+k ≤ snap.nr 58 := snapStorage.warm.candidatesAfter
      have within : a < snap.nr 51+3*k := by rw [port 51] at under; exact under
      exact finalNatural a (.inl (by rw [port 58]; omega))
    exact ⟨(lower _ (by omega)).trans props.1,(lower _ (by omega)).trans props.2.1,
      (lower _ (by omega)).trans props.2.2⟩
  let dual := contractionRegisteredDual part forest cycle base baseIn fixed oddCard manyCard covered advanced.registry.nested
    snap final advanced.dual (snap.nr 76) snapOrder.cursor advanced.registry.allocated
    finalReads.layout.dimension separateTables finalReads.potentials cutValues cutZero
    finalReads.representatives finalRoles finalTop
  have oldIDs (C : Finset (Fin k)) (live : C ∈ state.cuts) : dual.node C = advanced.dual.node C := by
    change (if C = cut then snap.nr 76 else advanced.dual.node C) = _
    exact if_neg (show C ≠ cut from fun h => freshCut (h ▸ live))
  have newID : dual.node cut = snap.nr 76 := if_pos rfl
  have cursor : final.nr 76 = snap.nr 76+1 := (finalPort 76).trans allocated
  have witnessBeforeMap : snap.nr 90 ≤ snap.nr 79 := by
    have low : snap.nr 90+2*k ≤ snap.nr 86 := beforeWork
    have work : snap.nr 86 ≤ snap.nr 89 := beforeMask
    have map : snap.nr 79 = snap.nr 89+k := snapStorage.memberMap
    omega
  have countSafe : final.nr 78+snap.nr 76 < final.nr 79 := by
    rw [fixedPort 78, fixedPort 79]
    exact beforeWitness.trans_le witnessBeforeMap
  have startSafe : final.nr 77+snap.nr 76 < final.nr 79 := by
    rw [fixedPort 77, fixedPort 79]
    exact firstHeader.trans_le ((Nat.le_add_right _ _).trans (beforeWitness.le.trans witnessBeforeMap))
  have archiveAt : matchingRebaseScratchEnd final ≤ matchingCycleRecordStart final (snap.nr 76) := by
    rw [newStart, matchingRebaseScratchEnd, fixedPort 80, fixedPort 55]
    exact snapOrder.scratch
  have stackSpace : final.nr 79+final.nr 55 ≤ final.nr 80 := by
    rw [fixedPort 79, fixedPort 55, fixedPort 80, show snap.nr 55 = k from sSize]
    exact snapStorage.memberStack.ge
  have safeStarts : final.nr 65+2*(k*k) ≤ final.nr 77 := by
    rw [fixedPort 65, fixedPort 77, ← show snap.nr 74 = snap.nr 65+2*(k*k) from snapStorage.nodes]
    exact firstBase
  have safeCounts : final.nr 65+2*(k*k) ≤ final.nr 78 := by
    rw [fixedPort 65, fixedPort 78, ← show snap.nr 74 = snap.nr 65+2*(k*k) from snapStorage.nodes]
    exact secondBase
  have safeStack : final.nr 65+2*(k*k) ≤ final.nr 80+3*final.nr 55 := by
    rw [fixedPort 65, fixedPort 80, fixedPort 55, ← show snap.nr 74 = snap.nr 65+2*(k*k) from snapStorage.nodes]
    have first : snap.nr 74 ≤ snap.nr 90 := secondBase.trans ((Nat.le_add_right _ _).trans beforeWitness.le)
    have stack : snap.nr 80 = snap.nr 79+k := snapStorage.memberStack
    omega
  have refs (p : Fin k) : reference.nm (snap.nr 74+p.val) = blossomNodeAt snap p.val := refNodes p
  obtain ⟨registry, ⟨cycles⟩⟩ := matchingContractionRegistersCycles liveCycles top left right base unique odd
    ((by decide : 1 < 3).trans_le longCycle) fixed mates (alternatingForest_contractionRotationMates advanced.search.valid oldA oldB ancestor)
    rowGeometry refs snapOrder (fun r listed => fixedPort r (by simp at listed ⊢; omega)) stableArchive
    finalTop finalCount finalTable cursor startSafe countSafe archiveAt stackSpace safeStarts safeCounts safeStack
    dual oldIDs newID
  have witnessFloor : snap.nr 74 ≤ snap.nr 90 :=
    secondBase.trans ((Nat.le_add_right _ _).trans beforeWitness.le)
  have witnessKept (v : Fin k) : matchingForestWitnessAt final.nm (final.nr 90) v.val =
      matchingForestWitnessAt snap.nm (snap.nr 90) v.val := by
    have nodeToWitness : snap.nr 74+k ≤ snap.nr 90 :=
      snapStorage.starts.ge.trans (headerOrder.trans ((Nat.le_add_right _ _).trans beforeWitness.le))
    have firstBefore : snap.nr 77+snap.nr 76 < snap.nr 90 :=
      firstHeader.trans_le ((Nat.le_add_right _ _).trans beforeWitness.le)
    have headKeep := view.witnesses sSize (port 90)
      (repsBefore.trans witnessFloor) (parentsBefore.trans ((Nat.le_add_right _ k).trans (repsBefore.trans witnessFloor)))
      nodeToWitness (.inr firstBefore) (.inr beforeWitness) beforeWork v
    rw [finalPort 90, port 90]
    have atWord (a : ℕ) (h : snap.nr 90 ≤ a) : final.nm a = u.nm a := highRead a (witnessFloor.trans h)
    simp only [matchingForestWitnessAt, forestWitnessAddress,
      atWord (snap.nr 90+(v.val+v.val)) (by omega), atWord (snap.nr 90+(v.val+v.val)+1) (by omega)]
    simpa only [matchingForestWitnessAt, forestWitnessAddress, (show u.nr 90 = snap.nr 90 from port 90)] using! headKeep
  obtain ⟨newTop, internal, search, linkWitnesses, links⟩ := matchingContraction_searchExit advanced.search top before.internal
    advanced.witnesses advanced.links oldA oldB ancestor witnessKept oddCard fixed
  have finalInherited :
      (nextState.cuts.filter fun C => dual.node C < final.nr 39) = inherited := by
    ext C
    change C ∈ (insert cut state.cuts).filter (fun C => dual.node C < final.nr 39) ↔
      C ∈ state.cuts.filter (fun C => advanced.dual.node C < snap.nr 39)
    simp only [Finset.mem_filter, Finset.mem_insert, fixedPort 39]
    by_cases old : C ∈ state.cuts
    · simp [old, oldIDs C old]
    · by_cases justAdded : C = cut
      · subst C
        have recent : ¬ dual.node cut < snap.nr 39 := by rw [newID]; exact Nat.not_lt_of_ge stamp
        simp [freshCut,recent]
      · simp [justAdded,old]
  have afterCounts : matchingStageCountsFromRAM k final (final.nr 39) =
      matchingPartitionCounts next.blocks (next.outerBlock after before.positive) inherited := by
    rw [matchingStageCountsFromRAM_eq dual before.positive _ registry.trees registry.unique registry.keys, finalInherited]
  have ramTransition : MatchingStageTransition (matchingStageCountsFromRAM k s (s.nr 39))
      (1+fresh.length+absorbed.length) (matchingStageCountsFromRAM k final (final.nr 39)) := by
    rw [counts,afterCounts]
    exact transition
  have budget := before.budget.advance ramTransition (fixedPort 39)
    (by rw [cursor]; exact Nat.le_succ _) (Nat.le_of_eq cursor)
  have outerTag (role : AlternatingForestRole (Fin k)) :
      role.outerTag = true ↔ alternatingRoleCode role = 1 := by
    cases role <;> simp [AlternatingForestRole.outerTag, alternatingRoleCode]
  have originalFresh : MatchingFreshCutOuter part forest advanced.dual.node (snap.nr 39) := by
    rw [nodes]
    exact before.fresh
  have finalFresh : MatchingFreshCutOuter next after dual.node (final.nr 39) := by
    rw [fixedPort 39]
    refine originalFresh.register cut rfl (fun C h _ => oldIDs C h) ?_ ?_
    · intro v hv
      have partOfCycle := (part.mem_contractCut cycle fixed v).mp hv
      have rep : next.representative v = base := by
        change blossomRepresentative cycle base (part.representative v) = base
        simp [blossomRepresentative,partOfCycle]
      rw [rep]
      apply (outerTag _).2
      obtain ⟨p, h⟩ := baseOuter
      have label : forest.role base = .outer p := h
      simp [after,AlternatingForestState.contract,label,alternatingRoleCode]
    · intro v current
      exact (outerTag _).2 (shape.outerPersists v ((outerTag _).1 current))
  have sameEffective : effectiveVertexPotential nextState.cuts nextState.potential nextState.cutDual = effective := by
    funext v
    exact effectiveVertexPotential_register_cut _ _ _ _ _
  have nextReads : MatchingRefreshInput final next.representative newRole cost
      (effectiveVertexPotential nextState.cuts nextState.potential nextState.cutDual) :=
    sameEffective.symm ▸ finalReads
  have nextPairs : MatchingSearchOuterBuckets final next.representative newRole cost
      (effectiveVertexPotential nextState.cuts nextState.potential nextState.cutDual) :=
    sameEffective.symm ▸ finalPairs
  have primal := advanced.primal
  have finalPrimal : CompactMatchingPrimalDualMemory nextState original final := {
    dimension := dual.dimension
    oddMap := (fixedPort 56).trans primal.oddMap
    mateAbove := by rw [fixedPort 50]; exact primal.mateAbove
    mate v := by
      rw [fixedPort 50]
      have idx := v.isLt
      have mates : snap.nr 50+k ≤ snap.nr 51 := snapStorage.warm.matesBefore
      have roles : snap.nr 51+3*k ≤ snap.nr 57 := snapStorage.warm.representativesAfter
      have reps : snap.nr 57+k ≤ snap.nr 58 := snapStorage.warm.candidatesAfter
      have addr : snap.nr 50+v.val < snap.nr 51 := by omega
      exact (finalNatural _ (.inl (by rw [port 58]; omega))).trans ((natural _ addr).trans (primal.mate v))
    saved r large := (fixedPort r (by simp; omega)).trans (primal.saved r large)
    natural a low := by
      have owned : original.nr 63 ≤ snap.nr 50 := primal.mateAbove
      have mates : snap.nr 50+k ≤ snap.nr 51 := snapStorage.warm.matesBefore
      have roles : snap.nr 51+3*k ≤ snap.nr 57 := snapStorage.warm.representativesAfter
      have reps : snap.nr 57+k ≤ snap.nr 58 := snapStorage.warm.candidatesAfter
      have below : a < snap.nr 51 := by omega
      exact (finalNatural a (.inl (by rw [port 58]; omega))).trans ((natural a below).trans (primal.natural a low))
    real a low := by
      have origin : snap.nr 62 = original.nr 64 := snapStorage.inputFloor
      have floor : snap.nr 62+k ≤ snap.nr 59 := advanced.reads.effectiveBefore
      have below : a < snap.nr 62 := by omega
      exact (finalReal a (.inl (by rw [port 59]; omega))).trans ((lowReal a below).trans (primal.real a low)) }
  have storage := snapStorage.keeps (t := final) (fun r h =>
    fixedPort r (by simp [matchingFixedStorageRegisters] at h; simp; omega))
  let post : MatchingActiveStage next after before.positive (matchingTopCutAt next) original i final :=
    ⟨finalPrimal,newTop,internal,search,linkWitnesses,links,dual,registry,finalFresh,finalRows,
      nextPairs,nextReads,budget,zero,(fixedPort 9).trans before.one⟩
  let prepared : MatchingPreparedStage cost original i final :=
    ⟨nextState,next,after,before.positive,before.count,post,cycles,storage,finalOrder⟩
  obtain ⟨checked, ticks, timing, checkedRun, _, _⟩ := matchingContractionHandlerBlock_runs s layout entry running before.one
  have same := whole.same_exit checkedRun
  have countsExit : 1+checked.nr 87+checked.nr 99 = 1+fresh.length+absorbed.length := by
    rw [← same.2]
    have a : result.nr 87 = absorbed.length := (tailPorts 87 (by decide)).trans countAbsorbed
    have b : result.nr 99 = fresh.length := (tailPorts 99 (by decide)).trans countFresh
    omega
  rw [← same.1, countsExit, sSize] at timing
  have allowance : (300*k+110)+(34*k+61) ≤ 1024*(k+1) := by omega
  have paid := Nat.mul_le_mul_right (1+fresh.length+absorbed.length) allowance
  rw [Nat.add_mul] at paid
  have overhead := Nat.le_mul_of_pos_right (34*k+61) (by omega : 0 < 1+fresh.length+absorbed.length)
  exact ⟨result,steps+tailTicks,1+fresh.length+absorbed.length,whole,tLive,
    (tailPorts 33 (by decide)).trans (port 33),⟨prepared⟩,ramTransition,by omega⟩

private theorem MatchingResolvedOuter.atArmEntry {k : ℕ} {forest : AlternatingForestState (Fin k)}
    {a b : Fin k} {scratch : ℕ} {s t : ArithmeticState} (trace : MatchingResolvedOuter forest a b scratch s t) :
    MatchingResolvedOuter forest a b scratch s {t with pc := 0} :=
  ⟨trace.tag, trace.selected, trace.zero, trace.leftCount, trace.rightCount, trace.left, trace.right, trace.shared,
    trace.split, trace.natural, trace.registers, trace.realRegisters, trace.realMemory⟩

set_option maxRecDepth 16384 in
/-- When the real classifier takes the contraction branch, the complete
dispatcher returns another prepared selector state and spends measured credit. -/
theorem MatchingDispatchState.contract {k i : ℕ} {cost : Fin k → Fin k → ℝ}
    {original s classified : ArithmeticState} {classTicks : ℕ}
    (before : MatchingDispatchState cost original i s) (searching : i < k/2)
    (symmetric : ∀ u v, cost u v = cost v u)
    (entry : s.pc = 0) (running : s.halted = false) (active : s.nr 33 ≠ 0)
    (outer : matchingEventClass s = 1) (winner : s.nr 1 ≤ s.nr 61)
    (classify : BlockRuns classifyAndTraceMatchingEvent classTicks s classified) (tag : classified.nr 35 = 1) :
    ∃ next ticks charge, BlockRuns weightedBlossomEventHandler ticks s next ∧
      next.halted = false ∧ next.nr 33 ≠ 0 ∧
      Nonempty (MatchingPreparedStage cost original i (matchingStageSnapshot next)) ∧
      MatchingStageTransition (matchingLoopCounts k i s) charge (matchingLoopCounts k i (matchingStageSnapshot next)) ∧
      ticks ≤ 1024*(k+1)*charge := by
  obtain ⟨a,b,selected,separate,pa,pb,oldA,oldB,middle,spent,classBound,actual,midLive,zero,one,two,
    id,ends,natural,real,rr,fixed,ready,_,_,trace⟩ := before.traceOuter entry running outer
  obtain ⟨sameTicks, sameExit⟩ := actual.same_exit classify
  subst middle
  have classifyCost : classTicks ≤ 34*k+57 := sameTicks ▸ classBound
  let m := {classified with pc := 0}
  have mTag : m.nr 35 = 1 := tag
  have port (r : ℕ) (used : r = 9 ∨ r = 20 ∨ r = 21 ∨ (30 ≤ r ∧ r ≤ 34) ∨
      (39 ≤ r ∧ r ≤ 90) ∨ 100 ≤ r := by decide) : m.nr r = s.nr r := fixed r used
  have regs (r : ℕ) (used : r = 9 ∨ r = 20 ∨ r = 21 ∨ r = 39 ∨ (50 ≤ r ∧ r ≤ 90) ∨ 100 ≤ r) :
      m.nr r = s.nr r := port r (by omega)
  let picked := before.afterTrace (t := m) searching winner natural real rr id regs
  cases ancestor : before.forest.commonAncestor (before.part.representative a) (before.part.representative b) with
  | none =>
    have bad : classified.nr 35 = 3 := by simpa [ancestor] using trace.tag
    exact ((by decide : (1 : ℕ) ≠ 3) (tag.symm.trans bad)).elim
  | some base =>
    have saved : MatchingResolvedOuter picked.forest (picked.part.representative a) (picked.part.representative b)
        (m.nr 83) ready m := by
      rw [port 83]
      exact trace.atArmEntry
    obtain ⟨t,ticks,charge,arm,live,activeAtExit,prepared,transition,armBound⟩ :=
      picked.contractArm searching symmetric rfl midLive oldA oldB separate selected ends ancestor saved
    have armByTag : BlockRuns (match m.nr 35 with
        | 0 => matchingGrowHandlerWithWitnesses
        | 1 => matchingContractionHandlerBlock
        | 2 => matchingExpandHandlerBlock
        | _ => matchingAugmentationHandlerBlock) ticks m t := by
      rw [mTag]
      exact arm
    obtain ⟨dispatchTicks, budget, dispatched⟩ :=
      dispatchMatchingActionBlock_spec (s := m) (t := t) rfl midLive live zero one two (by omega) armByTag
    have counts : matchingStageCountsFromRAM k m (m.nr 39) = matchingStageCountsFromRAM k s (s.nr 39) :=
      before.afterTrace_counts searching winner natural real rr id regs
    refine ⟨_,classTicks+dispatchTicks,charge,classify.append dispatched,live,?_,prepared,?_,by omega⟩
    · exact fun off => active ((activeAtExit.trans (port 33)).symm.trans off)
    · change MatchingStageTransition (matchingStageCountsFromRAM k s (s.nr 39)) charge
        (matchingStageCountsFromRAM k (matchingStageSnapshot t) ((matchingStageSnapshot t).nr 39))
      rw [← counts]
      exact transition


end VehicleRoutingSurvey.Routing
end RppSource_MatchingDispatchContraction

open VehicleRoutingSurvey.Routing SupplyChainTheory in
theorem solution : (fun {P : Prop} (_ : P) => P) (@VehicleRoutingSurvey.Routing.MatchingDispatchState.contract) :=
  @VehicleRoutingSurvey.Routing.MatchingDispatchState.contract
