-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.MatchingDispatchState.augment
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T16:04:17.596578+00:00
-- url     : https://prove2.me/submissions/6a5754d6-2821-4e11-8287-da1accd039af

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces
import Theorems.Thm_VehicleRoutingSurvey_Routing_matchingAugmentationHandlerBlock_selectedLift
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





theorem matchingCrossesCut_mk_iff {n : ℕ} (S : Finset (Fin n)) {u v : Fin n}
    (distinct : u ≠ v) : MatchingCrossesCut S s(u, v) ↔
      (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S) := by
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
    simp [MatchingCrossesCut, Sym2.mk_isDiag_iff, Sym2.toFinset_mk_eq, Finset.filter_insert,
      Finset.filter_singleton, hu, hv, distinct]











end VehicleRoutingSurvey.Routing
end RppSource_WeightedCertificate

/-! matching/WeightedDualStep.lean -/
section RppSource_WeightedDualStep
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory





















theorem oddCutDualEdgeValue_shift {n : ℕ} (cuts : Finset (Finset (Fin n)))
    (potential direction : Fin n → ℝ) (cutDual cutDirection : Finset (Fin n) → ℝ)
    (δ : ℝ) (e : Sym2 (Fin n)) :
    oddCutDualEdgeValue cuts (fun v => potential v + δ * direction v)
      (fun S => cutDual S + δ * cutDirection S) e =
    oddCutDualEdgeValue cuts potential cutDual e + δ * oddCutDualEdgeValue cuts direction cutDirection e := by
  simp only [oddCutDualEdgeValue, Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
  abel









end VehicleRoutingSurvey.Routing
end RppSource_WeightedDualStep

/-! matching/WeightedForestSlope.lean -/
section RppSource_WeightedForestSlope
namespace VehicleRoutingSurvey.Routing







private theorem forest_crossing_blocks {n : ℕ} {O : Finset (Fin n)}
    {cuts : Finset (Finset (Fin n))} (blocks : TopLevelMatchingBlocks O cuts)
    {u v : Fin n} (hu : u ∈ O) (hv : v ∈ O) (distinct : u ≠ v) :
    (O.image blocks.block).filter (MatchingCrossesCut · s(u, v)) =
      if blocks.block u = blocks.block v then ∅ else {blocks.block u, blocks.block v} := by
  by_cases same : blocks.block u = blocks.block v
  · rw [if_pos same]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hS
    obtain ⟨top, cross⟩ := Finset.mem_filter.mp hS
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp top
    rcases (matchingCrossesCut_mk_iff _ distinct).mp cross with ⟨inU, outV⟩ | ⟨inV, outU⟩
    · exact outV ((same.symm.trans (blocks.same_of_mem hw inU)) ▸ blocks.self_mem v hv)
    · exact outU ((same.trans (blocks.same_of_mem hw inV)) ▸ blocks.self_mem u hu)
  · rw [if_neg same]
    ext S
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
      matchingCrossesCut_mk_iff _ distinct]
    constructor
    · rintro ⟨top, ⟨inU, _⟩ | ⟨inV, _⟩⟩
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp top
        exact Or.inl (blocks.same_of_mem hw inU).symm
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp top
        exact Or.inr (blocks.same_of_mem hw inV).symm
    · rintro (rfl | rfl)
      · exact ⟨Finset.mem_image_of_mem _ hu, Or.inl ⟨blocks.self_mem u hu, fun bad =>
          same (blocks.same_of_mem hu bad).symm⟩⟩
      · exact ⟨Finset.mem_image_of_mem _ hv, Or.inr ⟨blocks.self_mem v hv, fun bad =>
          same (blocks.same_of_mem hv bad)⟩⟩

/-- The dual slope of an edge is zero within a block. Across blocks it is the sum of their
two labels, so checking one edge does not require scanning the current cut variables. -/
theorem forest_edge_slope {n : ℕ} {O : Finset (Fin n)} {cuts : Finset (Finset (Fin n))}
    (blocks : TopLevelMatchingBlocks O cuts) (label : Finset (Fin n) → ℝ)
    {u v : Fin n} (hu : u ∈ O) (hv : v ∈ O) (distinct : u ≠ v) :
    oddCutDualEdgeValue cuts (forestVertexDirection blocks label) (forestCutDirection blocks label)
      s(u, v) = if blocks.block u = blocks.block v then 0 else label (blocks.block u) + label (blocks.block v) := by
  have supportEq : (cuts.filter (MatchingCrossesCut · s(u, v))).filter
      (fun S => S ∈ O.image blocks.block ∧ S.card ≠ 1) =
      ((O.image blocks.block).filter (MatchingCrossesCut · s(u, v))).filter (fun S => S.card ≠ 1) := by
    ext S
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨_, cross⟩, top, notOne⟩
      exact ⟨⟨top, cross⟩, notOne⟩
    · rintro ⟨⟨top, cross⟩, notOne⟩
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp top
      exact ⟨⟨blocks.cut_mem hw notOne, cross⟩, top, notOne⟩
  have sumEq : (∑ S ∈ cuts.filter (MatchingCrossesCut · s(u, v)), forestCutDirection blocks label S) =
      ∑ S ∈ ((O.image blocks.block).filter (MatchingCrossesCut · s(u, v))).filter (fun S => S.card ≠ 1),
        label S := by
    calc
      _ = ∑ S ∈ (cuts.filter (MatchingCrossesCut · s(u, v))).filter
          (fun S => S ∈ O.image blocks.block ∧ S.card ≠ 1), label S :=
        (Finset.sum_filter _ _).symm
      _ = _ := congrArg (fun sets => ∑ S ∈ sets, label S) supportEq
  unfold oddCutDualEdgeValue forestVertexDirection
  rw [sumEq, forest_crossing_blocks blocks hu hv distinct, Sym2.toFinset_mk_eq]
  by_cases same : blocks.block u = blocks.block v
  · have vNotOne : (blocks.block v).card ≠ 1 := by
      intro one
      obtain ⟨w, singleton⟩ := Finset.card_eq_one.mp one
      have uIn : u ∈ blocks.block v := same ▸ blocks.self_mem u hu
      have vIn := blocks.self_mem v hv
      rw [singleton] at uIn vIn
      exact distinct ((Finset.mem_singleton.mp uIn).trans (Finset.mem_singleton.mp vIn).symm)
    simp [same, vNotOne, Finset.sum_insert, distinct]
  · by_cases uOne : (blocks.block u).card = 1 <;> by_cases vOne : (blocks.block v).card = 1 <;>
      simp [same, uOne, vOne, distinct, Finset.sum_insert, Finset.filter_insert,
        Finset.filter_singleton, add_comm]

end VehicleRoutingSurvey.Routing
end RppSource_WeightedForestSlope

/-! matching/MatchingPartitionView.lean -/
section RppSource_MatchingPartitionView
namespace VehicleRoutingSurvey.Routing













theorem CompactMatchingPartition.representativeOf_block {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (positive : 0 < k)
    (v : Fin k) : part.representativeOf positive (part.blocks.block v) = part.representative v := by
  have members : (part.blocks.block v).Nonempty := ⟨v, part.blocks.self_mem v (Finset.mem_univ v)⟩
  rw [CompactMatchingPartition.representativeOf, dif_pos members]
  exact part.constant _ _ (part.blocks.same_of_mem (Finset.mem_univ v) members.choose_spec)




end VehicleRoutingSurvey.Routing
end RppSource_MatchingPartitionView

/-! matching/CompactEdges.lean -/
section RppSource_CompactEdges
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



theorem mem_compactMatchingEdges_mk {k : ℕ} {u v : Fin k} (different : u ≠ v) :
    s(u, v) ∈ compactMatchingEdges k := by
  apply List.mem_flatMap.mpr
  refine ⟨u, by simp, List.mem_map.mpr ⟨v, ?_, rfl⟩⟩
  simp [different]

theorem mem_compactMatchingEdges_iff {k : ℕ} {e : Sym2 (Fin k)} :
    e ∈ compactMatchingEdges k ↔ ¬ e.IsDiag := by
  constructor
  · intro h
    obtain ⟨u, _, row⟩ := List.mem_flatMap.mp h
    obtain ⟨v, present, rfl⟩ := List.mem_map.mp row
    have distinct : u ≠ v := of_decide_eq_true (List.mem_filter.mp present).2
    exact fun loop => distinct (Sym2.mk_isDiag_iff.mp loop)
  · induction e using Sym2.inductionOn with
    | hf u v => exact fun h => mem_compactMatchingEdges_mk (fun eq => h (Sym2.mk_isDiag_iff.mpr eq))



end VehicleRoutingSurvey.Routing
end RppSource_CompactEdges

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

/-! matching/MatchingSearchDual.lean -/
section RppSource_MatchingSearchDual
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory





theorem AlternatingForestState.mate_dualDirection_add_eq_zero {α : Type*}
    {forest : AlternatingForestState α} {mate : α → Option α} {tight : α → α → Prop}
    (valid : forest.valid mate tight) {u v : α} (uv : mate u = some v) (vu : mate v = some u) :
    (forest.role u).dualDirection + (forest.role v).dualDirection = 0 := by
  have outerPartner {x y : α} {p : Option α} (outer : forest.role x = .outer p) (xy : mate x = some y) :
      ∃ r, forest.role y = .inner r := by
    have row := valid x
    rw [outer] at row
    cases p with
    | none =>
      have impossible : some y = none := xy.symm.trans row
      simp at impossible
    | some p =>
      obtain ⟨pInner, xp, _, _, _⟩ := row
      exact (Option.some.inj (xp.symm.trans xy)) ▸ pInner
  have innerPartner {x y p : α} (inner : forest.role x = .inner p) (xy : mate x = some y) :
      forest.role y = .outer (some x) := by
    have row := valid x
    rw [inner] at row
    obtain ⟨_, _, ⟨z, xz, outer⟩, _, _⟩ := row
    exact (Option.some.inj (xz.symm.trans xy)) ▸ outer
  cases hu : forest.role u with
  | outer p =>
    obtain ⟨r, hv⟩ := outerPartner hu uv
    norm_num [hv, AlternatingForestRole.dualDirection]
  | inner p => norm_num [innerPartner hu uv, AlternatingForestRole.dualDirection]
  | unlabelled =>
    cases hv : forest.role v with
    | unlabelled => simp [AlternatingForestRole.dualDirection]
    | outer p =>
      obtain ⟨r, bad⟩ := outerPartner hv vu
      simp [hu] at bad
    | inner p =>
      have bad := innerPartner hv vu
      simp [hu] at bad



theorem CompactMatchingPartition.dualLabel_block {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (positive : 0 < k) (v : Fin k) :
    part.dualLabel forest positive (part.blocks.block v) = (forest.role (part.representative v)).dualDirection := by
  rw [CompactMatchingPartition.dualLabel, part.representativeOf_block]

theorem CompactMatchingSearchForest.matched_slope_zero {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop}
    (search : CompactMatchingSearchForest part forest mate tight) (positive : 0 < k)
    {e : Sym2 (Fin k)} (present : e ∈ state.edges) :
    oddCutDualEdgeValue state.cuts (forestVertexDirection part.blocks (part.dualLabel forest positive))
      (forestCutDirection part.blocks (part.dualLabel forest positive)) e = 0 := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    have legal := (state.perfect.1 _ present).1
    have distinct : u ≠ v := fun same => legal (Sym2.mk_isDiag_iff.mpr same)
    rw [forest_edge_slope part.blocks _ (Finset.mem_univ u) (Finset.mem_univ v) distinct]
    by_cases same : part.blocks.block u = part.blocks.block v
    · rw [if_pos same]
    · rw [if_neg same, part.dualLabel_block, part.dualLabel_block]
      obtain ⟨uv, vu⟩ := search.crossing present same
      exact AlternatingForestState.mate_dualDirection_add_eq_zero search.valid uv vu

/-- The selected step keeps the primal matching and partition intact while
updating the two dual functions and exposing the newly tight event. -/
noncomputable def CompactMatchingPrimalDual.advanceSearch {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) (part : CompactMatchingPartition state)
    {forest : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop}
    (search : CompactMatchingSearchForest part forest mate tight) (positive : 0 < k)
    (internal : state.InternalCuts) (bound : DualBound (MatchingDualEvent k))
    (adjustment : MatchingDualAdjustment cost (compactMatchingEdges k) state.cuts state.potential
      (forestVertexDirection part.blocks (part.dualLabel forest positive)) state.cutDual
      (forestCutDirection part.blocks (part.dualLabel forest positive)) bound) : CompactMatchingPrimalDual k cost where
  covered := state.covered
  edges := state.edges
  perfect := state.perfect
  cuts := state.cuts
  potential v := state.potential v + bound.amount * forestVertexDirection part.blocks (part.dualLabel forest positive) v
  cutDual B := state.cutDual B + bound.amount * forestCutDirection part.blocks (part.dualLabel forest positive) B
  cutValid B present := ⟨(state.cutValid B present).1, adjustment.2.2.1 B present⟩
  feasible e legal := adjustment.2.1 e (mem_compactMatchingEdges_iff.mpr legal)
  tight e present := by
    rw [oddCutDualEdgeValue_shift, search.matched_slope_zero positive present, mul_zero, add_zero]
    exact state.tight e present
  internal B present _ := internal B present


end VehicleRoutingSurvey.Routing
end RppSource_MatchingSearchDual

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











theorem CompactMatchingPartition.mem_activeRepresentatives {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (v : Fin k) :
    v ∈ part.activeRepresentatives ↔ part.representative v = v := by
  simp [CompactMatchingPartition.activeRepresentatives]










end VehicleRoutingSurvey.Routing
end RppSource_MatchingWarmPrimal

/-! matching/MatchingMemberTree.lean -/
section RppSource_MatchingMemberTree
namespace VehicleRoutingSurvey.Routing



namespace MatchingMemberTree



def nodes : MatchingMemberTree → ℕ
  | .nil => 0
  | .leaf _ siblings => 1 + siblings.nodes
  | .blossom _ _ children siblings => 1 + children.nodes + siblings.nodes













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





def proper (job : MatchingMemberJob) : Prop :=
  match job.children with
  | none => job.node = 0
  | some children => 0 < job.node ∧ 2 ≤ children.arity ∧ children.proper













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

/-! matching/MatchingEventDualRefinement.lean -/
section RppSource_MatchingEventDualRefinement
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Moving the dual leaves the top partition and its representatives intact. -/
noncomputable def CompactMatchingPartition.advanceSearch {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    {forest : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop}
    (search : CompactMatchingSearchForest part forest mate tight) (positive : 0 < k)
    (internal : state.InternalCuts) (bound : DualBound (MatchingDualEvent k))
    (adjustment : MatchingDualAdjustment cost (compactMatchingEdges k) state.cuts state.potential
      (forestVertexDirection part.blocks (part.dualLabel forest positive)) state.cutDual
      (forestCutDirection part.blocks (part.dualLabel forest positive)) bound) :
    CompactMatchingPartition (state.advanceSearch part search positive internal bound adjustment) where
  blocks := part.blocks
  representative := part.representative
  inside := part.inside
  constant := part.constant
  coveredAway := part.coveredAway

/-- Run the actual linear dual-update block and recover the shifted primal-dual
state in RAM, with the same matching, topology, and registry identifiers. -/
theorem advanceMatchingEventDuals_refines {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop}
    {original s : ArithmeticState} (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (primal : CompactMatchingPrimalDualMemory state original s)
    (dual : MatchingSearchDualMemory part forest s) (search : CompactMatchingSearchForest part forest mate tight)
    (positive : 0 < k) (internal : state.InternalCuts) (realFloor : original.nr 64 ≤ s.nr 62)
    (event : MatchingDualEvent k)
    (adjustment : MatchingDualAdjustment cost (compactMatchingEdges k) state.cuts state.potential
      (forestVertexDirection part.blocks (part.dualLabel forest positive)) state.cutDual
      (forestCutDirection part.blocks (part.dualLabel forest positive)) ⟨event, s.rr 1⟩) :
    let next := state.advanceSearch part search positive internal ⟨event, s.rr 1⟩ adjustment
    let nextPart := part.advanceSearch search positive internal ⟨event, s.rr 1⟩ adjustment
    ∃ t ticks, ticks ≤ 31 * k + 6 ∧ BlockRuns advanceMatchingEventDuals ticks s t ∧ t.halted = false ∧
      CompactMatchingPrimalDualMemory next original t ∧
      (∃ nextDual : MatchingSearchDualMemory nextPart forest t, nextDual.node = dual.node) ∧
      t.nm = s.nm ∧ t.rr 1 = s.rr 1 ∧ t.rr 15 = s.rr 15 + s.rr 1 ∧ t.nr 14 = 0 ∧
      (∀ r, r ∉ [0, 6, 7, 10, 11, 12, 14] → t.nr r = s.nr r) := by
  intro next nextPart
  obtain ⟨t, ticks, bound, run, live, natural, delta, clock, zero, fixed, real⟩ :=
    advanceMatchingEventDuals_spec s entry running one
  rw [dual.dimension] at bound
  have realBase : t.nr 62 = s.nr 62 := fixed 62 (by decide)
  have cutBase : t.nr 75 = s.nr 75 := fixed 75 (by decide)
  have primalNext : CompactMatchingPrimalDualMemory next original t := {
    dimension := (fixed 55 (by decide)).trans primal.dimension
    oddMap := (fixed 56 (by decide)).trans primal.oddMap
    mateAbove := (fixed 50 (by decide)).symm ▸ primal.mateAbove
    mate := by
      intro v
      rw [natural, fixed 50 (by decide)]
      exact primal.mate v
    saved r high := (fixed r (by simp; omega)).trans (primal.saved r high)
    natural a ha := by rw [natural]; exact primal.natural a ha
    real a ha := by
      rw [real, matchingEventDualMemory_keeps_prefix s (original.nr 64) a ha realFloor
        (realFloor.trans ((Nat.le_add_right _ _).trans dual.separated))]
      exact primal.real a ha }
  let dualNext : MatchingSearchDualMemory nextPart forest t := {
    dimension := primalNext.dimension
    separated := by rw [realBase, cutBase]; exact dual.separated
    reps v := by rw [natural, fixed 57 (by decide)]; exact dual.reps v
    roles := by rw [natural, fixed 51 (by decide)]; exact dual.roles
    effective v := dual.advanced_effective_table positive real realBase v
    node := dual.node
    nodeNonzero := dual.nodeNonzero
    nodeInjective := dual.nodeInjective
    cutValues _ present := dual.advanced_cut_table positive real cutBase present
    top v := by rw [blossomNodeAt, natural, fixed 74 (by decide)]; exact dual.top v }
  exact ⟨t, ticks, bound, run, live, primalNext, ⟨dualNext, rfl⟩,
    natural, delta, clock, zero, fixed⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingEventDualRefinement

/-! matching/MatchingSearchWitnesses.lean -/
section RppSource_MatchingSearchWitnesses
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



theorem AlternatingForestState.parent_directions_cancel {α : Type*} {forest : AlternatingForestState α}
    {mate : α → Option α} {tight : α → α → Prop} (valid : forest.valid mate tight)
    {child parent : α} (link : (forest.role child).parent = some parent) :
    (forest.role parent).dualDirection + (forest.role child).dualDirection = 0 := by
  have row := valid child
  cases kind : forest.role child with
  | unlabelled => simp [kind, AlternatingForestRole.parent] at link
  | outer prior =>
    rw [kind] at link
    change prior = some parent at link
    subst prior
    rw [kind] at row
    obtain ⟨q, inner⟩ := row.1
    norm_num [inner, AlternatingForestRole.dualDirection]
  | inner p =>
    rw [kind] at link
    change some p = some parent at link
    obtain rfl := Option.some.inj link
    rw [kind] at row
    obtain ⟨q, outer⟩ := row.1
    norm_num [outer, AlternatingForestRole.dualDirection]

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

/-- The original edge witnesses for parent links remain tight at the end of a
dual step. The input state uses the old numerical values, and the output state
may be the result of any block preserving the parent-edge array. -/
theorem MatchingForestOriginalWitnesses.advance {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop}
    {s t : ArithmeticState} (original : MatchingForestOriginalWitnesses part forest s)
    (search : CompactMatchingSearchForest part forest mate tight) (positive : 0 < k)
    (internal : state.InternalCuts) (bound : DualBound (MatchingDualEvent k))
    (adjustment : MatchingDualAdjustment cost (compactMatchingEdges k) state.cuts state.potential
      (forestVertexDirection part.blocks (part.dualLabel forest positive)) state.cutDual
      (forestCutDirection part.blocks (part.dualLabel forest positive)) bound)
    (keeps : ∀ v : Fin k, matchingForestWitnessAt t.nm (t.nr 90) v.val = matchingForestWitnessAt s.nm (s.nr 90) v.val) :
    let nextPart := part.advanceSearch search positive internal bound adjustment
    MatchingForestOriginalWitnesses nextPart forest t ∧ CompactMatchingSearchForest nextPart forest mate nextPart.tightBetween := by
  intro nextPart
  have witnesses : MatchingForestOriginalWitnesses nextPart forest t := by
    intro child parent link
    obtain ⟨a, b, words, first, second, before⟩ := original link
    have marked : forest.role child ≠ .unlabelled := by
      intro idle
      simp [idle, AlternatingForestRole.parent] at link
    have row := AlternatingForestState.parent_valid search.valid marked
    rw [link] at row
    have different : parent ≠ child := fun eq => (lt_irrefl _) (eq ▸ row.2.1)
    have separated : part.blocks.block a ≠ part.blocks.block b := by
      intro same
      exact different (first.symm.trans ((part.same_block.mpr same).trans second))
    have endpoints : a ≠ b := fun eq => separated (congrArg part.blocks.block eq)
    have slope : oddCutDualEdgeValue state.cuts (forestVertexDirection part.blocks (part.dualLabel forest positive))
        (forestCutDirection part.blocks (part.dualLabel forest positive)) s(a, b) = 0 := by
      rw [forest_edge_slope part.blocks _ (Finset.mem_univ a) (Finset.mem_univ b) endpoints, if_neg separated,
        part.dualLabel_block, part.dualLabel_block, first, second]
      exact AlternatingForestState.parent_directions_cancel search.valid link
    refine ⟨a, b, (keeps child).trans words, first, second, ?_⟩
    change oddCutDualEdgeValue state.cuts
      (fun v => state.potential v + bound.amount * forestVertexDirection part.blocks (part.dualLabel forest positive) v)
      (fun S => state.cutDual S + bound.amount * forestCutDirection part.blocks (part.dualLabel forest positive) S)
      s(a, b) = _
    rw [oddCutDualEdgeValue_shift, slope, mul_zero, add_zero]
    exact before
  refine ⟨witnesses, ⟨?_, search.crossing, search.exposed⟩⟩
  apply AlternatingForestState.valid_of_parent_tight search.valid
  intro child parent link
  obtain ⟨a, b, _, first, second, value⟩ := witnesses link
  exact ⟨a, b, first, second, value⟩




end VehicleRoutingSurvey.Routing
end RppSource_MatchingSearchWitnesses

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

/-! matching/MatchingGrowCacheRows.lean -/
section RppSource_MatchingGrowCacheRows
namespace VehicleRoutingSurvey.Routing



theorem MatchingCacheLayout.keeps {k : ℕ} {s t : ArithmeticState} (layout : MatchingCacheLayout k s)
    (fixed : ∀ r ≥ 50, t.nr r = s.nr r) : MatchingCacheLayout k t := by
  constructor
  · rw [fixed 55 (by decide)]; exact layout.dimension
  · rw [fixed 61 (by decide)]; exact layout.rows
  · rw [fixed 58 (by decide), fixed 61 (by decide), fixed 54 (by decide)]; exact layout.idsBefore
  · rw [fixed 54 (by decide), fixed 61 (by decide), fixed 65 (by decide)]; exact layout.recordsBefore
  · rw [fixed 59 (by decide), fixed 61 (by decide), fixed 60 (by decide)]; exact layout.slacksBefore
  · rw [fixed 60 (by decide), fixed 61 (by decide), fixed 66 (by decide)]; exact layout.ratesBefore




end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowCacheRows

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










end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseFrontier

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




end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseArchiveFootprint

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





theorem MatchingRegistryBudget.finish {k stage : ℕ} {s t : ArithmeticState} {before : MatchingStageCounts}
    (budget : MatchingRegistryBudget k stage s before) (cursor : t.nr 76 = s.nr 76) :
    t.nr 76 ≤ 6 * k * (stage + 1) + 1 := by
  have cut := budget.cutoff
  have old := budget.allowance
  rw [Nat.mul_succ]
  omega


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRegistryBudget

/-! matching/MatchingRegistryView.lean -/
section RppSource_MatchingRegistryView
namespace VehicleRoutingSurvey.Routing







private theorem MatchingMemberTree.readable_keeps {tree : MatchingMemberTree}
    {s t : ℕ → ℕ} {startBase countBase : ℕ} {untouched : ℕ → Prop}
    (ready : tree.readable s startBase countBase untouched) (keeps : ∀ a, untouched a → t a = s a) :
    tree.readable t startBase countBase untouched := by
  induction tree with
  | nil => trivial
  | leaf v rest ih => exact ih ready
  | blossom r node children rest childIH tailIH =>
    obtain ⟨first, last, words, child, tail⟩ := ready
    refine ⟨first, last, ?_, childIH child, tailIH tail⟩
    intro i inside j bound
    rw [keeps _ first]
    exact words i inside j bound

/-- Moving the search dual or changing the labels retains all cycle records
whenever the live cuts, top partition and physical registry agree. -/
def MatchingRegistryView.reindex {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state next : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {nextPart : CompactMatchingPartition next}
    {before after : AlternatingForestState (Fin k)} {s t : ArithmeticState}
    {old : MatchingSearchDualMemory part before s} {new : MatchingSearchDualMemory nextPart after t}
    (registry : MatchingRegistryView old) (ids : new.node = old.node)
    (cuts : next.cuts = state.cuts) (blocks : nextPart.blocks.block = part.blocks.block)
    (headers : t.nr 77 = s.nr 77) (lengths : t.nr 78 = s.nr 78) (cursor : t.nr 76 = s.nr 76)
    (pointers : t.nr 65 = s.nr 65) (top : ∀ v : Fin k, blossomNodeAt t v = blossomNodeAt s v)
    (natural : ∀ a ≥ s.nr 65 + 2 * (k * k), t.nm a = s.nm a) : MatchingRegistryView new := by
  let tree : MatchingTopMemberTrees k t := {
    tree := registry.trees.tree
    roots := by
      intro v
      change (registry.trees.tree v).rootKeys =
        (if blossomNodeAt t v = 0 then [] else [MatchingMemberTree.rootKey v.val (blossomNodeAt t v)])
      rw [top]
      exact registry.trees.roots v
    proper := registry.trees.proper
    encoded := by
      intro v
      rw [headers, lengths]
      exact MatchingMemberTree.encoded_congr (registry.trees.encoded v) (registry.readable v) natural }
  refine ⟨tree, ?_, registry.unique, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    rw [headers, lengths, pointers]
    exact MatchingMemberTree.readable_keeps (registry.readable v) natural
  · intro n
    change n ∈ registry.trees.registryIds ↔ _
    rw [ids, cuts]
    exact registry.keys n
  · intro B present
    rw [ids, cursor]
    exact registry.allocated B (cuts ▸ present)
  · rw [cuts]; exact registry.nontrivial
  · rw [cuts]; exact registry.laminar
  · intro B present u hu v hv
    rw [blocks]
    exact registry.nested B (cuts ▸ present) u hu v hv

def MatchingRegistryView.transport {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {before after : AlternatingForestState (Fin k)} {s t : ArithmeticState}
    {old : MatchingSearchDualMemory part before s} {new : MatchingSearchDualMemory part after t}
    (registry : MatchingRegistryView old) (ids : new.node = old.node)
    (headers : t.nr 77 = s.nr 77) (lengths : t.nr 78 = s.nr 78) (cursor : t.nr 76 = s.nr 76)
    (pointers : t.nr 65 = s.nr 65) (top : ∀ v : Fin k, blossomNodeAt t v = blossomNodeAt s v)
    (natural : ∀ a ≥ s.nr 65 + 2 * (k * k), t.nm a = s.nm a) : MatchingRegistryView new :=
  registry.reindex ids rfl rfl headers lengths cursor pointers top natural


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRegistryView

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

theorem matchingCacheReads_unchanged {k : ℕ} (cutAt : Fin k → Finset (Fin k)) {m t : ArithmeticState}
    (natural : t.nm = m.nm) (real : t.rm = m.rm)
    (registers : ∀ r ∈ matchingRefreshTableRegisters, t.nr r = m.nr r) :
    (∀ i, MatchingCandidateRowValid cutAt t i = MatchingCandidateRowValid cutAt m i ∧
      readMatchingCandidate cutAt t i = readMatchingCandidate cutAt m i) ∧
    (∀ i, MatchingPairBucketValid k t i = MatchingPairBucketValid k m i ∧
      readMatchingPairBucket (k := k) t i = readMatchingPairBucket (k := k) m i) := by
  have keep (r : ℕ) (used : r ∈ matchingRefreshTableRegisters := by decide) := registers r used
  constructor <;> intro i <;> constructor
  · simp only [MatchingCandidateRowValid, decodeMatchingDictionaryEvent, natural, keep 54, keep 58]
  · simp only [readMatchingCandidate, decodeMatchingDictionaryEvent, natural, real, keep 54, keep 58, keep 59, keep 60]
  · simp only [MatchingPairBucketValid, natural, keep 65]
  · simp only [readMatchingPairBucket, natural, real, keep 65, keep 66]









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

/-- Size and allocation of every encountered ID put the full stored child
records above the part of RAM modified by a warm search preparation. -/
theorem MatchingMemberTree.readableAbove {s : ArithmeticState} {floor : ℕ} (tree : MatchingMemberTree)
    (order : MatchingCycleRecordOrder s) (starts : floor ≤ s.nr 77) (sizes : floor ≤ s.nr 78)
    (rows : floor ≤ matchingRebaseScratchEnd s)
    (bounds : ∀ n ∈ tree.registryIds, 0 < n ∧ n < s.nr 76) :
    tree.readable s.nm (s.nr 77) (s.nr 78) (fun a => floor ≤ a) := by
  induction tree with
  | nil => trivial
  | leaf v rest ih => exact ih bounds
  | blossom r n c rest ci ri =>
    have here := bounds n (by simp [MatchingMemberTree.registryIds])
    have start := rows.trans (order.bounded n here.1 here.2).1
    unfold matchingCycleRecordStart at start
    refine ⟨by omega, by omega, fun _ _ _ _ => by omega,
      ci (fun id h => bounds id (by simp [MatchingMemberTree.registryIds,h])),
      ri (fun id h => bounds id (by simp [MatchingMemberTree.registryIds,h]))⟩

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





end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentPathProjection

/-! matching/MatchingAugmentComplete.lean -/
section RppSource_MatchingAugmentComplete
namespace VehicleRoutingSurvey.Routing







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






end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentInitialTasks

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




end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentBlockLifts

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

/-! matching/MatchingRebaseRegisteredTree.lean -/
section RppSource_MatchingRebaseRegisteredTree
namespace VehicleRoutingSurvey.Routing

/-- Relabel registered children by their new exposed originals while
retaining every leaf and every permanent node identifier. -/
def MatchingMemberTree.relabel (change : ℕ → ℕ → ℕ) : MatchingMemberTree → MatchingMemberTree
  | .nil => .nil
  | .leaf v rest => .leaf v (rest.relabel change)
  | .blossom p n child rest => .blossom (change n p) n (child.relabel change) (rest.relabel change)

@[simp] theorem MatchingMemberTree.relabel_arity (e : MatchingMemberTree) (f : ℕ → ℕ → ℕ) :
    (e.relabel f).arity = e.arity := by
  induction e <;> simp [MatchingMemberTree.relabel,MatchingMemberTree.arity, *]

@[simp] theorem MatchingMemberTree.relabel_leaves (e : MatchingMemberTree) (f : ℕ → ℕ → ℕ) :
    (e.relabel f).leaves = e.leaves := by
  induction e <;> simp [MatchingMemberTree.relabel,MatchingMemberTree.leaves, *]

@[simp] theorem MatchingMemberTree.relabel_ids (e : MatchingMemberTree) (f : ℕ → ℕ → ℕ) :
    (e.relabel f).registryIds = e.registryIds := by
  induction e <;> simp [MatchingMemberTree.relabel,MatchingMemberTree.registryIds, *]

@[simp] theorem MatchingMemberTree.relabel_proper (e : MatchingMemberTree) (f : ℕ → ℕ → ℕ) :
    (e.relabel f).proper ↔ e.proper := by
  induction e <;> simp [MatchingMemberTree.relabel,MatchingMemberTree.proper, *]





def matchingRelabelKey (f : ℕ → ℕ → ℕ) (key : ℕ × ℕ) : ℕ × ℕ :=
  (if key.2 = 0 then key.1 else f key.2 key.1, key.2)

theorem MatchingMemberTree.relabel_keys (e : MatchingMemberTree) (well : e.proper) (f : ℕ → ℕ → ℕ) :
    (e.relabel f).rootKeys = e.rootKeys.map (matchingRelabelKey f) := by
  induction e with
  | nil => rfl
  | leaf v tail ih => simp [MatchingMemberTree.relabel,MatchingMemberTree.rootKeys,MatchingMemberTree.rootKey,matchingRelabelKey,ih well]
  | blossom p n child tail ci ti =>
    obtain ⟨positive,_,_,right⟩ := well
    simp [MatchingMemberTree.relabel,MatchingMemberTree.rootKeys,MatchingMemberTree.rootKey,matchingRelabelKey,
      Nat.ne_of_gt positive,ti right]

def MatchingMemberJob.relabel (f : ℕ → ℕ → ℕ) (j : MatchingMemberJob) : MatchingMemberJob :=
  match j.children with
  | none => ⟨j.representative,j.node,j.representative,none⟩
  | some child => ⟨f j.node j.representative,j.node,f j.node j.representative,some (child.relabel f)⟩

theorem MatchingMemberTree.relabel_jobs (tree : MatchingMemberTree) (f : ℕ → ℕ → ℕ) :
    (tree.relabel f).jobs none = (tree.jobs none).map (MatchingMemberJob.relabel f) := by
  induction tree with
  | nil => rfl
  | leaf v t ih => simp [MatchingMemberTree.relabel,MatchingMemberTree.jobs,MatchingMemberJob.relabel,ih]
  | blossom p n c t ci ti => simp [MatchingMemberTree.relabel,MatchingMemberTree.jobs,MatchingMemberJob.relabel,ti]

@[simp] theorem MatchingMemberJob.relabel_leaves (f : ℕ → ℕ → ℕ) (j : MatchingMemberJob) :
    (j.relabel f).tree.leaves = j.tree.leaves := by
  cases form : j.children <;> simp [MatchingMemberJob.relabel,MatchingMemberJob.tree,form,MatchingMemberTree.leaves]

theorem MatchingMemberTree.relabel_encoded {s t : ArithmeticState} (tree : MatchingMemberTree)
    (f : ℕ → ℕ → ℕ) (proper : tree.proper) (enc : tree.encoded s.nm (s.nr 77) (s.nr 78))
    (headers : ∀ n ∈ tree.registryIds, matchingCycleRecordStart t n = matchingCycleRecordStart s n ∧
      t.nm (t.nr 78+n) = s.nm (s.nr 78+n))
    (newKeys : ∀ n ∈ tree.registryIds, ∀ i < s.nm (s.nr 78+n),
      let oldRow := matchingRebaseRowsAt s s n i
      let newRow := matchingRebaseRowsAt s t n i
      (newRow.representative,newRow.node) = matchingRelabelKey f (oldRow.representative,oldRow.node)) :
    (tree.relabel f).encoded t.nm (t.nr 77) (t.nr 78) := by
  induction tree with
  | nil => trivial
  | leaf _ tail ih => exact ih proper enc headers newKeys
  | blossom p n child tail ci ti =>
    obtain ⟨_,_,childProper,tailProper⟩ := proper
    obtain ⟨count,keys,encChild,encTail⟩ := enc
    have here : n ∈ (MatchingMemberTree.blossom p n child tail).registryIds := by simp [MatchingMemberTree.registryIds]
    have inChild (r : ℕ) (hr : r ∈ child.registryIds) : r ∈ (MatchingMemberTree.blossom p n child tail).registryIds := by
      simp [MatchingMemberTree.registryIds,hr]
    have inTail (r : ℕ) (hr : r ∈ tail.registryIds) : r ∈ (MatchingMemberTree.blossom p n child tail).registryIds := by
      simp [MatchingMemberTree.registryIds,hr]
    refine ⟨by simpa only [MatchingMemberTree.relabel_arity] using (headers n here).2.trans count,?_,
      ci childProper encChild (fun j h => headers j (inChild j h)) (fun j h => newKeys j (inChild j h)),
      ti tailProper encTail (fun j h => headers j (inTail j h)) (fun j h => newKeys j (inTail j h))⟩
    intro i hi
    have labels := child.relabel_keys childProper f
    have bounded : i < child.rootKeys.length := by simpa [labels] using hi
    have slot := keys i bounded
    have fit : i < s.nm (s.nr 78+n) := by rw [count]; simpa using bounded
    have changed := newKeys n here i fit
    dsimp only at changed
    have start := (headers n here).1
    have old : ((matchingRebaseRowsAt s s n i).representative,(matchingRebaseRowsAt s s n i).node) = child.rootKeys[i] := slot
    rw [old] at changed
    change (t.nm (matchingCycleRecordStart t n + 4*i), t.nm (matchingCycleRecordStart t n + 4*i+1)) = _
    rw [start]
    simpa only [labels,List.getElem_map,matchingRebaseRowsAt,matchingCycleChildAt] using changed


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseRegisteredTree

/-! matching/MatchingRebasePersistentPorts.lean -/
section RppSource_MatchingRebasePersistentPorts
namespace VehicleRoutingSurvey.Routing

/-- New representatives rename the same child blocks. Old ownership
decodes each new name since that original lies inside its own child. -/
def MatchingExpansionChildPorts.relabel {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {B : Finset (Fin k)} (e : MatchingExpansionChildPorts old B)
    (sameCuts : next.cuts = old.cuts) (choose : Fin k → Fin k)
    (inside : ∀ q ∈ e.ports, choose q ∈ e.block q) : MatchingExpansionChildPorts next B := by
  let target := e.ports.image choose
  let block (v : Fin k) := e.block (e.owner v)
  let owner (v : Fin k) := choose (e.owner v)
  have inverse (p : Fin k) (hp : p ∈ e.ports) : e.owner (choose p) = p :=
    e.unique _ hp _ (inside p hp)
  refine ⟨target,block,owner,?_,?_,?_,?_,?_⟩
  · intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    simpa only [block,inverse p hp] using inside p hp
  · intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    simpa only [block,inverse p hp] using e.subset p hp
  · intro v hv
    obtain ⟨listed,here⟩ := e.covered v hv
    exact ⟨Finset.mem_image_of_mem _ listed, by simpa only [block,owner,inverse _ listed] using here⟩
  · intro q hq v hv
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    have belongs : v ∈ e.block p := by simpa only [block,inverse p hp] using hv
    exact congrArg choose (e.unique p hp v belongs)
  · intro q hq many
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    rw [sameCuts]
    simpa only [block,inverse p hp] using e.live p hp (by simpa only [block,inverse p hp] using many)

theorem MatchingExpansionChildPorts.relabel_injective {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {B : Finset (Fin k)} (e : MatchingExpansionChildPorts old B)
    (choose : Fin k → Fin k) (inside : ∀ q ∈ e.ports, choose q ∈ e.block q) :
    Set.InjOn choose (e.ports : Set (Fin k)) := by
  intro p hp q hq eq
  exact (e.unique p hp _ (inside p hp)).symm.trans ((congrArg e.owner eq).trans (e.unique q hq _ (inside q hq)))

theorem MatchingLiveCycle.relabel_members {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    (e : MatchingLiveCycle old node B) (sameCuts : next.cuts = old.cuts)
    (choose : Fin k → Fin k) (inside : ∀ q ∈ e.ports.ports, choose q ∈ e.ports.block q)
    (f : ℕ → ℕ → ℕ) (labels : ∀ j ∈ e.tree.jobs none, ∀ p : Fin k, j.representative = p.val →
      (j.relabel f).representative = (choose p).val) :
    MatchingChildMemberTree (e.ports.relabel sameCuts choose inside) (e.tree.relabel f) := by
  refine ⟨?_,?_⟩
  · intro v hv
    let p := e.ports.owner v
    have wanted := (e.ports.covered v hv).1
    have on : p ∈ e.geometry.cycle := List.mem_toFinset.mp (e.geometry.ports ▸ wanted)
    obtain ⟨i,hi,key⟩ := List.mem_iff_getElem.mp on
    have count := (e.tree.jobs_length none).trans e.arity
    have index : i < (e.tree.jobs none).length := count.symm ▸ hi
    let j := (e.tree.jobs none)[i]'index
    have key' : j.representative = p.val := (e.jobKey _ index).trans (congrArg Fin.val key)
    have oldLeaf := ((e.owner j (List.getElem_mem index) p key').2 v).mpr (e.ports.covered v hv).2
    let newJ := j.relabel f
    have listed : newJ ∈ (e.tree.relabel f).jobs none := by
      rw [e.tree.relabel_jobs]
      exact List.mem_map.mpr ⟨j,List.getElem_mem index,rfl⟩
    have hasLeaf : v.val ∈ newJ.tree.leaves := by simpa only [newJ,MatchingMemberJob.relabel_leaves] using oldLeaf
    have seen : v.val ∈ newJ.assignments.map Prod.fst := newJ.assignments_vertices.symm ▸ hasLeaf
    obtain ⟨pair,hp,atV⟩ := List.mem_map.mp seen
    have pairOwner : pair.2 = newJ.owner := by
      cases form : newJ.children with
      | none => simp [MatchingMemberJob.assignments,form] at hp; exact congrArg Prod.snd hp
      | some sub =>
        obtain ⟨x,_,eq⟩ := List.mem_map.mp (show pair ∈ sub.leaves.map (fun x => (x,newJ.owner)) by simpa [MatchingMemberJob.assignments,form] using hp)
        exact (congrArg Prod.snd eq).symm
    have newOwner : newJ.owner = (choose p).val :=
      ((e.tree.relabel f).jobs_owner none newJ listed).trans (labels j (List.getElem_mem index) p key')
    have target : pair = (v.val,(choose p).val) := Prod.ext atV (pairOwner.trans newOwner)
    exact List.mem_flatMap.mpr ⟨newJ,listed,target ▸ hp⟩
  · intro v hv
    simpa only [MatchingMemberTree.relabel_leaves] using e.geometry.members.absent v hv


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebasePersistentPorts

/-! matching/MatchingRebaseUpdatedGeometry.lean -/
section RppSource_MatchingRebaseUpdatedGeometry
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

private theorem alternatingEdges_map_original {k : ℕ} (f : Fin k → Fin k) (vertices : List (Fin k)) :
    alternatingEdges (vertices.map f) = (alternatingEdges vertices).map (Sym2.map f) := by
  induction vertices using List.twoStepInduction with
  | nil => rfl
  | singleton v => rfl
  | cons_cons v w tail ih _ => simp only [List.map_cons,alternatingEdges,Sym2.map_mk,ih]

private theorem matchingRotateMap {k : ℕ} (f : Fin k → Fin k) (vertices : List (Fin k)) (i : ℕ) :
    (vertices.map f).rotate i = (vertices.rotate i).map f := by
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp only [List.getElem_rotate,List.getElem_map,List.length_map]

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

/-- Renaming each child by its chosen original commutes with cyclic rotation
and turns the projected alternating tail into actual original matched edges. -/
noncomputable def MatchingLiveCycle.updatedGeometry {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    (e : MatchingLiveCycle old node B) {p : Fin k} (choose : MatchingCycleLiftPorts e p)
    (sameCuts : next.cuts = old.cuts) (potential : next.potential = old.potential) (cutDual : next.cutDual = old.cutDual)
    (f : ℕ → ℕ → ℕ) (labels : ∀ j ∈ e.tree.jobs none, ∀ q : Fin k, j.representative = q.val →
      (j.relabel f).representative = (choose.choose q).val)
    (global : (rematchBlossomCycle e.geometry.cycle choose.free.val).image (Sym2.map choose.choose) ⊆ next.edges) :
    MatchingExpansionGeometry (e.ports.relabel sameCuts choose.choose choose.members) (e.tree.relabel f) p := by
  let g := e.geometry
  let names := g.cycle.map choose.choose
  let edges (i : Fin names.length) := g.edges ⟨i.val, by simpa [names] using i.isLt⟩
  let base : Fin names.length := ⟨choose.free.val, by
    change choose.free.val < (e.geometry.cycle.map choose.choose).length
    rw [List.length_map]
    exact choose.free.isLt⟩
  let rest := (g.cycle.rotate choose.free.val).tail
  have atIndex (i : Fin names.length) :
      names.get i = choose.choose (g.cycle.get ⟨i.val, by simpa [names] using i.isLt⟩) :=
    List.getElem_map choose.choose
  have first : (g.cycle.rotate choose.free.val).head? = some (g.cycle.get choose.free) := by
    simpa only [g, List.get_eq_getElem, List.getElem?_eq_getElem choose.free.isLt] using
      List.head?_rotate choose.free.isLt
  have shape : g.cycle.rotate choose.free.val = g.cycle.get choose.free :: rest := by
    obtain ⟨tail,eq⟩ := List.head?_eq_some_iff.mp first
    simpa [rest,eq] using eq
  have within (i : Fin g.cycle.length) : g.cycle.get i ∈ e.ports.ports :=
    g.ports.symm ▸ List.mem_toFinset.mpr (List.get_mem ..)
  have decode (i : Fin g.cycle.length) : e.ports.owner (choose.choose (g.cycle.get i)) = g.cycle.get i :=
    e.ports.unique _ (within i) _ (choose.members _ (within i))
  let ports := e.ports.relabel sameCuts choose.choose choose.members
  have distinct : names.Nodup := List.Nodup.map_on (fun a ha b hb same =>
    e.ports.relabel_injective choose.choose choose.members (g.ports.symm ▸ List.mem_toFinset.mpr ha)
      (g.ports.symm ▸ List.mem_toFinset.mpr hb) same) g.distinct
  refine ⟨e.relabel_members sameCuts choose.choose choose.members f labels,names,edges,base,rest.map choose.choose,
    distinct,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [names] using g.odd
  · change (g.cycle.map choose.choose).rotate choose.free.val = _
    rw [matchingRotateMap,shape,List.map_cons,choose.exposed]
  · exact (atIndex base).trans choose.exposed
  · ext v
    change v ∈ e.ports.ports.image choose.choose ↔ v ∈ names.toFinset
    simp [g.ports,names]
  · intro i
    change (edges i).1 ∈ e.ports.block (e.ports.owner (names.get i))
    rw [atIndex,decode]
    exact g.source _
  · intro i
    let j : Fin g.cycle.length := ⟨i.val,by simpa [names] using i.isLt⟩
    let successor : Fin names.length := ⟨(i.val+1)%names.length,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    change (edges i).2 ∈ e.ports.block (e.ports.owner (names.get successor))
    rw [atIndex,decode]
    simpa only [successor,names,List.length_map,edges,j] using g.target j
  · intro i
    change oddCutDualEdgeValue next.cuts next.potential next.cutDual _ = _
    rw [sameCuts,potential,cutDual]
    exact g.tight _
  · intro a b h
    rw [alternatingEdges_map_original] at h
    obtain ⟨edge, used, eq⟩ := List.mem_map.mp h
    have picked := global (Finset.mem_image.mpr ⟨edge,List.mem_toFinset.mpr used,eq⟩)
    exact ⟨next.partialMate_some_iff.mpr picked,next.partialMate_some_iff.mpr (Sym2.eq_swap ▸ picked)⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseUpdatedGeometry

/-! matching/MatchingPairMeaning.lean -/
section RppSource_MatchingPairMeaning
namespace VehicleRoutingSurvey.Routing





theorem matchingPairSlot_lt {k : ℕ} (a b : Fin k) : k*a.val+b.val < k*k := by
  have bound := Nat.mul_le_mul_left k (Nat.succ_le_of_lt a.isLt)
  rw [Nat.mul_succ] at bound
  have hb := b.isLt
  omega





theorem normalizedOuterPairEntries_mem {k : ℕ} {rep : Fin k → Fin k} {cost : Fin k → Fin k → ℝ}
    {effective : Fin k → ℝ} {time : ℝ} {a b : Fin k} {d : DualSlack (MatchingDualEvent k)} :
    d ∈ normalizedOuterPairEntries rep cost effective time a b ↔
      ∃ u v : Fin k, rep u = a ∧ rep v = b ∧ normalizedOuterEdge cost effective time u v = d := by
  simp only [normalizedOuterPairEntries, List.mem_flatMap, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq, List.mem_map]
  constructor
  · rintro ⟨u, hu, v, hv, found⟩
    exact ⟨u, v, hu, hv, found⟩
  · rintro ⟨u, v, hu, hv, found⟩
    exact ⟨u, hu, v, hv, found⟩



theorem normalizedOuterEdge_advance {k : ℕ} (cost : Fin k → Fin k → ℝ) (before after : Fin k → ℝ)
    (time delta : ℝ) (u v : Fin k) (left : after u = before u + delta)
    (right : after v = before v + delta) :
    normalizedOuterEdge cost after (time+delta) u v = normalizedOuterEdge cost before time u v := by
  have same : (time+delta)+(time+delta)+(cost u v-after u-after v) = time+time+(cost u v-before u-before v) := by
    rw [left, right]
    ring
  simp only [normalizedOuterEdge, same]

/-- Both outer endpoints gain the dual increment, which cancels the increment
to the common normalization offset. The physical pair cache can stay in place. -/
theorem MatchingSearchOuterBuckets.advance {k : ℕ} {s t : ArithmeticState} {rep : Fin k → Fin k}
    {role : Fin k → ℕ} {cost : Fin k → Fin k → ℝ} {before after : Fin k → ℝ}
    (cached : MatchingSearchOuterBuckets s rep role cost before) (delta : ℝ)
    (time : t.rr 15 = s.rr 15 + delta) (effective : ∀ v, role (rep v) = 1 → after v = before v + delta)
    (valid : ∀ i < k*k, MatchingPairBucketValid k t i)
    (stored : ∀ i < k*k, readMatchingPairBucket (k := k) t i = readMatchingPairBucket (k := k) s i) :
    MatchingSearchOuterBuckets t rep role cost after := by
  refine ⟨valid, ?_, fun a b off => (stored _ (matchingPairSlot_lt a b)).trans (cached.inactive a b off)⟩
  intro a b distinct left right
  have slot : k*a.val+b.val < k*k := by
    have aBound := Nat.mul_le_mul_left k (Nat.succ_le_of_lt a.isLt)
    rw [Nat.mul_succ] at aBound
    have bBound := b.isLt
    omega
  rw [time, stored _ slot]
  have h := cached.least a b distinct left right
  have same (d : DualSlack (MatchingDualEvent k)) :
      d ∈ normalizedOuterPairEntries rep cost after (s.rr 15+delta) a b ↔
      d ∈ normalizedOuterPairEntries rep cost before (s.rr 15) a b := by
    rw [normalizedOuterPairEntries_mem, normalizedOuterPairEntries_mem]
    constructor
    · rintro ⟨u,v,hu,hv,datum⟩
      have agrees := normalizedOuterEdge_advance cost before after (s.rr 15) delta u v
        (effective u (by rwa [hu])) (effective v (by rwa [hv]))
      exact ⟨u,v,hu,hv,agrees.symm.trans datum⟩
    · rintro ⟨u,v,hu,hv,datum⟩
      have agrees := normalizedOuterEdge_advance cost before after (s.rr 15) delta u v
        (effective u (by rwa [hu])) (effective v (by rwa [hv]))
      exact ⟨u,v,hu,hv,agrees.trans datum⟩
  exact ⟨fun present => (same _).mpr (h.sound present), fun d present => h.covers d ((same _).mp present)⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingPairMeaning

/-! matching/MatchingDualCacheFrame.lean -/
section RppSource_MatchingDualCacheFrame
namespace VehicleRoutingSurvey.Routing

/-- Only the effective vertex table and the cut duals change during the
numerical update. The entire cache sits in the interval between them. -/
theorem matchingEventDualMemory_between {s : ArithmeticState} {a : ℕ}
    (below : s.nr 62+s.nr 55 ≤ a) (above : a < s.nr 75) :
    iterateBlossomDuals {s with rm := advancedEffectiveMemory s} (s.nr 55) a = s.rm a := by
  have untouched := iterateBlossomDuals_keeps_address {s with rm := advancedEffectiveMemory s} (s.nr 55) a
    (fun i _ _ _ => (show a ≠ s.nr 75 + blossomNodeAt s i by omega))
  exact untouched.trans (if_neg (fun range => (Nat.not_lt_of_ge below) range.2))

theorem advanceMatchingEventDuals_cache {k : ℕ} {s t : ArithmeticState} {ticks : ℕ}
    (cutAt : Fin k → Finset (Fin k)) (layout : MatchingCacheLayout k s)
    (lower : s.nr 62+k ≤ s.nr 59) (upper : s.nr 66+k*k ≤ s.nr 75)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (run : BlockRuns advanceMatchingEventDuals ticks s t) :
    (∀ i < s.nr 61, (MatchingCandidateRowValid cutAt t i ↔ MatchingCandidateRowValid cutAt s i) ∧
      readMatchingCandidate cutAt t i = readMatchingCandidate cutAt s i) ∧
    (∀ i < k*k, (MatchingPairBucketValid k t i ↔ MatchingPairBucketValid k s i) ∧
      readMatchingPairBucket (k := k) t i = readMatchingPairBucket s i) := by
  obtain ⟨u, _, _, checked, _, nm, _, _, _, ports, rm⟩ := advanceMatchingEventDuals_spec s entry running one
  have eq := (checked.same_exit run).2
  subst u
  have fixed (r : ℕ) (safe : r ∉ [0,6,7,10,11,12,14] := by decide) := ports r safe
  have first := layout.slacksBefore
  have last := layout.ratesBefore
  have dim := layout.dimension
  have between (a : ℕ) (lo : s.nr 59 ≤ a) (hi : a < s.nr 75) : t.rm a = s.rm a := by
    rw [rm, matchingEventDualMemory_between (by omega) hi]
  constructor
  · intro i hi
    simp only [MatchingCandidateRowValid, readMatchingCandidate, decodeMatchingDictionaryEvent, nm,
      fixed 54, fixed 58, fixed 59, fixed 60, between (s.nr 59+i) (by omega) (by omega),
      between (s.nr 60+i) (by omega) (by omega), iff_self, and_self]
  · intro i hi
    simp only [MatchingPairBucketValid, readMatchingPairBucket, nm, fixed 65, fixed 66,
      between (s.nr 66+i) (by omega) (by omega), iff_self, and_self]

/-- The dual update keeps all data read by the cache scanner and replaces
the effective potentials by precisely the new mathematical values. -/
theorem MatchingRefreshInput.dualStep {k : ℕ} {s t : ArithmeticState} {ticks : ℕ}
    {rep : Fin k → Fin k} {role : Fin k → ℕ} {cost : Fin k → Fin k → ℝ} {eff after : Fin k → ℝ}
    (old : MatchingRefreshInput s rep role cost eff)
    (metric : s.nr 20+k*k ≤ s.nr 62) (separate : s.nr 62 ≤ s.nr 75)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (run : BlockRuns advanceMatchingEventDuals ticks s t)
    (effective : ∀ v : Fin k, t.rm (t.nr 62+v.val) = after v) : MatchingRefreshInput t rep role cost after := by
  obtain ⟨u, _, _, checked, _, nm, _, _, _, ports, rm⟩ := advanceMatchingEventDuals_spec s entry running one
  have eq := (checked.same_exit run).2
  subst u
  have fixed (r : ℕ) (safe : r ∉ [0,6,7,10,11,12,14] := by decide) := ports r safe
  refine ⟨old.layout.keeps (fun r hi => fixed r (by simp; omega)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, effective⟩
  · rw [fixed 21, fixed 58]; exact old.offsetsBefore
  · rw [fixed 57, fixed 58]; exact old.representativesBefore
  · rw [fixed 51, fixed 58]; exact old.rolesBefore
  · rw [fixed 20, fixed 59]; exact old.metricBefore
  · rw [fixed 62, fixed 59]; exact old.effectiveBefore
  · intro v; rw [nm, fixed 21]; exact old.offsets v
  · intro v; rw [nm, fixed 57]; exact old.representatives v
  · intro v; rw [nm, fixed 51]; exact old.roles v
  · intro i j
    have cap := Nat.mul_le_mul_left k (Nat.succ_le_of_lt i.isLt)
    rw [Nat.mul_succ] at cap
    have small := j.isLt
    rw [fixed 20, rm, matchingEventDualMemory_keeps_prefix s (s.nr 62) _ (by omega) le_rfl separate]
    exact old.metric i j


end VehicleRoutingSurvey.Routing
end RppSource_MatchingDualCacheFrame

/-! matching/MatchingAdvancedStage.lean -/
section RppSource_MatchingAdvancedStage
namespace VehicleRoutingSurvey.Routing



theorem MatchingChosenStage.advance {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {cutAt : Fin k → Finset (Fin k)}
    {original s : ArithmeticState} (chosen : MatchingChosenStage part forest positive cutAt original s)
    (search : CompactMatchingSearchForest part forest state.partialMate part.tightBetween)
    (internal : state.InternalCuts) (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (storage : MatchingStageStorage k original s) :
    let bound : DualBound (MatchingDualEvent k) := ⟨chosen.event, s.rr 1⟩
    let next := state.advanceSearch part search positive internal bound chosen.adjustment
    let nextPart := part.advanceSearch search positive internal bound chosen.adjustment
    ∃ t ticks, BlockRuns advanceMatchingEventDuals ticks s t ∧ ticks ≤ 31*k+6 ∧ t.halted = false ∧
      t.nr 14 = 0 ∧ t.nm = s.nm ∧ (∀ r ∉ ([0,6,7,10,11,12,14] : List ℕ), t.nr r = s.nr r) ∧
      ∃ out : MatchingAdvancedStage nextPart forest positive cutAt original t,
        out.dual.node = chosen.dual.node ∧ out.registry.trees.tree = chosen.registry.trees.tree := by
  intro bound next nextPart
  obtain ⟨t, ticks, limit, run, live, primal, ⟨dual, ids⟩, nm, _, clock, zero, ports⟩ :=
    advanceMatchingEventDuals_refines entry running one chosen.primal chosen.dual search positive internal
      storage.inputFloor.symm.le chosen.event chosen.adjustment
  have fixed (r : ℕ) (safe : r ∉ [0,6,7,10,11,12,14] := by decide) := ports r safe
  have word (v : Fin k) : matchingForestWitnessAt t.nm (t.nr 90) v.val = matchingForestWitnessAt s.nm (s.nr 90) v.val := by
    rw [nm, fixed 90]
  obtain ⟨witness, nextSearch⟩ := MatchingForestOriginalWitnesses.advance (part := part) (forest := forest) chosen.witnesses search positive internal bound chosen.adjustment word
  have top (v : Fin k) : blossomNodeAt t v = blossomNodeAt s v := by rw [blossomNodeAt, nm, fixed 74]; rfl
  let registry : MatchingRegistryView dual := chosen.registry.reindex ids rfl rfl (fixed 77) (fixed 78) (fixed 76)
    (fixed 65) top (fun a _ => congrFun nm a)
  obtain ⟨rows, buckets⟩ := advanceMatchingEventDuals_cache cutAt chosen.reads.layout chosen.reads.effectiveBefore storage.cutDuals.ge
    entry running one run
  have eff := chosen.reads.dualStep storage.metricBelowInput ((Nat.le_add_right _ k).trans chosen.dual.separated)
    entry running one run dual.effective
  have pairs := chosen.pairs.advance (after := effectiveVertexPotential next.cuts next.potential next.cutDual)
    (s.rr 1) clock (by
      intro v on
      rw [show effectiveVertexPotential next.cuts next.potential next.cutDual v = _ from
        effectiveVertexPotential_shift part.blocks (part.dualLabel forest positive) state.potential state.cutDual
          (s.rr 1) (Finset.mem_univ v), part.dualLabel_block]
      cases h : forest.role (part.representative v) <;>
        simp_all [alternatingRoleCode, AlternatingForestRole.dualDirection])
    (fun i hi => (buckets i hi).1.mpr (chosen.pairs.valid i hi)) (fun i hi => (buckets i hi).2)
  refine ⟨t, ticks, run, limit, live, zero, nm, ports, ⟨primal, nextSearch, witness, chosen.links.advance rfl word,
    dual, registry, eff, pairs, ?_, ?_⟩, ids, rfl⟩
  · intro i hi
    have before := fixed 61 ▸ hi
    exact (rows i before).1.mpr (chosen.valid i before)
  · intro g
    rw [(rows g.slot (chosen.reads.layout.rows.symm ▸ g.slot_lt)).2]
    exact chosen.least g


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAdvancedStage

/-! matching/MatchingContractionDualSnapshot.lean -/
section RppSource_MatchingContractionDualSnapshot
namespace VehicleRoutingSurvey.Routing





/-- This proof view keeps the trace arguments available while exposing the
dual values and normalized caches at the new numerical point. -/
theorem MatchingChosenStage.contractionDualSnapshot
    {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {cutAt : Fin k → Finset (Fin k)}
    {original s : ArithmeticState} (chosen : MatchingChosenStage part forest positive cutAt original s)
    (search : CompactMatchingSearchForest part forest state.partialMate part.tightBetween)
    (internal : state.InternalCuts) (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 9 = 1) (storage : MatchingStageStorage k original s) :
    let bound : DualBound (MatchingDualEvent k) := ⟨chosen.event, s.rr 1⟩
    let nextPart := part.advanceSearch search positive internal bound chosen.adjustment
    ∃ advanced : MatchingAdvancedStage nextPart forest positive cutAt original
        (matchingContractionDualSnapshot s),
      advanced.dual.node = chosen.dual.node ∧ advanced.registry.trees.tree = chosen.registry.trees.tree := by
  intro bound nextPart
  obtain ⟨t, _, run, _, _, _, natural, regs, view, ids, trees⟩ :=
    chosen.advance search internal entry running one storage
  obtain ⟨u, _, _, exactRun, _, _, _, clock, _, _, values⟩ :=
    advanceMatchingEventDuals_spec s entry running one
  have same := (run.same_exit exactRun).2
  subst u
  let snap := matchingContractionDualSnapshot s
  have port (r : ℕ) (safe : r ∉ ([0,6,7,10,11,12,14] : List ℕ) := by decide) :
      snap.nr r = t.nr r := (regs r safe).symm
  have tables (r : ℕ) (used : r ∈ matchingRefreshTableRegisters) : snap.nr r = t.nr r :=
    port r (by simp [matchingRefreshTableRegisters] at used; simp; omega)
  have nm : snap.nm = t.nm := natural.symm
  have rm : snap.rm = t.rm := values.symm
  have time : snap.rr 15 = t.rr 15 := by simpa [snap, matchingContractionDualSnapshot] using clock.symm
  have reads := view.reads.keeps (t := snap)
    ⟨fun a _ => congrFun nm a, fun a _ _ _ => congrFun rm a⟩ tables
  let dual : MatchingSearchDualMemory nextPart forest snap := {
    dimension := reads.layout.dimension
    separated := by rw [port 62, port 75]; exact view.dual.separated
    reps := reads.representatives
    roles := by rw [port 51, nm]; exact view.dual.roles
    effective := reads.potentials
    node := view.dual.node
    nodeNonzero := view.dual.nodeNonzero
    nodeInjective := view.dual.nodeInjective
    cutValues B h := by rw [port 75, rm]; exact view.dual.cutValues B h
    top v := by simpa only [blossomNodeAt, port 74, nm] using view.dual.top v }
  let registry := view.registry.transport (new := dual) rfl (port 77) (port 78) (port 76)
    (port 65) (fun v => by simp only [blossomNodeAt, port 74, nm]) (fun a _ => congrFun nm a)
  have primal : CompactMatchingPrimalDualMemory _ original snap := {
    dimension := reads.layout.dimension
    oddMap := (port 56).trans view.primal.oddMap
    mateAbove := by rw [port 50]; exact view.primal.mateAbove
    mate v := by rw [port 50, nm]; exact view.primal.mate v
    saved r hi := (port r (by simp; omega)).trans (view.primal.saved r hi)
    natural a low := (congrFun nm a).trans (view.primal.natural a low)
    real a low := (congrFun rm a).trans (view.primal.real a low) }
  have words (v : Fin k) : matchingForestWitnessAt snap.nm (snap.nr 90) v.val =
      matchingForestWitnessAt t.nm (t.nr 90) v.val := by rw [port 90, nm]
  have rows := (matchingCacheReads_unchanged cutAt nm rm tables).1
  have keys := (matchingCacheReads_unchanged cutAt nm rm tables).2
  refine ⟨⟨primal, view.search, ?_, view.links.advance rfl words, dual, registry, reads,
    ⟨fun i hi => (keys i).1.symm ▸ view.pairs.valid i hi, ?_, ?_⟩,
    fun i hi => (rows i).1.symm ▸ view.valid i (port 61 ▸ hi),
    fun g => (rows g.slot).2.symm ▸ view.least g⟩, ids, trees⟩
  · intro child parent link
    obtain ⟨a, b, word, parentAt, childAt, tight⟩ := view.witnesses link
    exact ⟨a, b, (words child).trans word, parentAt, childAt, tight⟩
  · intro a b diff ha hb
    rw [time, (keys _).2]
    exact view.pairs.least a b diff ha hb
  · intro a b off
    exact (keys _).2.trans (view.pairs.inactive a b off)





end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionDualSnapshot

/-! matching/MatchingRebaseMatchedRows.lean -/
section RppSource_MatchingRebaseMatchedRows
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The forward row for a matched pair still identifies its saved original
edge after the children of a blossom receive new ports. -/
theorem MatchingCycleLiftPorts.updatedMatchedRow {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ}
    {B : Finset (Fin k)} {p : Fin k} {e : MatchingLiveCycle old node B}
    (choose : MatchingCycleLiftPorts e p) (size : 2 ≤ e.geometry.cycle.length)
    (root : matchingCutPort next B p)
    (global : (rematchBlossomCycle e.geometry.cycle choose.free.val).image (Sym2.map choose.choose) ⊆ next.edges) :
    let cycle := e.geometry.cycle
    let port := fun i : Fin cycle.length => choose.choose (cycle.get i)
    ∀ i : Fin cycle.length,
      let j : Fin cycle.length := ⟨(i.val+1)%cycle.length, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
      next.partialMate (port i) = some (port j) → e.geometry.edges i = (port i,port j) := by
  intro cycle port i j mate
  have inside (v : Fin cycle.length) : cycle.get v ∈ e.ports.ports :=
    e.geometry.ports.symm ▸ List.mem_toFinset.mpr (List.get_mem cycle v)
  have inB (v : Fin cycle.length) : port v ∈ B :=
    e.ports.subset _ (inside v) (choose.members _ (inside v))
  have fresh : i.val ≠ choose.free.val := by
    intro eq
    have atRoot : port i = p := (congrArg port (Fin.ext eq)).trans choose.exposed
    have matched := next.partialMate_some_iff.mp mate
    have all : ∀ v ∈ s(port i,port j), v ∈ B := by
      intro v hv
      rcases Sym2.mem_iff.mp hv with atLeft | atRight
      · exact atLeft.symm ▸ inB i
      · exact atRight.symm ▸ inB j
    exact root.2 _ matched (atRoot ▸ Sym2.mem_mk_left _ _) all
  obtain ⟨r,hr,side,whereAt⟩ := (matchingRebaseChildIndex_complete choose.free.isLt e.geometry.odd).2.1
    i.val i.isLt fresh
  let idx (side : Bool) : Fin cycle.length :=
    ⟨matchingRebaseChildIndex cycle.length choose.free.val r side, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
  have existing : s(port (idx false),port (idx true)) ∈ next.edges := by
    apply global
    refine Finset.mem_image.mpr ⟨s(cycle.get (idx false),cycle.get (idx true)), ?_, rfl⟩
    exact (rematchBlossomCycle_mem_iff_physicalPair cycle choose.free.isLt _).mpr ⟨r,hr,rfl⟩
  have edge : e.geometry.edges (idx false) = (port (idx false),port (idx true)) :=
    (choose.pairs r hr).symm
  have iAt : idx side = i := Fin.ext whereAt
  have step : ((idx false).val+1)%cycle.length = (idx true).val := by
    change (((choose.free.val+(2*r+1))%cycle.length)+1)%cycle.length = (choose.free.val+(2*r+2))%cycle.length
    rw [Nat.mod_add_mod]
    exact congrArg (· % cycle.length) (by omega)
  cases side with
  | false =>
    have atRight : idx true = j := Fin.ext (step.symm.trans (congrArg (fun z : Fin cycle.length =>
      (z.val+1)%cycle.length) iAt))
    rw [← iAt, ← atRight]
    exact edge
  | true =>
    have back : next.partialMate (port (idx true)) = some (port (idx false)) :=
      next.partialMate_some_iff.mpr (Sym2.eq_swap ▸ existing)
    have samePort : port (idx false) = port j :=
      Option.some.inj (back.symm.trans ((congrArg (fun v => next.partialMate (port v)) iAt).trans mate))
    have sameVertex := e.ports.relabel_injective choose.choose choose.members (inside (idx false)) (inside j) samePort
    have sameIdx : (idx false).val = j.val :=
      (List.Nodup.getElem_inj_iff e.geometry.distinct).mp sameVertex
    have wrap : (((idx false).val+1)%cycle.length+1)%cycle.length = (idx false).val := by
      rw [step, show (idx true).val = i.val from congrArg Fin.val iAt]
      exact sameIdx.symm
    rw [Nat.mod_add_mod] at wrap
    have long : 3 ≤ cycle.length := by
      have atLeast : 2 ≤ cycle.length := size
      obtain ⟨n, hn⟩ := e.geometry.odd
      change cycle.length = 2*n+1 at hn
      omega
    have bound := (idx false).isLt
    by_cases fits : (idx false).val+1+1 < cycle.length
    · rw [Nat.mod_eq_of_lt fits] at wrap
      omega
    · have upper : (idx false).val+1+1-cycle.length < cycle.length := by omega
      rw [Nat.mod_eq_sub_mod (by omega : cycle.length ≤ (idx false).val+1+1), Nat.mod_eq_of_lt upper] at wrap
      omega


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseMatchedRows

/-! matching/MatchingAugmentCycleShape.lean -/
section RppSource_MatchingAugmentCycleShape
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The rebased shape of a live cut, including the exact label that appears
in each child row and the saved crossings used by the new matching. -/
structure MatchingAugmentCycleShape {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ}
    {B : Finset (Fin k)} (e : MatchingLiveCycle old node B)
    (nodePort : ℕ → ℕ) where
  base : Fin k
  belongs : base ∈ B
  portWord : nodePort (node B) = base.val
  choose : MatchingCycleLiftPorts e base
  internal : IsPerfectMatchingOn (B.erase base) (matchingCycleInterior next B base)
  labels : ∀ j ∈ e.tree.jobs none, ∀ q : Fin k, j.representative = q.val →
    j.liftPort nodePort = (choose.choose q).val
  crossing : (rematchBlossomCycle e.geometry.cycle choose.free.val).image (Sym2.map choose.choose) ⊆ next.edges

theorem MatchingLiveCycle.base_mem {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ}
    {B : Finset (Fin k)} (e : MatchingLiveCycle old node B) : e.base ∈ B := by
  have label : e.geometry.cycle.get e.geometry.baseSlot = e.base := e.geometry.atBase
  have member : e.geometry.cycle.get e.geometry.baseSlot ∈ e.geometry.cycle :=
    List.get_mem e.geometry.cycle e.geometry.baseSlot
  rw [label] at member
  have listed : e.base ∈ e.ports.ports := e.geometry.ports.symm ▸ List.mem_toFinset.mpr member
  exact e.ports.subset _ listed (e.ports.containsPort _ listed)

theorem MatchingCycleLiftDerivation.internalMatching {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ}
    {lookup : ∀ B ∈ old.cuts, MatchingLiveCycle old node B} {B : Finset (Fin k)}
    {p : Fin k} {E : Finset (Sym2 (Fin k))} (found : MatchingCycleLiftDerivation lookup B p E) :
    IsPerfectMatchingOn (B.erase p) E := by
  cases found with
  | join _ _ _ perfect _ _ _ => exact perfect

/-- A reached node has the exact port selected by the recursive lift. -/
noncomputable def MatchingLiveCycles.liftedCycleShape {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (cycles : MatchingLiveCycles registry) {B : Finset (Fin k)} (live : B ∈ old.cuts)
    (reached : matchingAugmentDerivedCut cycles.entry next B) :
    MatchingAugmentCycleShape (next := next) (cycles.entry B live)
      (matchingAugmentNodePort next old.cuts dual.node) := by
  let p := reached.choose
  have inside : p ∈ B := reached.choose_spec.choose
  have selected : ∃ F, F ⊆ next.edges ∧ MatchingCycleLiftDerivation cycles.entry B p F :=
    reached.choose_spec.choose_spec
  let E := selected.choose
  have included : E ⊆ next.edges := selected.choose_spec.1
  have used : MatchingCycleLiftDerivation cycles.entry B p E := selected.choose_spec.2
  let e := cycles.entry B live
  let data := used.nodeData cycles live inside included
  let chosen := data.2.choose
  have details := data.2.choose_spec
  refine ⟨p,inside,data.1,chosen,?_,?_,?_⟩
  · rw [matchingCycleInterior_eq used.internalMatching included]
    exact used.internalMatching
  · intro j listed q key
    obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp listed
    subst j
    have atKey : e.geometry.cycle.get ⟨i,((e.tree.jobs_length none).trans e.arity) ▸ hi⟩ = q :=
      Fin.ext ((e.jobKey i hi).symm.trans key)
    have table := details.1 i hi
    change matchingRebasePortAt e.tree (MatchingMemberJob.liftPort (matchingAugmentNodePort next old.cuts dual.node)) i =
      (chosen.choose (e.geometry.cycle.get ⟨i, ((e.tree.jobs_length none).trans e.arity) ▸ hi⟩)).val at table
    rw [matchingRebasePortAt, dif_pos hi, atKey] at table
    exact table
  · intro edge present
    obtain ⟨pair,paired,rfl⟩ := Finset.mem_image.mp present
    obtain ⟨i,hi,eq⟩ := (rematchBlossomCycle_mem_iff_physicalPair e.geometry.cycle chosen.free.isLt pair).mp paired
    let idx (side : Bool) : Fin e.geometry.cycle.length :=
      ⟨matchingRebaseChildIndex e.geometry.cycle.length chosen.free.val i side,
        Nat.mod_lt _ (Nat.zero_lt_of_lt chosen.free.isLt)⟩
    have crossing : (chosen.choose (e.geometry.cycle.get (idx false)),chosen.choose (e.geometry.cycle.get (idx true))) =
        e.geometry.edges (idx false) := chosen.pairs i hi
    rw [eq, Sym2.map_mk]
    change s(chosen.choose (e.geometry.cycle.get (idx false)),chosen.choose (e.geometry.cycle.get (idx true))) ∈ next.edges
    have endpointEq := congrArg (fun z : Fin k × Fin k => s(z.1,z.2)) crossing
    exact endpointEq.symm ▸ details.2.1 i hi

/-- A cut outside the path keeps its old base and every old child label. -/
noncomputable def MatchingLiveCycles.retainedCycleShape {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (cycles : MatchingLiveCycles registry) {B : Finset (Fin k)} (live : B ∈ old.cuts)
    (unchanged : ∀ edge : Sym2 (Fin k), (∀ v ∈ edge, v ∈ B) → (edge ∈ next.edges ↔ edge ∈ old.edges)) :
    MatchingAugmentCycleShape (next := next) (cycles.entry B live)
      (matchingAugmentNodePort next old.cuts dual.node) := by
  let e := cycles.entry B live
  let nodePort := matchingAugmentNodePort next old.cuts dual.node
  have preserve {D : Finset (Fin k)} (sub : D ⊆ B) (p : Fin k) :
      matchingCycleInterior old D p ⊆ next.edges := by
    intro edge used
    obtain ⟨found, within⟩ := Finset.mem_filter.mp used
    exact (unchanged _ (fun v hv => sub (Finset.mem_erase.mp (within v hv)).2)).mpr found
  let cycle := e.geometry.cycle
  have kept : rematchBlossomCycle cycle e.geometry.baseSlot.val ⊆ next.edges := by
    intro edge on
    have pairs := (rematchBlossomCycle_spec e.geometry.baseSlot.isLt e.geometry.distinct e.geometry.odd
      (fun _ => True) (fun _ _ => trivial)).1
    have inside (v : Fin k) (hv : v ∈ edge) : v ∈ B := by
      have inCycle := (Finset.mem_erase.mp ((pairs.1 _ on).2 v hv)).2
      have here := e.geometry.ports.symm ▸ inCycle
      exact e.ports.subset v here (e.ports.containsPort v here)
    apply (unchanged edge inside).mpr
    change edge ∈ (alternatingEdges (e.geometry.cycle.rotate e.geometry.baseSlot.val).tail).toFinset at on
    rw [e.geometry.rotate, List.tail_cons, List.mem_toFinset] at on
    induction edge using Sym2.inductionOn with
    | hf a b => exact old.partialMate_some_iff.mp (e.geometry.matched a b on).1
  let chosen : MatchingCycleLiftPorts e e.base := {
    free := e.geometry.baseSlot
    choose := id
    exposed := e.geometry.atBase
    members := e.ports.containsPort
    pairs := by
      intro r hr
      let idx (side : Bool) : Fin cycle.length :=
        ⟨matchingRebaseChildIndex cycle.length e.geometry.baseSlot.val r side,
          Nat.mod_lt _ (Nat.zero_lt_of_lt e.geometry.baseSlot.isLt)⟩
      have inPairs : s(cycle.get (idx false),cycle.get (idx true)) ∈ rematchBlossomCycle cycle e.geometry.baseSlot.val :=
        (rematchBlossomCycle_mem_iff_physicalPair cycle e.geometry.baseSlot.isLt _).mpr ⟨r,hr,rfl⟩
      have next : ((idx false).val+1)%cycle.length = (idx true).val := by
        change (((e.geometry.baseSlot.val+(2*r+1))%cycle.length)+1)%cycle.length =
          (e.geometry.baseSlot.val+(2*r+2))%cycle.length
        rw [Nat.mod_add_mod]
        exact congrArg (· % cycle.length) (by omega)
      have original : s(cycle.get (idx false),cycle.get (idx true)) ∈ old.edges := by
        change s(cycle.get (idx false),cycle.get (idx true)) ∈
          (alternatingEdges (cycle.rotate e.geometry.baseSlot.val).tail).toFinset at inPairs
        change _ ∈ (alternatingEdges ((e.geometry.cycle.rotate e.geometry.baseSlot.val).tail)).toFinset at inPairs
        rw [e.geometry.rotate, List.tail_cons, List.mem_toFinset] at inPairs
        exact old.partialMate_some_iff.mp (e.geometry.matched _ _ inPairs).1
      have row := e.matchedRow (idx false)
      let following : Fin cycle.length :=
        ⟨((idx false).val+1)%cycle.length,Nat.mod_lt _ (Nat.zero_lt_of_lt (idx false).isLt)⟩
      change old.partialMate (cycle.get (idx false)) = some (cycle.get following) →
        e.geometry.edges (idx false) = (cycle.get (idx false), cycle.get following) at row
      rw [show following = idx true from Fin.ext next] at row
      exact (row (old.partialMate_some_iff.mpr original)).symm }
  have sub := preserve (D := B) Finset.Subset.rfl e.base
  refine ⟨e.base, e.base_mem, matchingAugmentNodePort_eq next dual.nodeInjective live e.base_mem e.internal sub,
    chosen, ?_, ?_, ?_⟩
  · rw [matchingCycleInterior_eq e.internal sub]
    exact e.internal
  · intro j used q label
    change j.liftPort nodePort = q.val
    cases form : j.children with
    | none => simpa only [MatchingMemberJob.liftPort,form] using label
    | some child =>
      obtain ⟨D,hd,id,tree,oldBase,block⟩ := cycles.child B live j used child form
      let d := cycles.entry D hd
      have identified : d.base = q := Fin.ext (oldBase.trans label)
      have below : D ⊆ B := block.symm ▸ e.ports.subset _ ((e.owner j used d.base oldBase.symm).1)
      have arrived : nodePort (dual.node D) = d.base.val :=
        matchingAugmentNodePort_eq next dual.nodeInjective hd d.base_mem d.internal (preserve below d.base)
      rw [MatchingMemberJob.liftPort, form]
      change nodePort j.node = q.val
      rw [← id, arrived, identified]
  · intro edge hit
    obtain ⟨source,here,rfl⟩ := Finset.mem_image.mp hit
    have eq : Sym2.map id source = source := by
      induction source using Sym2.inductionOn
      rfl
    change Sym2.map id source ∈ next.edges
    rw [eq]
    exact kept here


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentCycleShape

/-! matching/MatchingAugmentUpdatedCycle.lean -/
section RppSource_MatchingAugmentUpdatedCycle
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

def matchingAugmentRelabel (port : ℕ → ℕ) (node _old : ℕ) : ℕ := port node

theorem MatchingMemberJob.augmentationRelabel (job : MatchingMemberJob) (port : ℕ → ℕ) :
    let changed := job.relabel (matchingAugmentRelabel port)
    changed.representative = job.liftPort port ∧ changed.node = job.node ∧
      changed.children = job.children.map (MatchingMemberTree.relabel (matchingAugmentRelabel port)) := by
  cases h : job.children <;> simp [MatchingMemberJob.relabel, h, MatchingMemberJob.liftPort, matchingAugmentRelabel]

theorem MatchingExpansionChildPorts.relabel_block {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {B : Finset (Fin k)} (e : MatchingExpansionChildPorts old B)
    (sameCuts : next.cuts = old.cuts) (choose : Fin k → Fin k)
    (inside : ∀ q ∈ e.ports, choose q ∈ e.block q) (p : Fin k) (listed : p ∈ e.ports) :
    (e.relabel sameCuts choose inside).block (choose p) = e.block p := by
  change e.block (e.owner (choose p)) = e.block p
  rw [e.unique p listed _ (inside p listed)]

/-- Preserve the cyclic order and edge words while updating the exposed
originals in the abstract cycle and its recursively relabeled tree. -/
noncomputable def MatchingLiveCycle.afterAugment {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    (e : MatchingLiveCycle old node B) (port : ℕ → ℕ) (shape : MatchingAugmentCycleShape (next := next) e port)
    (sameCuts : next.cuts = old.cuts) (potential : next.potential = old.potential) (cutDual : next.cutDual = old.cutDual)
    (size : 2 ≤ e.geometry.cycle.length) : MatchingLiveCycle next node B := by
  let f := matchingAugmentRelabel port
  let choose := shape.choose
  let ports := e.ports.relabel sameCuts choose.choose choose.members
  let tree := e.tree.relabel f
  have labels (j : MatchingMemberJob) (listed : j ∈ e.tree.jobs none) (p : Fin k) (key : j.representative = p.val) :
      (j.relabel f).representative = (choose.choose p).val :=
    (j.augmentationRelabel port).1.trans (shape.labels j listed p key)
  let g := e.updatedGeometry choose sameCuts potential cutDual f labels shape.crossing
  have lengthEq : (e.tree.jobs none).length = e.geometry.cycle.length := (e.tree.jobs_length none).trans e.arity
  have renamed (p : Fin k) (hp : p ∈ e.ports.ports) : choose.choose p ∈ ports.ports := Finset.mem_image_of_mem _ hp
  have atBlock (p : Fin k) (hp : p ∈ e.ports.ports) : ports.block (choose.choose p) = e.ports.block p :=
    e.ports.relabel_block sameCuts _ choose.members p hp
  have oldKey (j : MatchingMemberJob) (hj : j ∈ e.tree.jobs none) :
      ∃ p : Fin k, j.representative = p.val ∧ p ∈ e.ports.ports := by
    obtain ⟨i,hi,atI⟩ := List.mem_iff_getElem.mp hj
    let slot : Fin e.geometry.cycle.length := ⟨i,lengthEq ▸ hi⟩
    refine ⟨e.geometry.cycle.get slot, ?_, ?_⟩
    · exact (congrArg MatchingMemberJob.representative atI).symm.trans (e.jobKey i hi)
    · exact e.geometry.ports.symm ▸ List.mem_toFinset.mpr (List.get_mem _ _)
  have oldJob (j : MatchingMemberJob) (hj : j ∈ tree.jobs none) (p : Fin k) (label : j.representative = p.val) :
      ∃ source ∈ e.tree.jobs none, ∃ q ∈ e.ports.ports,
        source.relabel f = j ∧ source.representative = q.val ∧ choose.choose q = p := by
    rw [e.tree.relabel_jobs f] at hj
    obtain ⟨source,listed,rfl⟩ := List.mem_map.mp hj
    obtain ⟨q,key,hq⟩ := oldKey source listed
    exact ⟨source,listed,q,hq,rfl,key,Fin.ext ((labels source listed q key).symm.trans label)⟩
  refine ⟨shape.base,tree,ports,g,?_,?_,?_,?_,?_,shape.internal,?_⟩
  · change (e.tree.relabel f).arity = (e.geometry.cycle.map choose.choose).length
    rw [MatchingMemberTree.relabel_arity, List.length_map]
    exact e.arity
  · change tree.rootKeys.map Prod.fst = (e.geometry.cycle.map choose.choose).map Fin.val
    rw [← tree.jobs_rootKeys none, List.map_map, e.tree.relabel_jobs f]
    apply List.ext_getElem
    · simp [lengthEq]
    · intro i hi _
      have within : i < (e.tree.jobs none).length := by simpa only [List.length_map] using hi
      let slot : Fin e.geometry.cycle.length := ⟨i,lengthEq ▸ within⟩
      let j := (e.tree.jobs none)[i]'within
      simp only [List.getElem_map, Function.comp_apply, MatchingMemberTree.rootKey]
      change (j.relabel f).representative = (choose.choose (e.geometry.cycle.get slot)).val
      exact labels j (List.getElem_mem within) _ (e.jobKey i within)
  · intro j listed p label
    obtain ⟨source,used,q,hq,rfl,key,rfl⟩ := oldJob j listed p label
    refine ⟨renamed q hq, fun v => ?_⟩
    simpa only [MatchingMemberJob.relabel_leaves, atBlock q hq] using (e.owner source used q key).2 v
  · intro j listed p label
    obtain ⟨source,used,q,hq,rfl,key,rfl⟩ := oldJob j listed p label
    rw [atBlock q hq, (source.augmentationRelabel port).2.1]
    exact e.childNode source used q key
  · intro D live sub
    rw [sameCuts] at live
    obtain ⟨p,hp,contains⟩ := e.descendants D live sub
    exact ⟨choose.choose p,renamed p hp,(atBlock p hp).symm ▸ contains⟩
  · intro i a b matched
    let slot : Fin e.geometry.cycle.length := ⟨i.val, by
      have hi : i.val < (e.geometry.cycle.map choose.choose).length := i.isLt
      simpa only [List.length_map] using hi⟩
    have root := (matchingCutPort_of_inner next shape.belongs shape.internal (Finset.filter_subset _ _)).1
    have atRow := choose.updatedMatchedRow size root shape.crossing slot
    dsimp only at atRow
    let successor : Fin e.geometry.cycle.length :=
      ⟨(slot.val+1)%e.geometry.cycle.length, Nat.mod_lt _ (Nat.zero_lt_of_lt slot.isLt)⟩
    have left : a = choose.choose (e.geometry.cycle.get slot) := by
      change (e.geometry.cycle.map choose.choose).get i = _
      exact List.getElem_map choose.choose
    have right : b = choose.choose (e.geometry.cycle.get successor) := by
      change (e.geometry.cycle.map choose.choose).get
        ⟨(i.val+1)%(e.geometry.cycle.map choose.choose).length,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩ = _
      simp only [List.get_eq_getElem,List.getElem_map,List.length_map,successor,slot]
    change e.geometry.edges slot = (a,b)
    rw [left,right]
    exact atRow (by rwa [left,right] at matched)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentUpdatedCycle

/-! matching/MatchingExpansionRegistryIds.lean -/
section RppSource_MatchingExpansionRegistryIds
namespace VehicleRoutingSurvey.Routing

/-- Singleton children have no top registry record after promotion. -/
def MatchingMemberJob.promotedTree (job : MatchingMemberJob) : MatchingMemberTree :=
  match job.children with
  | none => .nil
  | some children => .blossom job.representative job.node children .nil

theorem MatchingMemberTree.promoted_ids (tree : MatchingMemberTree) (owner : Option ℕ) :
    (tree.jobs owner).flatMap (fun job => job.promotedTree.registryIds) = tree.registryIds := by
  induction tree with
  | nil => rfl
  | leaf v tail ih => simpa [MatchingMemberTree.jobs, MatchingMemberJob.promotedTree, MatchingMemberTree.registryIds] using ih
  | blossom v n sub tail _ ih =>
    simpa [MatchingMemberTree.jobs, MatchingMemberJob.promotedTree, MatchingMemberTree.registryIds] using ih





end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionRegistryIds

/-! matching/MatchingLiveCycleDescendants.lean -/
section RppSource_MatchingLiveCycleDescendants
namespace VehicleRoutingSurvey.Routing

theorem MatchingMemberTree.jobNodes_lt (tree : MatchingMemberTree) (owner : Option ℕ)
    (job : MatchingMemberJob) (inside : job ∈ tree.jobs owner) (sub : MatchingMemberTree)
    (child : job.children = some sub) : sub.nodes < tree.nodes := by
  induction tree with
  | nil => simp [MatchingMemberTree.jobs] at inside
  | leaf v tail ih =>
    rcases List.mem_cons.mp inside with rfl | found
    · contradiction
    · have := ih found
      simp only [MatchingMemberTree.nodes]; omega
  | blossom v n c tail _ ih =>
    rcases List.mem_cons.mp inside with rfl | found
    · have eq : c = sub := Option.some.inj child
      simp only [MatchingMemberTree.nodes,eq]; omega
    · have := ih found
      simp only [MatchingMemberTree.nodes]; omega

/-- An ID inside a live cut names an actual geometric descendant. The
order of recursion is the size of the immutable member tree. -/
theorem MatchingLiveCycles.descendantCut {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (live : MatchingLiveCycles registry) (B : Finset (Fin k)) (h : B ∈ state.cuts)
    (n : ℕ) (inside : n ∈ (live.entry B h).tree.registryIds) :
    ∃ C ∈ state.cuts, dual.node C = n ∧ C ⊆ B := by
  generalize eq : (live.entry B h).tree.nodes = m
  induction m using Nat.strong_induction_on generalizing B with
  | h m ih =>
    let e := live.entry B h
    have nodes := e.tree.promoted_ids none
    have found : n ∈ (e.tree.jobs none).flatMap (fun j => j.promotedTree.registryIds) := nodes.symm ▸ inside
    obtain ⟨job,onJob,under⟩ := List.mem_flatMap.mp found
    cases c : job.children with
    | none => simp [MatchingMemberJob.promotedTree,c,MatchingMemberTree.registryIds] at under
    | some sub =>
      obtain ⟨C,hc,id,tree,base,block⟩ := live.child B h job onJob sub c
      have port := (e.owner job onJob (live.entry C hc).base base.symm).1
      have contained : C ⊆ B := block.symm ▸ e.ports.subset _ port
      have choice : n = job.node ∨ n ∈ sub.registryIds := by
        simpa [MatchingMemberJob.promotedTree,c,MatchingMemberTree.registryIds] using under
      rcases choice with same | deeper
      · exact ⟨C,hc,id.trans same.symm,contained⟩
      · have small : sub.nodes < m := eq ▸ e.tree.jobNodes_lt none job onJob sub c
        obtain ⟨D,hd,atId,subD⟩ := ih sub.nodes small C hc (tree.symm ▸ deeper) (congrArg MatchingMemberTree.nodes tree)
        exact ⟨D,hd,atId,subD.trans contained⟩



end VehicleRoutingSurvey.Routing
end RppSource_MatchingLiveCycleDescendants

/-! matching/MatchingAugmentRebaseOwners.lean -/
section RppSource_MatchingAugmentRebaseOwners
namespace VehicleRoutingSurvey.Routing

theorem MatchingLiveCycles.cutBelowTop {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (cycles : MatchingLiveCycles registry) {B : Finset (Fin k)} (live : B ∈ old.cuts)
    (q : Fin k) (found : dual.node B ∈ (registry.trees.tree q).registryIds) :
    part.representative q = q ∧ B ⊆ part.blocks.block q := by
  have present : blossomNodeAt s q ≠ 0 := by
    intro empty
    have keys := registry.trees.roots q
    change (registry.trees.tree q).rootKeys =
      (if blossomNodeAt s q = 0 then [] else [MatchingMemberTree.rootKey q.val (blossomNodeAt s q)]) at keys
    rw [if_pos empty] at keys
    cases shape : registry.trees.tree q with
    | nil => simp [shape, MatchingMemberTree.registryIds] at found
    | leaf => simp [shape, MatchingMemberTree.rootKeys] at keys
    | blossom => simp [shape, MatchingMemberTree.rootKeys] at keys
  have atTop : part.representative q = q ∧ (part.blocks.block q).card ≠ 1 := by
    by_contra absent
    exact present ((dual.top q).trans (if_neg absent))
  let C := part.blocks.block q
  have cut : C ∈ old.cuts := part.blocks.cut_mem (Finset.mem_univ _) atTop.2
  have tree := (cycles.top q cut atTop.1).2
  rw [tree] at found
  have owned : dual.node B = dual.node C ∨ dual.node B ∈ (cycles.entry C cut).tree.registryIds := by
    simpa [MatchingMemberTree.registryIds] using found
  refine ⟨atTop.1, ?_⟩
  rcases owned with here | below
  · exact (dual.nodeInjective live cut here) ▸ Finset.Subset.rfl
  · obtain ⟨D, hd, same, inside⟩ := cycles.descendantCut C cut _ below
    exact (dual.nodeInjective hd live same) ▸ inside

/-- Every allocated cut is stored under the top representative of each of
its originals. The same permanent ID remains in that tree during rebasing. -/
theorem MatchingLiveCycles.cutInTopTree {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (cycles : MatchingLiveCycles registry) {B : Finset (Fin k)} (live : B ∈ old.cuts)
    {v : Fin k} (inside : v ∈ B) :
    dual.node B ∈ (registry.trees.tree (part.representative v)).registryIds := by
  have found := (registry.keys _).mpr ⟨B,live,rfl⟩
  obtain ⟨q, _, inTree⟩ := List.mem_flatMap.mp found
  obtain ⟨fixed, sub⟩ := cycles.cutBelowTop live q inTree
  have selected := (part.mem_activeRepresentatives q).mpr fixed
  have rep := (part.membership_representative selected).mp (sub inside)
  simpa only [rep] using inTree

/-- Recursion visits exactly the registered cuts within the selected top
blocks. An untouched top keeps all of its archived children as well. -/
theorem MatchingLiveCycles.cutQueued_iff {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (cycles : MatchingLiveCycles registry) (ports : List (Fin k))
    {B : Finset (Fin k)} (live : B ∈ old.cuts) {v : Fin k} (inside : v ∈ B) :
    dual.node B ∈ matchingRebaseQueueIds (ports.filterMap (matchingAugmentTopTask cycles)) ↔
      part.representative v ∈ ports.map part.representative := by
  constructor
  · intro queued
    obtain ⟨task, stored, contains⟩ := List.mem_flatMap.mp queued
    obtain ⟨p, selected, emitted⟩ := List.mem_filterMap.mp stored
    have ids := (matchingAugmentTopTask_shape cycles p emitted).2.2.1
    rw [ids] at contains
    obtain ⟨fixed, sub⟩ := cycles.cutBelowTop live _ contains
    have atRep := (part.membership_representative ((part.mem_activeRepresentatives _).mpr fixed)).mp (sub inside)
    exact List.mem_map.mpr ⟨p,selected,atRep.symm⟩
  · intro marked
    obtain ⟨p, selected, same⟩ := List.mem_map.mp marked
    let q := part.representative p
    let C := part.blocks.block q
    have fixed : part.representative q = q := part.representative_idem _
    have found := cycles.cutInTopTree live inside
    rw [← same] at found
    obtain ⟨_, subset⟩ := cycles.cutBelowTop live q found
    have large : C.card ≠ 1 := by
      have size := registry.nontrivial B live
      have below : B.card ≤ C.card := Finset.card_le_card subset
      omega
    let h := part.blocks.cut_mem (Finset.mem_univ q) large
    let task : MatchingRebaseTask := ⟨dual.node C,p.val,(cycles.entry C h).tree⟩
    have emitted : matchingAugmentTopTask cycles p = some task := dif_pos large
    have ids := (matchingAugmentTopTask_shape cycles p emitted).2.2.1
    exact List.mem_flatMap.mpr ⟨task, List.mem_filterMap.mpr ⟨p,selected,emitted⟩, ids.symm ▸ found⟩




end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentRebaseOwners

/-! matching/MatchingAugmentPersistentCycles.lean -/
section RppSource_MatchingAugmentPersistentCycles
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

private theorem MatchingRebaseArchive.descendantLive {s : ArithmeticState} (archive : MatchingRebaseArchive s)
    {tree : MatchingMemberTree} {id n : ℕ} (live : archive.live id tree)
    (inside : n ∈ tree.registryIds) : ∃ next, archive.live n next := by
  generalize eq : tree.nodes = size
  induction size using Nat.strong_induction_on generalizing id tree with
  | h size ih =>
    rw [← tree.jobs_registryIds none] at inside
    obtain ⟨job, used, below⟩ := List.mem_flatMap.mp inside
    cases kind : job.children with
    | none => simp [MatchingMemberJob.tree, kind, MatchingMemberTree.registryIds] at below
    | some child =>
      have valid := archive.child id tree live job used child kind
      have whereAt : n = job.node ∨ n ∈ child.registryIds := by
        simpa [MatchingMemberJob.tree, kind, MatchingMemberTree.registryIds] using below
      rcases whereAt with here | deeper
      · exact ⟨child, here.symm ▸ valid⟩
      · have smaller : child.nodes < size := eq ▸ tree.jobNodes_lt none job used child kind
        exact ih child.nodes smaller valid deeper rfl

theorem MatchingPreparedRebase.queuedIdLive {base : ArithmeticState} {jobs : List MatchingRebaseTask}
    (prepared : MatchingPreparedRebase base jobs) {id : ℕ} (queued : id ∈ matchingRebaseQueueIds jobs) :
    ∃ tree, prepared.registry.live id tree := by
  obtain ⟨task, used, contains⟩ := List.mem_flatMap.mp queued
  have typed := (prepared.tasks task used).1
  rcases List.mem_cons.mp contains with here | below
  · exact ⟨task.children,here.symm ▸ typed⟩
  · exact prepared.registry.descendantLive typed below

theorem MatchingAugmentPreparedRegistry.derived {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {before base : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest before} {registry : MatchingRegistryView dual}
    {cycles : MatchingLiveCycles registry} {rows : List (Fin k × Fin k)} {nextPart : CompactMatchingPartition next}
    {jobs : List MatchingRebaseTask} {prepared : MatchingPreparedLift base jobs (compactPrimalMateWord next)}
    (view : MatchingAugmentPreparedRegistry cycles rows nextPart prepared) {B : Finset (Fin k)}
    (live : B ∈ old.cuts) (queued : dual.node B ∈ matchingRebaseQueueIds jobs) :
    matchingAugmentDerivedCut cycles.entry next B := by
  obtain ⟨tree, stored⟩ := prepared.toMatchingPreparedRebase.queuedIdLive queued
  obtain ⟨C,hc,id,_,use⟩ := (view.live _ tree).mp stored
  exact (dual.nodeInjective hc live id) ▸ use

theorem MatchingAugmentPreparedRegistry.untouchedCut {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {before base : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest before} {registry : MatchingRegistryView dual}
    {cycles : MatchingLiveCycles registry} {rows : List (Fin k × Fin k)} {nextPart : CompactMatchingPartition next}
    {jobs : List MatchingRebaseTask} {prepared : MatchingPreparedLift base jobs (compactPrimalMateWord next)}
    (view : MatchingAugmentPreparedRegistry cycles rows nextPart prepared) {B : Finset (Fin k)}
    (live : B ∈ old.cuts) (outside : dual.node B ∉ matchingRebaseQueueIds jobs) :
    ∀ edge : Sym2 (Fin k), (∀ v ∈ edge, v ∈ B) → (edge ∈ next.edges ↔ edge ∈ old.edges) := by
  let p := (cycles.entry B live).base
  have inside := (cycles.entry B live).base_mem
  have owns := cycles.cutInTopTree live inside
  obtain ⟨fixed, sub⟩ := cycles.cutBelowTop live _ owns
  have notPicked : part.representative p ∉ (selectedAugmentationPorts rows).map part.representative := by
    intro picked
    apply outside
    rw [view.tasks]
    exact (cycles.cutQueued_iff _ live inside).mpr picked
  intro edge within
  exact view.untouched _ ((part.mem_activeRepresentatives _).mpr fixed) notPicked edge (fun v h => sub (within v h))

noncomputable def MatchingAugmentPreparedRegistry.cycleShape {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {before base : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest before} {registry : MatchingRegistryView dual}
    {cycles : MatchingLiveCycles registry} {rows : List (Fin k × Fin k)} {nextPart : CompactMatchingPartition next}
    {jobs : List MatchingRebaseTask} {prepared : MatchingPreparedLift base jobs (compactPrimalMateWord next)}
    (view : MatchingAugmentPreparedRegistry cycles rows nextPart prepared) (B : Finset (Fin k)) (live : B ∈ old.cuts) :
    MatchingAugmentCycleShape (next := next) (cycles.entry B live)
      (matchingAugmentNodePort next old.cuts dual.node) :=
  if queued : dual.node B ∈ matchingRebaseQueueIds jobs then cycles.liftedCycleShape live (view.derived live queued)
  else cycles.retainedCycleShape live (view.untouchedCut live queued)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentPersistentCycles

/-! matching/MatchingAugmentPersistentMemory.lean -/
section RppSource_MatchingAugmentPersistentMemory
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

private theorem MatchingAugmentArchiveFrame.start {s base : ArithmeticState} (frame : MatchingAugmentArchiveFrame s base)
    {n : ℕ} (low : 0 < n) (high : n < s.nr 76) :
    matchingCycleRecordStart base n = matchingCycleRecordStart s n := by
  simp only [matchingCycleRecordStart, frame.fixed 77 (by decide), (frame.headers n low high).1]

/-- The archived row contains the original edge words and the new label of
the immediate child, as determined by the completed matching. -/
theorem MatchingAugmentPreparedRegistry.completedChild {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {before base out : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest before} {registry : MatchingRegistryView dual}
    {cycles : MatchingLiveCycles registry} {rows : List (Fin k × Fin k)} {nextPart : CompactMatchingPartition next}
    {jobs : List MatchingRebaseTask} {prepared : MatchingPreparedLift base jobs (compactPrimalMateWord next)}
    (view : MatchingAugmentPreparedRegistry cycles rows nextPart prepared)
    (completed : MatchingRebaseCompletedRows prepared.lift jobs out)
    (B : Finset (Fin k)) (live : B ∈ old.cuts) (i : Fin (cycles.entry B live).geometry.cycle.length) :
    let e := cycles.entry B live
    let chosen := (view.cycleShape B live).choose
    let n := dual.node B
    matchingRebaseRowsAt before out n i.val =
      {matchingRebaseRowsAt before before n i.val with
        representative := (chosen.choose (e.geometry.cycle.get i)).val} := by
  intro e chosen n
  have low : 0 < n := Nat.pos_of_ne_zero (dual.nodeNonzero B live)
  have high : n < before.nr 76 := registry.allocated B live
  have oldMemory := (cycles.memory B live).rows
  have len : before.nm (before.nr 78+n) = e.geometry.cycle.length := oldMemory.length
  have keepLength : base.nm (base.nr 78+n) = e.geometry.cycle.length := by
    rw [view.frame.fixed 78 (by decide), (view.frame.headers n low high).2]
    exact len
  have oldWord (w : ℕ) (width : w < 4) :
      base.nm (matchingCycleRecordStart before n+4*i.val+w) =
        before.nm (matchingCycleRecordStart before n+4*i.val+w) := by
    apply view.frame.rows n low high
    have bound : i.val < e.geometry.cycle.length := i.isLt
    simp only [matchingRebaseRowArea, matchingCycleRecordEnd, len]
    omega
  have oldRow : matchingRebaseRowsAt base base n i.val = matchingRebaseRowsAt before before n i.val := by
    simp only [matchingRebaseRowsAt, view.frame.start low high, matchingCycleChildAt,
      show base.nm (matchingCycleRecordStart before n+4*i.val) = _ from oldWord 0 (by decide),
      oldWord 1 (by decide), oldWord 2 (by decide), oldWord 3 (by decide), Nat.add_zero]
  have formulas : matchingRebaseRowsAt before out n i.val = matchingRebaseRowsAt base out n i.val := by
    simp only [matchingRebaseRowsAt, view.frame.start low high]
  rw [formulas, ← oldRow]
  by_cases queued : n ∈ matchingRebaseQueueIds jobs
  · have reached : prepared.registry.live n e.tree :=
      (view.live n e.tree).mpr ⟨B,live,rfl,rfl,view.derived live queued⟩
    have index : i.val < e.tree.arity := e.arity.symm ▸ i.isLt
    have row := completed.rows n e.tree reached i.val index
    rw [if_pos queued, view.port] at row
    rw [row]
    have hj : i.val < (e.tree.jobs none).length := ((e.tree.jobs_length none).trans e.arity).symm ▸ i.isLt
    let j := (e.tree.jobs none)[i.val]'hj
    have key : j.representative = (e.geometry.cycle.get i).val := e.jobKey i.val hj
    have label := (view.cycleShape B live).labels j (List.getElem_mem hj) _ key
    rw [matchingRebasePortAt, dif_pos hj]
    exact congrArg (fun word => {(matchingRebaseRowsAt base base n i.val) with representative := word}) label
  · have stable := completed.untouched n low (by rwa [view.frame.fixed 76 (by decide)]) queued
      i.val (by rw [keepLength]; exact i.isLt)
    rw [stable, oldRow]
    have chosenEq : chosen.choose (e.geometry.cycle.get i) = e.geometry.cycle.get i := by
      change (view.cycleShape B live).choose.choose (e.geometry.cycle.get i) = _
      rw [MatchingAugmentPreparedRegistry.cycleShape, dif_neg queued]
      rfl
    rw [chosenEq]
    have atRow : (matchingRebaseRowsAt before before n i.val).representative = (e.geometry.cycle.get i).val :=
      (oldMemory.records i).1
    rw [← atRow]

theorem MatchingAugmentPreparedRegistry.completedKey {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {before base out : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest before} {registry : MatchingRegistryView dual}
    {cycles : MatchingLiveCycles registry} {rows : List (Fin k × Fin k)} {nextPart : CompactMatchingPartition next}
    {jobs : List MatchingRebaseTask} {prepared : MatchingPreparedLift base jobs (compactPrimalMateWord next)}
    (view : MatchingAugmentPreparedRegistry cycles rows nextPart prepared)
    (completed : MatchingRebaseCompletedRows prepared.lift jobs out)
    (B : Finset (Fin k)) (live : B ∈ old.cuts) (i : Fin (cycles.entry B live).geometry.cycle.length) :
    let n := dual.node B
    let oldRow := matchingRebaseRowsAt before before n i.val
    let newRow := matchingRebaseRowsAt before out n i.val
    (newRow.representative,newRow.node) = matchingRelabelKey
      (matchingAugmentRelabel (matchingAugmentNodePort next old.cuts dual.node)) (oldRow.representative,oldRow.node) := by
  intro n oldRow newRow
  let e := cycles.entry B live
  let port := matchingAugmentNodePort next old.cuts dual.node
  have count : e.tree.rootKeys.length = e.geometry.cycle.length := e.tree.rootKeys_length.trans e.arity
  have fits : i.val < e.tree.rootKeys.length := count.symm ▸ i.isLt
  have seen : i.val < (e.tree.jobs none).length := ((e.tree.jobs_length none).trans e.arity).symm ▸ i.isLt
  let job := (e.tree.jobs none)[i.val]'seen
  have registered := (cycles.memory B live).members
  have words : (oldRow.representative,oldRow.node) = e.tree.rootKeys[i.val]'fits :=
    registered.encoded.2.1 i.val fits
  have atJob : e.tree.rootKeys[i.val]'fits = (job.representative,job.node) := by
    have keys := (e.tree.jobs_rootKeys none).symm
    have eq : e.tree.rootKeys[i.val]'fits =
        ((e.tree.jobs none).map (fun j => MatchingMemberTree.rootKey j.representative j.node))[i.val]'(by
          simpa only [List.length_map] using seen) := getElem_congr_coll keys
    simpa only [List.getElem_map,MatchingMemberTree.rootKey,job] using eq
  have original := words.trans atJob
  have rep : oldRow.representative = job.representative := congrArg Prod.fst original
  have id : oldRow.node = job.node := congrArg Prod.snd original
  have label : job.representative = (e.geometry.cycle.get i).val := e.jobKey i.val seen
  have chosen := (view.cycleShape B live).labels job (List.getElem_mem seen) _ label
  have update := view.completedChild completed B live i
  change newRow = {oldRow with representative := ((view.cycleShape B live).choose.choose (e.geometry.cycle.get i)).val} at update
  rw [update]
  change (((view.cycleShape B live).choose.choose (e.geometry.cycle.get i)).val,oldRow.node) =
    matchingRelabelKey (matchingAugmentRelabel port) (oldRow.representative,oldRow.node)
  rw [← chosen,original]
  have properJob := e.tree.jobs_proper none registered.proper.2.2.1 job (List.getElem_mem seen)
  cases kind : job.children with
  | none =>
    have empty : job.node = 0 := by simpa only [MatchingMemberJob.proper,kind] using properJob
    simp [MatchingMemberJob.liftPort,kind,matchingRelabelKey,empty,id]
  | some children =>
    have positive : 0 < job.node := (show 0 < job.node ∧ 2 ≤ children.arity ∧ children.proper by
      simpa only [MatchingMemberJob.proper,kind] using properJob).1
    simp [MatchingMemberJob.liftPort,kind,matchingRelabelKey,matchingAugmentRelabel,Nat.ne_of_gt positive,id,port]

theorem MatchingAugmentPreparedRegistry.completedHeaders {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {original before base out : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest before} {registry : MatchingRegistryView dual}
    {cycles : MatchingLiveCycles registry} {rows : List (Fin k × Fin k)} {nextPart : CompactMatchingPartition next}
    {jobs : List MatchingRebaseTask} {prepared : MatchingPreparedLift base jobs (compactPrimalMateWord next)}
    (view : MatchingAugmentPreparedRegistry cycles rows nextPart prepared)
    (completed : MatchingRebaseCompletedRows prepared.lift jobs out)
    (storage : MatchingStageStorage k original before) (capacity : ∀ n < before.nr 76, n < matchingBlossomCapacity k)
    (starts : out.nr 77 = before.nr 77) (counts : out.nr 78 = before.nr 78)
    {n : ℕ} (low : 0 < n) (high : n < before.nr 76) :
    matchingCycleRecordStart out n = matchingCycleRecordStart before n ∧
      out.nm (out.nr 78+n) = before.nm (before.nr 78+n) := by
  obtain ⟨warm,_,nodes,_,first,lengths,left,right,marks,witnesses,records,promotion,mask,map,_,_⟩ := storage
  have mates := warm.matesBefore
  have role := warm.representativesAfter
  have reps := warm.candidatesAfter
  have cache := warm.pairsAfter
  have size := warm.size
  have fits := capacity n high
  have header (a : ℕ) (bounds : before.nr 50+k ≤ a ∧ a < before.nr 79) : out.nm a = base.nm a := by
    apply completed.headers
    simpa only [matchingRebaseHeaderArea,view.frame.fixed 50 (by decide), view.frame.fixed 55 (by decide),
      view.frame.fixed 79 (by decide), size] using bounds
  obtain ⟨start,length⟩ := view.frame.headers n low high
  constructor
  · rw [matchingCycleRecordStart, matchingCycleRecordStart, starts, header _ (by omega)]
    exact start
  · rw [counts, header _ (by omega)]
    exact length


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentPersistentMemory

/-! matching/MatchingAugmentTopRegistry.lean -/
section RppSource_MatchingAugmentTopRegistry
namespace VehicleRoutingSurvey.Routing

def matchingAugmentTopSwap {k : ℕ} (old next : Fin k → Fin k) (v : Fin k) : Fin k :=
  if v = old v then next v else if v = next v then old v else v

private theorem matchingAugmentTopSwap_spec {k : ℕ} (old next : Fin k → Fin k)
    (oldOld : ∀ v, old (old v) = old v) (newNew : ∀ v, next (next v) = next v)
    (oldNew : ∀ v, old (next v) = old v) (newOld : ∀ v, next (old v) = next v) :
    let swap := matchingAugmentTopSwap old next
    Function.Involutive swap ∧ ∀ v, old (swap v) = old v ∧ (old (swap v) = swap v ↔ next v = v) := by
  intro swap
  have before (v : Fin k) : old (swap v) = old v := by
    change old (if v = old v then next v else if v = next v then old v else v) = _
    split
    · exact oldNew v
    · split
      · exact oldOld v
      · rfl
  have after (v : Fin k) : next (swap v) = next v := by
    change next (if v = old v then next v else if v = next v then old v else v) = _
    split
    · exact newNew v
    · split
      · exact newOld v
      · rfl
  constructor
  · intro v
    change (if swap v = old (swap v) then next (swap v)
      else if swap v = next (swap v) then old (swap v) else swap v) = v
    rw [before,after]
    by_cases left : v = old v
    · have atSwap : swap v = next v := if_pos left
      rw [atSwap]
      by_cases same : next v = old v
      · rw [if_pos same, same, ← left]
      · rw [if_neg same, if_pos rfl, ← left]
    · by_cases right : v = next v
      · have atSwap : swap v = old v := (if_neg left).trans (if_pos right)
        rw [atSwap, if_pos rfl, ← right]
      · have atSwap : swap v = v := (if_neg left).trans (if_neg right)
        rw [atSwap, if_neg left, if_neg right]
  · intro v
    refine ⟨before v,?_⟩
    rw [before]
    change old v = (if v = old v then next v else if v = next v then old v else v) ↔ _
    by_cases left : v = old v
    · rw [if_pos left, ← left, eq_comm]
    · by_cases right : v = next v
      · rw [if_neg left, if_pos right, ← right]
        exact iff_of_true rfl rfl
      · rw [if_neg left, if_neg right]
        exact iff_of_false (Ne.symm left) (Ne.symm right)

/-- A rebase exchanges each top block's old and new exposed originals.
Permuting the top slots and relabeling their trees preserves all live IDs. -/
noncomputable def MatchingRegistryView.afterAugment {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {nextPart : CompactMatchingPartition next} {forest : AlternatingForestState (Fin k)} {original s t : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {newDual : MatchingSearchDualMemory nextPart forest t}
    (registry : MatchingRegistryView dual) (sameCuts : next.cuts = old.cuts)
    (sameBlocks : nextPart.blocks.block = part.blocks.block) (nodes : newDual.node = dual.node)
    (cursor : t.nr 76 = s.nr 76) (storage : MatchingStageStorage k original t)
    (order : MatchingCycleRecordOrder t) (f : ℕ → ℕ → ℕ)
    (labels : ∀ q : Fin k, part.representative q = q → (part.blocks.block q).card ≠ 1 →
      f (dual.node (part.blocks.block q)) q.val = (nextPart.representative q).val)
    (encoding : ∀ q : Fin k, ((registry.trees.tree q).relabel f).encoded t.nm (t.nr 77) (t.nr 78)) :
    MatchingRegistryView newDual := by
  let swap := matchingAugmentTopSwap part.representative nextPart.representative
  have oldNew (v : Fin k) : part.representative (nextPart.representative v) = part.representative v := by
    apply part.same_block.mpr (part.blocks.same_of_mem (Finset.mem_univ v) _)
    rw [← sameBlocks]
    exact nextPart.inside v
  have newOld (v : Fin k) : nextPart.representative (part.representative v) = nextPart.representative v := by
    apply nextPart.same_block.mpr
    rw [sameBlocks]
    exact part.blocks.same_of_mem (Finset.mem_univ v) (part.inside v)
  have shape := matchingAugmentTopSwap_spec part.representative nextPart.representative
    part.representative_idem nextPart.representative_idem oldNew newOld
  have involution := shape.1
  have facts := shape.2
  let tree (v : Fin k) := (registry.trees.tree (swap v)).relabel f
  have block (v : Fin k) : part.blocks.block (swap v) = nextPart.blocks.block v := by
    rw [sameBlocks]
    exact part.same_block.mp (facts v).1
  have top (v : Fin k) : blossomNodeAt t v = blossomNodeAt s (swap v) := by
    have fixed : part.representative (swap v) = swap v ↔ nextPart.representative v = v := (facts v).2
    by_cases active : nextPart.representative v = v
    · simp only [newDual.top,dual.top,nodes,active,fixed.mpr active,block]
    · have inactive : part.representative (swap v) ≠ swap v := fun h => active (fixed.mp h)
      simp only [newDual.top,dual.top,nodes,active,inactive,block,false_and,if_false]
  let trees : MatchingTopMemberTrees k t := {
    tree := tree
    proper v := (MatchingMemberTree.relabel_proper _ _).2 (registry.trees.proper (swap v))
    encoded v := encoding (swap v)
    roots := by
      intro v
      let q := swap v
      have fromOld := registry.trees.roots q
      change (registry.trees.tree q).rootKeys =
        (if blossomNodeAt s q = 0 then [] else [MatchingMemberTree.rootKey q.val (blossomNodeAt s q)]) at fromOld
      change (tree v).rootKeys =
        (if blossomNodeAt t v = 0 then [] else [MatchingMemberTree.rootKey v.val (blossomNodeAt t v)])
      rw [top v, show tree v = (registry.trees.tree q).relabel f from rfl,
        MatchingMemberTree.relabel_keys _ (registry.trees.proper q) f, fromOld]
      change (List.map (matchingRelabelKey f)
        (if blossomNodeAt s q = 0 then [] else [MatchingMemberTree.rootKey q.val (blossomNodeAt s q)])) =
        (if blossomNodeAt s q = 0 then [] else [MatchingMemberTree.rootKey v.val (blossomNodeAt s q)])
      by_cases empty : blossomNodeAt s q = 0
      · simp only [if_pos empty, List.map_nil]
      · rw [if_neg empty]
        have active : part.representative q = q ∧ (part.blocks.block q).card ≠ 1 := by
          by_contra missing
          exact empty ((dual.top q).trans (if_neg missing))
        have fixed := (facts v).2.mp active.1
        have atV : nextPart.representative q = v := by
          apply Eq.trans _ fixed
          apply nextPart.same_block.mpr
          rw [sameBlocks]
          exact (block v).trans (congrFun sameBlocks v)
        have target := (labels q active.1 active.2).trans (congrArg Fin.val atV)
        have node : blossomNodeAt s q = dual.node (part.blocks.block q) := (dual.top q).trans (if_pos active)
        have key : f (blossomNodeAt s q) q.val = v.val := node.symm ▸ target
        simp only [if_neg empty, List.map_cons, List.map_nil, matchingRelabelKey, MatchingMemberTree.rootKey, key] }
  have fin : ((List.finRange k).map swap).Perm (List.finRange k) := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange k).map involution.injective) (List.nodup_finRange k)).mpr
    intro v
    exact ⟨fun _ => List.mem_finRange v, fun _ => List.mem_map.mpr ⟨swap v, List.mem_finRange _, involution v⟩⟩
  have perm : trees.registryIds.Perm registry.trees.registryIds := by
    change ((List.finRange k).flatMap (fun v => (tree v).registryIds)).Perm _
    simp only [tree,MatchingMemberTree.relabel_ids]
    change ((List.finRange k).flatMap (fun v => (registry.trees.tree (swap v)).registryIds)).Perm
      ((List.finRange k).flatMap (fun v => (registry.trees.tree v).registryIds))
    simpa only [List.flatMap_map] using (fin.flatMap_right (fun v => (registry.trees.tree v).registryIds))
  have legal (n : ℕ) (seen : n ∈ trees.registryIds) : 0 < n ∧ n < t.nr 76 := by
    obtain ⟨B,live,atN⟩ := (registry.keys n).mp (perm.mem_iff.mp seen)
    rw [← atN,cursor]
    exact ⟨Nat.pos_of_ne_zero (dual.nodeNonzero B live), registry.allocated B live⟩
  have headers := storage.starts
  have lengths := storage.lengths
  have pointers := storage.nodes
  have left := storage.memberStack
  have map := storage.memberMap
  have masks := storage.mask
  have records := storage.records
  have stages := storage.traceLeft
  have traces := storage.traceRight
  have marks := storage.traceMarks
  have witnesses := storage.witnesses
  have promotion := storage.promotion
  refine ⟨trees,?_,perm.nodup_iff.mpr registry.unique,?_,?_,?_,?_,?_⟩
  · intro v
    apply (tree v).readableAbove order (by omega) (by omega)
    · unfold matchingRebaseScratchEnd
      omega
    · intro n seen
      exact legal n (List.mem_flatMap.mpr ⟨v, List.mem_finRange v, seen⟩)
  · intro n
    rw [perm.mem_iff,nodes,sameCuts]
    exact registry.keys n
  · rw [nodes,cursor,sameCuts]
    exact registry.allocated
  · rw [sameCuts]
    exact registry.nontrivial
  · rw [sameCuts]
    exact registry.laminar
  · intro B live u hu v hv
    rw [sameBlocks]
    exact registry.nested B (sameCuts ▸ live) u hu v hv


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentTopRegistry

/-! matching/MatchingAugmentTopNodes.lean -/
section RppSource_MatchingAugmentTopNodes
namespace VehicleRoutingSurvey.Routing

private theorem matchingAugmentNodeFold {k : ℕ} (rep : Fin k → Fin k)
    (rows : List (Fin k × Fin k)) (model : AugmentationRebaseModel k) :
    rows.foldl (AugmentationRebaseModel.crossing rep) model =
      (selectedAugmentationPorts rows).foldl (fun m p => m.move (rep p) p) model := by
  induction rows generalizing model with
  | nil => rfl
  | cons p rest ih =>
    exact ih ((model.move (rep p.1) p.1).move (rep p.2) p.2)

private theorem matchingAugmentLabelFold_unseen {k : ℕ} (rep : Fin k → Fin k)
    (ports : List (Fin k)) (f : Fin k → Fin k) (q : Fin k)
    (outside : q ∉ ports.map rep) :
    ports.foldl (fun acc p => Function.update acc (rep p) p) f q = f q := by
  induction ports generalizing f with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨different, tail⟩ : q ≠ rep p ∧ q ∉ rest.map rep := by
      simpa only [List.map_cons, List.mem_cons, not_or] using outside
    exact (ih _ tail).trans (Function.update_of_ne different _ _)

private theorem matchingAugmentLabelFold {k : ℕ} (rep : Fin k → Fin k)
    (rows : List (Fin k × Fin k)) (f : Fin k → Fin k) :
    rows.foldl (chooseAugmentationRepresentatives rep) f =
      (selectedAugmentationPorts rows).foldl (fun acc p => Function.update acc (rep p) p) f := by
  induction rows generalizing f with
  | nil => rfl
  | cons p rest ih => exact ih (Function.update (Function.update f (rep p.1) p.1) (rep p.2) p.2)

/-- Crossing installation moves a permanent node ID to the chosen port of
its own top block, leaving all other slots for that block empty. -/
theorem matchingAugmentTopNodes_represented {k : ℕ} (rep : Fin k → Fin k)
    (idem : ∀ v, rep (rep v) = rep v) (nodes : Fin k → ℕ)
    (zero : ∀ v, rep v ≠ v → nodes v = 0) (rows : List (Fin k × Fin k))
    (unique : ((selectedAugmentationPorts rows).map rep).Nodup) :
    let port := rows.foldl (chooseAugmentationRepresentatives rep) id
    let final := rows.foldl (AugmentationRebaseModel.crossing rep) ⟨nodes, []⟩
    ∀ v, final.nodes v = if v = port (rep v) then nodes (rep v) else 0 := by
  intro port final v
  change (rows.foldl (AugmentationRebaseModel.crossing rep) ⟨nodes, []⟩).nodes v =
    if v = rows.foldl (chooseAugmentationRepresentatives rep) id (rep v) then nodes (rep v) else 0
  rw [matchingAugmentLabelFold, matchingAugmentNodeFold]
  generalize eq : selectedAugmentationPorts rows = ports at unique ⊢
  clear eq final port rows
  induction ports using List.reverseRecOn generalizing v with
  | nil =>
    by_cases fixed : v = rep v
    · change nodes v = if v = rep v then nodes (rep v) else 0
      rw [if_pos fixed]
      exact congrArg nodes fixed
    · change nodes v = if v = rep v then nodes (rep v) else 0
      rw [if_neg fixed]
      exact zero v (Ne.symm fixed)
  | append_singleton head p ih =>
    have parts : (head.map rep).Nodup ∧ rep p ∉ head.map rep := by
      simpa [List.nodup_append] using unique
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    let f := head.foldl (fun acc p => Function.update acc (rep p) p) id
    let m : AugmentationRebaseModel k := head.foldl (fun m p => m.move (rep p) p) ⟨nodes, []⟩
    have before (q : Fin k) : m.nodes q = if q = f (rep q) then nodes (rep q) else 0 := ih q parts.1
    have oldLabel : f (rep p) = rep p := matchingAugmentLabelFold_unseen rep head id (rep p) parts.2
    have oldNode : m.nodes (rep p) = nodes (rep p) := by rw [before, idem, oldLabel, if_pos rfl]
    change (m.move (rep p) p).nodes v =
      if v = Function.update f (rep p) p (rep v) then nodes (rep v) else 0
    by_cases new : v = p
    · subst v
      simp [AugmentationRebaseModel.move, oldNode]
    by_cases old : v = rep p
    · subst v
      simp [AugmentationRebaseModel.move, idem, new]
    have kept : (m.move (rep p) p).nodes v = m.nodes v := by
      simp [AugmentationRebaseModel.move, Function.update_of_ne new, Function.update_of_ne old]
    rw [kept, before]
    by_cases sameBlock : rep v = rep p
    · simp [sameBlock,oldLabel,new,old]
    · rw [Function.update_of_ne sameBlock]


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentTopNodes

/-! matching/MatchingBetweenStages.lean -/
section RppSource_MatchingBetweenStages
namespace VehicleRoutingSurvey.Routing



def MatchingBetweenStages.reframe {k i : ℕ} {cost : Fin k → Fin k → ℝ} {original s t : ArithmeticState}
    (view : MatchingBetweenStages cost original i s) (natural : t.nm = s.nm) (real : t.rm = s.rm)
    (ports : ∀ r, r ≠ 30 → r ≠ 40 → t.nr r = s.nr r) : MatchingBetweenStages cost original i t := by
  have fixed (r : ℕ) (a : r ≠ 30 := by decide) (b : r ≠ 40 := by decide) := ports r a b
  let g := view.graph
  have read := view.reads.keeps (t := t) ⟨fun addr _ => congrFun natural addr, fun addr _ _ _ => congrFun real addr⟩
    (fun r mem => fixed r (by simp [matchingRefreshTableRegisters] at mem; omega)
      (by simp [matchingRefreshTableRegisters] at mem; omega))
  have primal : CompactMatchingPrimalDualMemory g.state original t := by
    refine ⟨read.layout.dimension, (fixed 56).trans g.primal.oddMap, ?_, ?_, ?_, ?_, ?_⟩
    · rw [fixed 50]; exact g.primal.mateAbove
    · intro v; rw [fixed 50, natural]; exact g.primal.mate v
    · intro r hi; exact (fixed r (by omega) (by omega)).trans (g.primal.saved r hi)
    · intro a ha; exact (congrFun natural a).trans (g.primal.natural a ha)
    · intro a ha; exact (congrFun real a).trans (g.primal.real a ha)
  let graph : CompactMatchingInterstage cost original i t := ⟨g.state, g.part, g.top, g.count, g.internal, primal,
    read.representatives, read.potentials⟩
  have tops (v : Fin k) : blossomNodeAt t v = blossomNodeAt s v := by simp only [blossomNodeAt, natural, fixed 74]
  let dual : MatchingSearchDualMemory graph.part view.oldForest t := {
    dimension := read.layout.dimension
    separated := by rw [fixed 62, fixed 75]; exact view.dual.separated
    reps := read.representatives
    roles := by rw [fixed 51, natural]; exact view.dual.roles
    effective := read.potentials
    node := view.dual.node
    nodeNonzero := view.dual.nodeNonzero
    nodeInjective := view.dual.nodeInjective
    cutValues B h := by rw [fixed 75, real]; exact view.dual.cutValues B h
    top v := (tops v).trans (view.dual.top v) }
  let registry : MatchingRegistryView dual := view.registry.transport rfl (fixed 77) (fixed 78) (fixed 76) (fixed 65)
    tops (fun a _ => congrFun natural a)
  let cycles : MatchingLiveCycles registry := {
    entry := view.cycles.entry
    memory B h := (view.cycles.memory B h).sameMemory natural
      (fun r mem => fixed r (by simp at mem; omega) (by simp at mem; omega))
    top := view.cycles.top
    child := view.cycles.child
    ids := view.cycles.ids }
  have storage := view.storage.keeps (t := t)
    (fun r mem => fixed r (by simp [matchingFixedStorageRegisters] at mem; omega)
      (by simp [matchingFixedStorageRegisters] at mem; omega))
  have order := view.order.transport (t := t) (by simp [matchingRebaseScratchEnd, fixed 80, fixed 55])
    (fixed 76) (fixed 68) (fun _ _ _ => by simp only [matchingCycleRecordStart, fixed 77, natural])
    (fun _ _ _ => by simp only [matchingCycleRecordEnd, matchingCycleRecordStart, fixed 77, fixed 78, natural])
  exact ⟨graph, view.oldForest, dual, registry, cycles, storage, order, (fixed 76).trans_le view.cursor, read⟩






end VehicleRoutingSurvey.Routing
end RppSource_MatchingBetweenStages

/-! matching/MatchingAugmentNextStage.lean -/
section RppSource_MatchingAugmentNextStage
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

private theorem MatchingMemberTree.recordsAbove_of_order {s : ArithmeticState} (tree : MatchingMemberTree)
    (order : MatchingCycleRecordOrder s) (legal : ∀ n ∈ tree.registryIds, 0 < n ∧ n < s.nr 76) :
    tree.recordsAbove s.nm (s.nr 77) (s.nr 80+3*s.nr 55) := by
  induction tree with
  | nil => trivial
  | leaf v tail ih => exact ih legal
  | blossom p n c tail ci ti =>
    have allocated := legal n (by simp [MatchingMemberTree.registryIds])
    have bound := (order.bounded n allocated.1 allocated.2).1
    unfold matchingRebaseScratchEnd matchingCycleRecordStart at bound
    exact ⟨by omega, ci (fun id h => legal id (by simp [MatchingMemberTree.registryIds,h])),
      ti (fun id h => legal id (by simp [MatchingMemberTree.registryIds,h]))⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem MatchingAugmentPreparedRegistry.nextStage {k i : ℕ} {cost : Fin k → Fin k → ℝ}
    {old next : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition old}
    {forest : AlternatingForestState (Fin k)} {original before base out : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest before} {registry : MatchingRegistryView dual}
    {cycles : MatchingLiveCycles registry} {rows : List (Fin k × Fin k)} {nextPart : CompactMatchingPartition next}
    {jobs : List MatchingRebaseTask} {prepared : MatchingPreparedLift base jobs (compactPrimalMateWord next)}
    (view : MatchingAugmentPreparedRegistry cycles rows nextPart prepared)
    (completed : MatchingRebaseCompletedRows prepared.lift jobs out)
    (storage : MatchingStageStorage k original before) (order : MatchingCycleRecordOrder before)
    (capacity : ∀ n < before.nr 76, n < matchingBlossomCapacity k)
    (reads : MatchingRefreshInput before part.representative (fun v => alternatingRoleCode (forest.role v))
      cost (effectiveVertexPotential old.cuts old.potential old.cutDual))
    (sameCuts : next.cuts = old.cuts) (sameBlocks : nextPart.blocks.block = part.blocks.block)
    (potential : next.potential = old.potential) (cutDual : next.cutDual = old.cutDual)
    (primal : CompactMatchingPrimalDualMemory next original out) (count : next.edges.card = i)
    (top : CompactTopMatching nextPart) (internal : next.InternalCuts)
    (keep : ∀ r ∈ matchingFixedStorageRegisters ++ [68,76], out.nr r = before.nr r)
    (real : out.rm = before.rm) (cursor : out.nr 76 ≤ 6*k*i+1) :
    Nonempty (MatchingBetweenStages cost original i (matchingStageSnapshot out)) := by
  have port (r : ℕ) (safe : r ∈ matchingFixedStorageRegisters ++ [68,76] := by decide) := keep r safe
  have outStore := storage.keeps (t := out) (fun r h => port r (List.mem_append.mpr (.inl h)))
  have headers (n : ℕ) (low : 0 < n) (high : n < before.nr 76) :=
    view.completedHeaders completed storage capacity (port 77) (port 78) low high
  have newOrder : MatchingCycleRecordOrder out := order.transport
    (by simp only [matchingRebaseScratchEnd,port 80,port 55]) (port 76) (port 68)
    (fun n lo hi => (headers n lo hi).1)
    (fun n lo hi => by simp only [matchingCycleRecordEnd,(headers n lo hi).1,(headers n lo hi).2])
  have middle (address : ℕ) (low : before.nr 50+k ≤ address) (high : address < before.nr 79) :
      out.nm address = base.nm address := by
    apply completed.headers
    simp only [matchingRebaseHeaderArea,view.frame.fixed 50 (by decide), view.frame.fixed 55 (by decide),
      view.frame.fixed 79 (by decide),dual.dimension]
    exact ⟨low,high⟩
  have lowMemory (address : ℕ) (bound : address < before.nr 50) : out.nm address = before.nm address :=
    (completed.lowMemory address (by rwa [view.frame.fixed 50 (by decide)])).trans (view.lowMemory address bound)
  have m := storage.warm.matesBefore
  have r := storage.warm.representativesAfter
  have cache := storage.warm.candidatesAfter
  have table := storage.warm.pairsAfter
  have beforeNode := storage.nodes
  have starts := storage.starts
  have lens := storage.lengths
  have left := storage.traceLeft
  have right := storage.traceRight
  have marks := storage.traceMarks
  have witness := storage.witnesses
  have record := storage.records
  have promotion := storage.promotion
  have mask := storage.mask
  have map := storage.memberMap
  have stack := storage.memberStack
  have roleBytes (address : ℕ) (lo : before.nr 51 ≤ address) (hi : address < before.nr 51+3*k) :
      out.nm address = before.nm address :=
    (middle address (by omega) (by omega)).trans (view.forestMemory address lo hi)
  have roles : AlternatingForestMemory forest (out.nr 51) out.nm := by
    rw [port 51]
    intro v
    have hi := v.isLt
    simp only [roleBytes (before.nr 51+v.val) (by omega) (by omega),
      roleBytes (before.nr 51+k+v.val) (by omega) (by omega),
      roleBytes (before.nr 51+k+k+v.val) (by omega) (by omega)]
    exact dual.roles v
  have representatives (v : Fin k) : out.nm (out.nr 57+v.val) = (nextPart.representative v).val := by
    rw [port 57, middle _ (by have := v.isLt; omega) (by have := v.isLt; omega)]
    exact view.representatives v
  have effective (v : Fin k) : out.rm (out.nr 62+v.val) =
      effectiveVertexPotential next.cuts next.potential next.cutDual v := by
    rw [port 62,real,sameCuts,potential,cutDual]
    exact dual.effective v
  have nodes (v : Fin k) : blossomNodeAt out v =
      if nextPart.representative v = v ∧ (nextPart.blocks.block v).card ≠ 1
        then dual.node (nextPart.blocks.block v) else 0 := by
    have asModel := matchingAugmentTopNodes_represented part.representative part.representative_idem
      (fun p => blossomNodeAt before p) (fun p h => (dual.top p).trans (if_neg (fun hit => h hit.1))) rows view.unique v
    have moved : blossomNodeAt out v =
        if v = nextPart.representative v then blossomNodeAt before (part.representative v) else 0 := by
      unfold blossomNodeAt at ⊢
      rw [port 74, middle _ (by have := v.isLt; omega) (by have := v.isLt; omega), view.topNodes]
      rw [view.chosenPorts]
      exact asModel
    have same : part.blocks.block (part.representative v) = nextPart.blocks.block v := by
      rw [sameBlocks]
      exact part.same_block.mp (part.representative_idem v)
    rw [moved]
    by_cases fixed : nextPart.representative v = v
    · have value := dual.top (part.representative v)
      simp only [part.representative_idem, true_and, same] at value
      simpa only [fixed, if_true, true_and] using value
    · simp only [if_neg (Ne.symm fixed), fixed, false_and, if_false]
  let newDual : MatchingSearchDualMemory nextPart forest out := {
    dimension := primal.dimension
    separated := by rw [port 62,port 75]; exact dual.separated
    reps := representatives
    roles := roles
    effective := effective
    node := dual.node
    nodeNonzero B h := dual.nodeNonzero B (sameCuts ▸ h)
    nodeInjective := by rw [sameCuts]; exact dual.nodeInjective
    cutValues B h := by rw [port 75,real,cutDual]; exact dual.cutValues B (sameCuts ▸ h)
    top := nodes }
  have newReads : MatchingRefreshInput out nextPart.representative (fun v => alternatingRoleCode (forest.role v))
      cost (effectiveVertexPotential next.cuts next.potential next.cutDual) := by
    have layout : MatchingCacheLayout k out := by
      refine ⟨(port 55).trans reads.layout.dimension, (port 61).trans reads.layout.rows, ?_, ?_, ?_, ?_⟩
      · rw [port 58,port 61,port 54]; exact reads.layout.idsBefore
      · rw [port 54,port 61,port 65]; exact reads.layout.recordsBefore
      · rw [port 59,port 61,port 60]; exact reads.layout.slacksBefore
      · rw [port 60,port 61,port 66]; exact reads.layout.ratesBefore
    refine ⟨layout, ?_, ?_, ?_, ?_, ?_, ?_, representatives,
      fun v => (roles v).1, ?_, effective⟩
    · rw [port 21,port 58]; exact reads.offsetsBefore
    · rw [port 57,port 58]; exact reads.representativesBefore
    · rw [port 51,port 58]; exact reads.rolesBefore
    · rw [port 20,port 59]; exact reads.metricBefore
    · rw [port 62,port 59]; exact reads.effectiveBefore
    · intro v
      have space := storage.warm.offsetsBefore
      rw [port 21, lowMemory _ (by have := v.isLt; omega)]
      exact reads.offsets v
    · intro a b
      rw [port 20,real]
      exact reads.metric a b
  let f := matchingAugmentRelabel (matchingAugmentNodePort next old.cuts dual.node)
  let entry (B : Finset (Fin k)) (h : B ∈ next.cuts) : MatchingLiveCycle next dual.node B :=
    let live : B ∈ old.cuts := sameCuts ▸ h
    let e := cycles.entry B live
    let size : 2 ≤ e.geometry.cycle.length := e.arity ▸ (cycles.memory B live).members.proper.2.1
    e.afterAugment _ (view.cycleShape B live) sameCuts potential cutDual size
  have bounds (n : ℕ) (seen : n ∈ registry.trees.registryIds) : 0 < n ∧ n < before.nr 76 := by
    obtain ⟨B,live,id⟩ := (registry.keys n).mp seen
    rw [← id]
    exact ⟨Nat.pos_of_ne_zero (dual.nodeNonzero B live),registry.allocated B live⟩
  have rootIds (B : Finset (Fin k)) (h : B ∈ old.cuts) (n : ℕ)
      (seen : n ∈ dual.node B :: (cycles.entry B h).tree.registryIds) : n ∈ registry.trees.registryIds := by
    rcases List.mem_cons.mp seen with id | below
    · exact (registry.keys n).mpr ⟨B,h,id.symm⟩
    · exact cycles.ids B h n below
  have encoding (tree : MatchingMemberTree) (proper : tree.proper) (encoded : tree.encoded before.nm (before.nr 77) (before.nr 78))
      (ids : ∀ n ∈ tree.registryIds, n ∈ registry.trees.registryIds) : (tree.relabel f).encoded out.nm (out.nr 77) (out.nr 78) := by
    apply tree.relabel_encoded f proper encoded
    · intro n seen
      obtain ⟨lo,hi⟩ := bounds n (ids n seen)
      exact headers n lo hi
    · intro n seen index within
      obtain ⟨B,live,rfl⟩ := (registry.keys n).mp (ids n seen)
      have size := (cycles.memory B live).rows.length
      have fits : index < (cycles.entry B live).geometry.cycle.length := size ▸ within
      exact view.completedKey completed B live ⟨index,fits⟩
  have baseOfTop (q : Fin k) (fixed : part.representative q = q)
      (big : (part.blocks.block q).card ≠ 1) :
      f (dual.node (part.blocks.block q)) q.val = (nextPart.representative q).val := by
    let B := part.blocks.block q
    let live : B ∈ old.cuts := part.blocks.cut_mem (Finset.mem_univ _) big
    let shape := view.cycleShape B live
    let p := nextPart.representative q
    have inB : p ∈ B := by
      have := nextPart.inside q
      simpa only [sameBlocks] using this
    have other : matchingCutPort next B p := by
      refine ⟨inB, ?_⟩
      intro edge found atP inBlock
      have isFixed : nextPart.representative p = p := nextPart.representative_idem q
      have block : nextPart.blocks.block p = B := by
        rw [sameBlocks]
        exact part.blocks.same_of_mem (Finset.mem_univ q) inB
      exact top.internal_avoids_base isFixed found (fun v hv => block.symm ▸ inBlock v hv) atP
    have portEq := ((matchingCutPort_of_inner next shape.belongs shape.internal (Finset.filter_subset _ _)).2 p other)
    change matchingAugmentNodePort next old.cuts dual.node (dual.node B) = p.val
    exact shape.portWord.trans (congrArg Fin.val portEq.symm)
  let newRegistry := registry.afterAugment (newDual := newDual) sameCuts sameBlocks rfl (port 76) outStore
    newOrder f baseOfTop (fun v => encoding _ (registry.trees.proper v) (registry.trees.encoded v)
      (fun n seen => List.mem_flatMap.mpr ⟨v,List.mem_finRange v,seen⟩))
  have headerArea (n : ℕ) (hi : n < out.nr 76) :
      matchingRebaseHeaderArea out (out.nr 77+n) ∧ matchingRebaseHeaderArea out (out.nr 78+n) := by
    have fits := capacity n (by rwa [port 76] at hi)
    simp only [matchingRebaseHeaderArea,port 50,port 55,port 77,port 78,port 79, dual.dimension]
    omega
  have memory (B : Finset (Fin k)) (h : B ∈ next.cuts) : MatchingLiveCycleMemory (entry B h) out := by
    let live : B ∈ old.cuts := sameCuts ▸ h
    let e := cycles.entry B live
    let n := dual.node B
    let root := MatchingMemberTree.blossom 0 n e.tree .nil
    let newRoot := root.relabel f
    have oldMemory := cycles.memory B live
    have mem := oldMemory.members
    have rootBound (j : ℕ) (found : j ∈ newRoot.registryIds) : 0 < j ∧ j < out.nr 76 := by
      rw [port 76]
      apply bounds j
      apply rootIds B live j
      simpa only [newRoot,MatchingMemberTree.relabel_ids,root,MatchingMemberTree.registryIds,List.append_nil] using found
    have oldWell : root.proper := mem.proper
    have oldEncoding : root.encoded before.nm (before.nr 77) (before.nr 78) := mem.encoded
    have newEncoding := encoding root oldWell oldEncoding (fun j hj => rootIds B live j
      (by simpa only [root,MatchingMemberTree.registryIds,List.append_nil] using hj))
    have safe := newRoot.readable_archive newOrder (by rw [port 79,port 55,port 80,dual.dimension,stack])
      newEncoding rootBound (fun j h => headerArea j (rootBound j h).2)
    have readable := MatchingMemberTree.readable_after_move (tree := newRoot) safe (fun _ _ => rfl)
    have above := newRoot.recordsAbove_of_order newOrder rootBound
    let b := matchingRebaseNodeState out n
    have members : MatchingMemberRoot b (entry B h).tree := by
      refine ⟨(MatchingMemberTree.relabel_proper root f).2 oldWell, newEncoding, ?_, above, ?_, ?_, ?_⟩
      · change newRoot.readable out.nm (out.nr 77) (out.nr 78) (outsideMatchingMemberScratch out)
        exact readable
      · change (e.tree.relabel f).leaves.Nodup
        rw [MatchingMemberTree.relabel_leaves]
        exact mem.unique
      · intro a ha
        change a ∈ (e.tree.relabel f).leaves at ha
        rw [MatchingMemberTree.relabel_leaves] at ha
        exact (port 55).symm ▸ mem.valid a ha
      · change out.nr 79+out.nr 55 ≤ out.nr 80
        rw [port 79,port 55,port 80]
        exact mem.separated
    have hdr := headers n (Nat.pos_of_ne_zero (dual.nodeNonzero B live)) (registry.allocated B live)
    refine ⟨members,⟨?_,?_⟩⟩
    · change out.nm (out.nr 78+n) = (e.geometry.cycle.map (view.cycleShape B live).choose.choose).length
      rw [hdr.2,List.length_map]
      exact oldMemory.rows.length
    · intro j
      let idx : Fin e.geometry.cycle.length := ⟨j.val, by
        have fits : j.val < (e.geometry.cycle.map (view.cycleShape B live).choose.choose).length := j.isLt
        simpa only [List.length_map] using fits⟩
      let choose := (view.cycleShape B live).choose.choose
      change let row := matchingCycleChildAt out.nm (matchingCycleRecordStart out n + 4*j.val)
        row.representative = ((e.geometry.cycle.map choose).get j).val ∧
          (row.endpointA,row.endpointB) = ((e.geometry.edges idx).1.val,(e.geometry.edges idx).2.val)
      rw [hdr.1]
      change let row := matchingRebaseRowsAt before out n idx.val
        row.representative = ((e.geometry.cycle.map choose).get j).val ∧
          (row.endpointA,row.endpointB) = ((e.geometry.edges idx).1.val,(e.geometry.edges idx).2.val)
      rw [view.completedChild completed B live idx]
      exact ⟨congrArg Fin.val (List.getElem_map choose).symm,(oldMemory.rows.records idx).2⟩
  let activeCycles : MatchingLiveCycles newRegistry := by
    refine ⟨entry,memory,?_,?_,?_⟩
    · intro p h fixed
      let q := part.representative p
      let B := nextPart.blocks.block p
      let live : B ∈ old.cuts := sameCuts ▸ h
      let shape := view.cycleShape B live
      have oldFixed : part.representative q = q := part.representative_idem p
      have same : part.blocks.block q = B := by
        change part.blocks.block q = nextPart.blocks.block p
        rw [sameBlocks]
        exact part.same_block.mp oldFixed
      have qLarge : (part.blocks.block q).card ≠ 1 := by
        rw [same]
        have := registry.nontrivial B live
        omega
      have label : nextPart.representative q = p :=
        (nextPart.same_block.mpr (by rw [sameBlocks]; exact same.trans (congrFun sameBlocks p))).trans fixed
      have baseLabel : f (dual.node B) q.val = p.val := by
        have atRoot := baseOfTop q oldFixed qLarge
        rw [same,label] at atRoot
        exact atRoot
      have baseEq : shape.base = p := Fin.ext (shape.portWord.symm.trans baseLabel)
      have oldTree : registry.trees.tree q = .blossom q.val (dual.node B) (cycles.entry B live).tree .nil := by
        have prior := (cycles.top q (same.symm ▸ live) oldFixed).2
        have atCut {C : Finset (Fin k)} (hc : C ∈ old.cuts) (eq : C = B) :
            (cycles.entry C hc).tree = (cycles.entry B live).tree := by
          subst C
          rfl
        exact prior.trans (congrArg₂ (fun n c => MatchingMemberTree.blossom q.val n c .nil)
          (congrArg dual.node same) (atCut (same.symm ▸ live) same))
      have swap : matchingAugmentTopSwap part.representative nextPart.representative p = q := by
        change (if p = q then nextPart.representative p else if p = nextPart.representative p then q else p) = q
        rw [fixed]
        by_cases eq : p = q <;> simp [eq]
      refine ⟨baseEq, ?_⟩
      change ((registry.trees.tree (matchingAugmentTopSwap part.representative nextPart.representative p)).relabel f) =
        .blossom p.val (dual.node B) ((cycles.entry B live).tree.relabel f) .nil
      rw [swap, oldTree]
      change MatchingMemberTree.blossom (f (dual.node B) q.val) (dual.node B)
        ((cycles.entry B live).tree.relabel f) .nil = _
      rw [baseLabel]
    · intro B h job listed sub child
      let live : B ∈ old.cuts := sameCuts ▸ h
      let e := cycles.entry B live
      let shape := view.cycleShape B live
      change job ∈ (e.tree.relabel f).jobs none at listed
      rw [e.tree.relabel_jobs] at listed
      obtain ⟨source,used,rfl⟩ := List.mem_map.mp listed
      rw [(source.augmentationRelabel _).2.2] at child
      cases form : source.children with
      | none => simp [form] at child
      | some oldSub =>
        have subEq : oldSub.relabel f = sub := by
          simpa only [form,Option.map_some,Option.some.injEq] using child
        obtain ⟨C,hC,n,tree,root,block⟩ := cycles.child B live source used oldSub form
        let retained : C ∈ next.cuts := sameCuts.symm ▸ hC
        let oldChild := cycles.entry C hC
        let newChild := view.cycleShape C hC
        have written : source.liftPort (matchingAugmentNodePort next old.cuts dual.node) = newChild.base.val := by
          rw [MatchingMemberJob.liftPort,form]
          rw [← n]
          exact newChild.portWord
        have key := (source.augmentationRelabel (matchingAugmentNodePort next old.cuts dual.node)).1
        have renamed : shape.choose.choose oldChild.base = newChild.base :=
          Fin.ext ((shape.labels source used oldChild.base root.symm).symm.trans written)
        refine ⟨C,retained,n.trans (source.augmentationRelabel (matchingAugmentNodePort next old.cuts dual.node)).2.1.symm,?_,written.symm.trans key.symm,?_⟩
        · change oldChild.tree.relabel f = sub
          exact (congrArg (MatchingMemberTree.relabel f) tree).trans subEq
        · change C = (e.ports.relabel sameCuts shape.choose.choose shape.choose.members).block newChild.base
          rw [← renamed, e.ports.relabel_block sameCuts shape.choose.choose shape.choose.members oldChild.base
            (e.owner source used oldChild.base root.symm).1]
          exact block
    · intro B h n seen
      have live : B ∈ old.cuts := sameCuts ▸ h
      have oldTree : n ∈ (cycles.entry B live).tree.registryIds := by
        change n ∈ ((cycles.entry B live).tree.relabel f).registryIds at seen
        rwa [MatchingMemberTree.relabel_ids] at seen
      obtain ⟨D,hD,eq⟩ := (registry.keys n).mp (cycles.ids B live n oldTree)
      exact (newRegistry.keys n).mpr ⟨D,sameCuts.symm ▸ hD,eq⟩
  let graph : CompactMatchingInterstage cost original i out :=
    ⟨next,nextPart,top,count,internal,primal,representatives,effective⟩
  let result : MatchingBetweenStages cost original i out :=
    ⟨graph,forest,newDual,newRegistry,activeCycles,outStore,newOrder,cursor,newReads⟩
  exact ⟨result.reframe (t := matchingStageSnapshot out) rfl rfl
    (fun r stage _ => Function.update_of_ne stage _ _)⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAugmentNextStage

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

structure MatchingResolvedOuter {k : ℕ} (forest : AlternatingForestState (Fin k))
    (u v : Fin k) (base : ℕ) (s t : ArithmeticState) : Prop where
  tag : t.nr 35 = if forest.commonAncestor u v = none then 3 else 1
  selected : t.nr 1 = s.nr 91
  zero : t.nr 36 = 0
  leftCount : t.nr 10 = (forest.traceToRoot u).length
  rightCount : t.nr 11 = (forest.traceToRoot v).length
  left : ForestTraceArray t.nm (s.nr 83) (forest.traceToRoot u)
  right : ForestTraceArray t.nm (s.nr 84) (forest.traceToRoot v)
  shared : t.nr 12 = ((forest.commonAncestor u v).map Fin.val).getD k
  split : ForestTraceSplit (forest.traceToRoot u) (forest.traceToRoot v)
    (forest.commonAncestor u v) (t.nr 13) (t.nr 14)
  natural : ∀ a, a < base ∨ base + 3 * k ≤ a → t.nm a = s.nm a
  registers : ∀ r, r ∉ [1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 35, 36] → t.nr r = s.nr r
  realRegisters : t.rr = s.rr
  realMemory : t.rm = s.rm

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

/-! matching/MatchingDispatchAugment.lean -/
section RppSource_MatchingDispatchAugment
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3200000 in
/-- The two-root event leaves the actual dispatcher with one additional
original matched edge and the typed archive for the next search. -/
theorem MatchingDispatchState.augment {k i : ℕ} {cost : Fin k → Fin k → ℝ}
    {original s classified : ArithmeticState} {classTicks : ℕ}
    (before : MatchingDispatchState cost original i s) (searching : i < k/2)
    (entry : s.pc = 0) (running : s.halted = false) (outer : matchingEventClass s = 1)
    (winner : s.nr 1 ≤ s.nr 61)
    (classify : BlockRuns classifyAndTraceMatchingEvent classTicks s classified) (tag : classified.nr 35 = 3) :
    ∃ next ticks, BlockRuns weightedBlossomEventHandler ticks s next ∧
      next.halted = false ∧ next.nr 33 = 0 ∧
      Nonempty (MatchingBetweenStages cost original (i+1) (matchingStageSnapshot next)) ∧
      ticks ≤ 512 * (k^2+1) := by
  obtain ⟨a,b,selected,_,pa,pb,left,right,middle,spent,classBound,actual,midLive,zero,one,two,
    id,ends,natural,real,rr,fixed,ready,leftBase,rightBase,trace⟩ := before.traceOuter entry running outer
  obtain ⟨sameTicks,sameExit⟩ := actual.same_exit classify
  subst middle
  have classCost : classTicks ≤ 34*k+57 := sameTicks ▸ classBound
  have different : before.forest.commonAncestor (before.part.representative a) (before.part.representative b) = none := by
    by_contra joined
    have same := trace.tag
    rw [if_neg joined] at same
    omega
  let m := {classified with pc := 0}
  have mTag : m.nr 35 = 3 := tag
  have port (r : ℕ) (used : r = 9 ∨ r = 20 ∨ r = 21 ∨ (30 ≤ r ∧ r ≤ 34) ∨
      (39 ≤ r ∧ r ≤ 90) ∨ 100 ≤ r := by decide) : m.nr r = s.nr r := fixed r used
  have regs (r : ℕ) (used : r = 9 ∨ r = 20 ∨ r = 21 ∨ r = 39 ∨ (50 ≤ r ∧ r ≤ 90) ∨ 100 ≤ r) :
      m.nr r = s.nr r := port r (by omega)
  let picked := before.afterTrace (t := m) searching winner natural real rr id regs
  let delta : DualBound (MatchingDualEvent k) := ⟨picked.selected.event, m.rr 1⟩
  let state := picked.state.advanceSearch picked.part picked.search picked.positive picked.internal delta picked.selected.adjustment
  let part := picked.part.advanceSearch picked.search picked.positive picked.internal delta picked.selected.adjustment
  let snap := matchingAugmentDualPoint m
  obtain ⟨advanced,nodes,trees⟩ :=
    picked.selected.contractionDualSnapshot picked.search picked.internal rfl midLive picked.one picked.storage
  let cycles := picked.cycles.advanceDual picked.search picked.positive picked.internal delta picked.selected.adjustment
    advanced.registry nodes trees rfl (fun _ _ => rfl)
  have top : CompactTopMatching part := ⟨picked.top.interior,picked.top.matchedBase⟩
  have allCuts : state.InternalCuts := picked.internal
  have primal : CompactMatchingPrimalDualMemory state original m := by
    let old := picked.selected.primal
    exact ⟨old.dimension,old.oddMap,old.mateAbove,old.mate,old.saved,old.natural,old.real⟩
  have tight : matchingLiftTight state s(a,b) := by
    have step := picked.selected.adjustment.2.2.2
    have event : picked.selected.event = .edge s(a,b) := selected
    rw [event] at step
    exact step.2.2
  have traces : MatchingForestTraceResult picked.forest (part.representative a) (part.representative b)
      (m.nr 83) m m := by
    refine ⟨trace.leftCount,trace.rightCount,?_,?_,trace.shared,trace.split,fun _ _ => rfl,fun _ _ => rfl,rfl,rfl⟩
    · rw [port 83,← leftBase]
      exact trace.left
    · rw [port 84,← rightBase]
      exact trace.right
  have room (n : ℕ) (low : n < m.nr 76) : n < matchingBlossomCapacity k :=
    picked.budget.allocated_fits searching low
  obtain ⟨next,nextPart,t,ticks,arm,live,armBound,_,off,_,_,numbers,primalNext,increased,
    internalNext,topNext,sameBlocks,sameCuts,potential,cutDual,base,jobs,prepared,view,completed⟩ :=
    matchingAugmentationHandlerBlock_selectedLift cycles top allCuts advanced.search.valid advanced.links
      advanced.witnesses primal picked.storage picked.order room (a,b) left right different rfl tight traces ends rfl midLive picked.one
  have fixedAtExit (r : ℕ) (safe : r ∈ matchingFixedStorageRegisters ++ [68,76]) : t.nr r = snap.nr r :=
    matchingAugmentationHandlerBlock_preserves arm r (by simp [matchingFixedStorageRegisters] at safe; simp; omega)
  have exitReal : t.rm = snap.rm := by
    have size := picked.storage.warm.size
    change t.rm = iterateBlossomDuals {m with rm := advancedEffectiveMemory m} (m.nr 55)
    rwa [size]
  have count : next.edges.card = i+1 := increased.trans (congrArg (· + 1) picked.count)
  have snapStorage := picked.storage.keeps (t := snap) (fun _ _ => rfl)
  have snapOrder := picked.order.transport (t := snap) rfl rfl rfl (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  have between := view.nextStage completed snapStorage snapOrder room advanced.reads sameCuts sameBlocks potential cutDual
    primalNext count topNext internalNext fixedAtExit exitReal (picked.budget.finish (fixedAtExit 76 (by decide)))
  have armByTag : BlockRuns (match m.nr 35 with
        | 0 => matchingGrowHandlerWithWitnesses
        | 1 => matchingContractionHandlerBlock
        | 2 => matchingExpandHandlerBlock
        | _ => matchingAugmentationHandlerBlock) ticks m t := by
    rw [mTag]
    exact arm
  obtain ⟨d,dispatchCost,dispatched⟩ :=
    dispatchMatchingActionBlock_spec (s := m) (t := t) rfl midLive live zero one two (by omega) armByTag
  exact ⟨_,classTicks+d,classify.append dispatched,live,off,between,by omega⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingDispatchAugment

open VehicleRoutingSurvey.Routing SupplyChainTheory in
theorem solution : (fun {P : Prop} (_ : P) => P) (@VehicleRoutingSurvey.Routing.MatchingDispatchState.augment) :=
  @VehicleRoutingSurvey.Routing.MatchingDispatchState.augment
