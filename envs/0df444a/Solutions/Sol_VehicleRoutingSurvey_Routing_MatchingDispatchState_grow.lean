-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.MatchingDispatchState.grow
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T15:23:39.436651+00:00
-- url     : https://prove2.me/submissions/d76c1969-c6ac-46ea-a32c-6b4d6bc55533

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatchingInterface

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





theorem oddCutDualEdgeValue_mk {n : ℕ} (cuts : Finset (Finset (Fin n)))
    (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ) {u v : Fin n} (distinct : u ≠ v) :
    oddCutDualEdgeValue cuts potential cutDual s(u, v) = potential u + potential v +
      ∑ S ∈ cuts.filter (fun S => (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S)), cutDual S := by
  have sameCuts : cuts.filter (MatchingCrossesCut · s(u, v)) =
      cuts.filter (fun S => (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S)) := Finset.ext fun S => by
    simp only [Finset.mem_filter, matchingCrossesCut_mk_iff S distinct]
  simp [oddCutDualEdgeValue, sameCuts, Sym2.toFinset_mk_eq, Finset.sum_insert, distinct]





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



theorem CompactMatchingPartition.same_block {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) {u v : Fin k} :
    part.representative u = part.representative v ↔ part.blocks.block u = part.blocks.block v := by
  refine ⟨?_, part.constant u v⟩
  intro same
  have first := part.blocks.same_of_mem (Finset.mem_univ u) (part.inside u)
  have second := part.blocks.same_of_mem (Finset.mem_univ v) (part.inside v)
  rw [same] at first
  exact first.symm.trans second

theorem CompactMatchingPartition.representative_idem {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (v : Fin k) :
    part.representative (part.representative v) = part.representative v :=
  part.same_block.mpr (part.blocks.same_of_mem (Finset.mem_univ v) (part.inside v))



theorem CompactMatchingPartition.exposed_fixed {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    {v : Fin k} (exposed : v ∉ state.covered) : part.representative v = v := by
  by_contra different
  exact exposed (part.coveredAway v v (part.blocks.self_mem v (Finset.mem_univ v)) (Ne.symm different))



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

/-! matching/AlternatingForestGrow.lean -/
section RppSource_AlternatingForestGrow
namespace VehicleRoutingSurvey.Routing







/-- Reach a matched, unlabelled pair through a tight edge from an existing outer node. -/
def AlternatingForestState.grow {α : Type*} [DecidableEq α] (state : AlternatingForestState α)
    (source inner outer : α) : AlternatingForestState α where
  role x := if x = inner then .inner source else if x = outer then .outer (some inner) else state.role x
  depth x := if x = inner then state.depth source + 1
    else if x = outer then state.depth source + 2 else state.depth x

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

/-! matching/AlternatingForestTrace.lean -/
section RppSource_AlternatingForestTrace
namespace VehicleRoutingSurvey.Routing



theorem AlternatingForestState.parent_valid {α : Type*}
    {state : AlternatingForestState α} {mate : α → Option α} {tight : α → α → Prop}
    (valid : state.valid mate tight) {x : α} (marked : state.role x ≠ .unlabelled) :
    match (state.role x).parent with
    | none => state.role x = .outer none ∧ mate x = none
    | some p => state.role p ≠ .unlabelled ∧ state.depth p < state.depth x ∧ tight p x := by
  have old := valid x
  cases kind : state.role x with
  | unlabelled => exact (marked kind).elim
  | outer parent =>
    try rw [kind] at old
    cases parent with
    | none => exact ⟨rfl, old⟩
    | some p =>
      obtain ⟨⟨q, pRole⟩, _, _, edge, earlier⟩ := old
      exact ⟨by simp [pRole], earlier, edge⟩
  | inner p =>
    try rw [kind] at old
    obtain ⟨⟨q, pRole⟩, _, _, edge, earlier⟩ := old
    exact ⟨by simp [pRole], earlier, edge⟩









end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestTrace

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



theorem external_edge_dual_eq_effectivePotential {n : ℕ} {O : Finset (Fin n)}
    {cuts : Finset (Finset (Fin n))} (blocks : TopLevelMatchingBlocks O cuts)
    (nested : ∀ S ∈ cuts, ∀ u ∈ S, ∀ v ∈ S, blocks.block u = blocks.block v)
    (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ) {u v : Fin n}
    (separate : blocks.block u ≠ blocks.block v) :
    oddCutDualEdgeValue cuts potential cutDual s(u, v) =
      effectiveVertexPotential cuts potential cutDual u + effectiveVertexPotential cuts potential cutDual v := by
  have different : u ≠ v := fun equal => separate (congrArg blocks.block equal)
  rw [oddCutDualEdgeValue_mk cuts potential cutDual different]
  have cutSum : (∑ S ∈ cuts.filter (fun S => (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S)), cutDual S) =
      (∑ S ∈ cuts.filter (u ∈ ·), cutDual S) + ∑ S ∈ cuts.filter (v ∈ ·), cutDual S := by
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S inCuts
    by_cases insideU : u ∈ S <;> by_cases insideV : v ∈ S
    · exact (separate (nested S inCuts u insideU v insideV)).elim
    all_goals simp [insideU, insideV]
  rw [cutSum]
  unfold effectiveVertexPotential
  abel

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

theorem growOuterCacheSide_frames (source target : ℕ) (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ t ticks, ticks ≤ 35 ∧ BlockRuns (growOuterCacheSide source target) ticks s t ∧
      t.halted = false ∧ CacheMemoryFrame s t :=
  growOuterCacheSide_bound source target s entry running one dict bucket

private theorem growOuterCache_bound : CacheBlockBounded insertMatchingOuterEdgeBlock 73 := by
  exact CacheBlockBounded.append (m := 3) (n := 70) normalizeGrowthSlack_bound
    (CacheBlockBounded.append (growOuterCacheSide_bound 26 17) (growOuterCacheSide_bound 17 26) rfl) rfl





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

theorem refreshGrowthNeighborBlock_memory (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ t steps, steps ≤ 95 ∧ BlockRuns refreshGrowthNeighborBlock steps s t ∧ t.halted = false ∧ CacheMemoryFrame s t :=
  refreshGrowthNeighborBlock_frames s entry running one dict bucket



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

theorem refreshSelectedOuterVertex_bound (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ t steps, steps ≤ s.nr 55 * 98 + 2 ∧ BlockRuns refreshSelectedOuterVertex steps s t ∧
      t.halted = false ∧ ∀ a < s.nr 58, t.nm a = s.nm a := by
  obtain ⟨t, steps, cost, run, live, natural, _⟩ := refreshSelectedOuterVertex_spec s entry running one dict bucket
  exact ⟨t, steps, cost, run, live, natural⟩

theorem refreshSelectedOuterVertex_no_write {r : ℕ}
    (away : r ∉ [0, 6, 10, 11, 16, 17, 18, 19, 25]) :
    ∀ i ∈ refreshSelectedOuterVertex, naturalDestination i ≠ r :=
  naturalDestination_ne_of_list [0, 6, 10, 11, 16, 17, 18, 19, 25] (by decide) away











theorem readGrowthCacheSource_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    let next := { s with
      pc := 3
      nr := Function.update (Function.update (Function.update s.nr 15 (s.nr 24 + s.nr 14))
        6 (s.nr 57 + (s.nr 24 + s.nr 14))) 17 (s.nm (s.nr 57 + (s.nr 24 + s.nr 14))) }
    BlockRuns readGrowthCacheSource 3 s next := by
  dsimp only
  apply BlockRuns.of_running_exit
  · simp [readGrowthCacheSource, arithmeticStep, Function.iterate_succ_apply', entry, running]
  · exact running
  · rfl

private theorem nilBlockRuns (s : ArithmeticState) (entry : s.pc = 0) :
    BlockRuns [] 0 s s := by
  exact ⟨fun i early => (Nat.not_lt_zero i early).elim, by simp, entry⟩

private theorem selectedGrowthCacheSource_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ t steps, steps ≤ s.nr 55 * 98 + 3 ∧ BlockRuns selectedGrowthCacheSource steps s t ∧
      t.halted = false ∧ t.nr 27 = s.nr 27 + 1 ∧
      t.nr 9 = s.nr 9 ∧ t.nr 24 = s.nr 24 ∧ t.nr 55 = s.nr 55 ∧
      ∀ a < s.nr 58, t.nm a = s.nm a := by
  let bumped := {s with pc := 1, nr := Function.update s.nr 27 (s.nr 27 + 1)}
  have bump : BlockRuns [.natAdd 27 27 9] 1 s bumped := by
    apply BlockRuns.of_running_exit
    · simp [bumped, arithmeticStep, entry, running, one]
    · exact running
    · rfl
  let loaded := {bumped with pc := 0}
  have oneAt : loaded.nr 9 = 1 := by simp [loaded, bumped, one]
  have dimension : loaded.nr 55 = s.nr 55 := by simp [loaded, bumped]
  have dictAt : loaded.nr 58 ≤ loaded.nr 54 := by simpa [loaded, bumped] using dict
  have bucketAt : loaded.nr 58 ≤ loaded.nr 65 := by simpa [loaded, bumped] using bucket
  obtain ⟨t, steps, short, run, live, earlier⟩ := refreshSelectedOuterVertex_bound loaded rfl running oneAt dictAt bucketAt
  have fixed {r : ℕ} (away : r ∉ [0, 6, 10, 11, 16, 17, 18, 19, 25]) :
      t.nr r = loaded.nr r := by
    rw [← run.run, arithmeticRun_keeps_register (refreshSelectedOuterVertex_no_write away)]
  refine ⟨_, 1 + steps, by omega, bump.append run, live, ?_, ?_, ?_, ?_, ?_⟩
  · change t.nr 27 = s.nr 27 + 1
    rw [fixed (by decide)]
    simp [loaded, bumped]
  · change t.nr 9 = s.nr 9
    rw [fixed (by decide), oneAt, one]
  · change t.nr 24 = s.nr 24
    rw [fixed (by decide)]
    simp [loaded, bumped]
  · exact (fixed (by decide)).trans dimension
  · intro a before
    exact earlier a (by simpa [loaded, bumped] using before)

private theorem refreshGrowthCacheSourceBlock_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ (t : ArithmeticState) (steps : ℕ) (selected : Bool), BlockRuns refreshGrowthCacheSourceBlock steps s t ∧
      t.halted = false ∧ t.nr 9 = s.nr 9 ∧ t.nr 24 = s.nr 24 ∧ t.nr 55 = s.nr 55 ∧
      t.nr 27 = s.nr 27 + selected.toNat ∧ steps ≤ 8 + (s.nr 55 * 98 + 2) * selected.toNat ∧
      selected = decide (s.nm (s.nr 57 + (s.nr 24 + s.nr 14)) = s.nr 26) ∧
      ∀ a < s.nr 58, t.nm a = s.nm a := by
  let fetched := { s with
    pc := 3
    nr := Function.update (Function.update (Function.update s.nr 15 (s.nr 24 + s.nr 14)) 6
      (s.nr 57 + (s.nr 24 + s.nr 14))) 17 (s.nm (s.nr 57 + (s.nr 24 + s.nr 14))) }
  have reads : BlockRuns readGrowthCacheSource 3 s fetched := readGrowthCacheSource_spec s entry running
  let p := {fetched with pc := 0}
  have pOne : p.nr 9 = 1 := by simp [p, fetched, one]
  have fixed9 : p.nr 9 = s.nr 9 := by simp [p, fetched]
  have fixed24 : p.nr 24 = s.nr 24 := by simp [p, fetched]
  have fixed55 : p.nr 55 = s.nr 55 := by simp [p, fetched]
  have fixed27 : p.nr 27 = s.nr 27 := by simp [p, fetched]
  have number : p.nr 17 = s.nm (s.nr 57 + (s.nr 24 + s.nr 14)) := by simp [p, fetched]
  have peer : p.nr 26 = s.nr 26 := by simp [p, fetched]
  have pDict : p.nr 58 ≤ p.nr 54 := by simpa [p, fetched] using dict
  have pBucket : p.nr 58 ≤ p.nr 65 := by simpa [p, fetched] using bucket
  by_cases upper : p.nr 17 ≤ p.nr 26
  · by_cases lower : p.nr 26 ≤ p.nr 17
    · obtain ⟨t, steps, short, scanned, live, count, oneAgain, index, dimension, earlier⟩ :=
        selectedGrowthCacheSource_spec p rfl running pOne pDict pBucket
      have inner := branchOnAtMost_left 26 17 selectedGrowthCacheSource [] (s := p) rfl running lower scanned live
      have outer := branchOnAtMost_left 17 26 _ [] (s := p) rfl running upper inner live
      have accepted : s.nm (s.nr 57 + (s.nr 24 + s.nr 14)) = s.nr 26 :=
        number.symm.trans ((Nat.le_antisymm upper lower).trans peer)
      rw [fixed55] at short
      refine ⟨_, 3 + (1 + (1 + steps + 1) + 1), true, reads.append outer, live, oneAgain.trans fixed9,
        index.trans fixed24, dimension.trans fixed55, by
          change t.nr 27 = s.nr 27 + 1
          rw [count, fixed27], by
          change 3 + (1 + (1 + steps + 1) + 1) ≤ 8 + (s.nr 55 * 98 + 2) * 1
          omega, by simp [accepted], ?_⟩
      intro a before
      exact earlier a (by simpa [p, fetched] using before)
    · have inner := branchOnAtMost_right 26 17 selectedGrowthCacheSource [] (s := p) rfl running
        (Nat.lt_of_not_ge lower) (nilBlockRuns p rfl) running
      have outer := branchOnAtMost_left 17 26 _ [] (s := p) rfl running upper inner running
      have rejected : s.nm (s.nr 57 + (s.nr 24 + s.nr 14)) ≠ s.nr 26 := by
        rw [← number, ← peer]
        exact fun eq => lower eq.ge
      exact ⟨_, 3 + (1 + (1 + 0) + 1), false, reads.append outer, running, fixed9, fixed24, fixed55,
        by change p.nr 27 = s.nr 27; exact fixed27, by simp, by simp [rejected], fun _ _ => rfl⟩
  · have outer := branchOnAtMost_right 17 26 (branchOnAtMost 26 17 selectedGrowthCacheSource []) []
      (s := p) rfl running (Nat.lt_of_not_ge upper) (nilBlockRuns p rfl) running
    have rejected : s.nm (s.nr 57 + (s.nr 24 + s.nr 14)) ≠ s.nr 26 := by
      rw [← number, ← peer]
      exact fun eq => upper eq.le
    exact ⟨_, 3 + (1 + 0), false, reads.append outer, running, fixed9, fixed24, fixed55,
      by change p.nr 27 = s.nr 27; exact fixed27, by simp, by simp [rejected], fun _ _ => rfl⟩

theorem growthCacheSourceBlock_no_write {r : ℕ}
    (away : r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 25, 27]) :
    ∀ ins ∈ refreshGrowthCacheSourceBlock, naturalDestination ins ≠ r :=
  naturalDestination_ne_of_list [0, 6, 10, 11, 15, 16, 17, 18, 19, 25, 27] (by decide) away

private theorem growthCacheSourceBlock_keeps {s t : ArithmeticState} {steps : ℕ}
    (run : BlockRuns refreshGrowthCacheSourceBlock steps s t) {r : ℕ}
    (base : r ∈ [14, 26, 54, 57, 58, 65]) : t.nr r = s.nr r := by
  have away : r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 25, 27] := by simp at base ⊢; omega
  exact run.run ▸ arithmeticRun_keeps_register (growthCacheSourceBlock_no_write away) s steps

theorem refreshMatchingNewOuterBlock_keeps {s t : ArithmeticState} {steps r : ℕ}
    (run : BlockRuns refreshMatchingNewOuterBlock steps s t)
    (away : r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 27]) : t.nr r = s.nr r := by
  rw [← run.run]
  exact arithmeticRun_keeps_from_destination_list [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 27]
    (by decide) away s steps

def matchingGrowthMembers (s : ArithmeticState) (i : ℕ) : ℕ :=
  ((List.range i).filter fun j => decide (s.nm (s.nr 57 + j) = s.nr 26)).length

private theorem matchingGrowthMembers_succ (s : ArithmeticState) (i : ℕ) :
    matchingGrowthMembers s (i + 1) = matchingGrowthMembers s i +
      (decide (s.nm (s.nr 57 + i) = s.nr 26)).toNat := by
  by_cases accepts : s.nm (s.nr 57 + i) = s.nr 26 <;>
    simp [matchingGrowthMembers, List.range_succ, List.filter_append, accepts]

private structure GrowthCacheScan (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  live : s.halted = false
  index : s.nr 24 = i
  dimension : s.nr 55 = initial.nr 55
  one : s.nr 9 = 1
  count : s.nr 27 ≤ i
  countExact : s.nr 27 = matchingGrowthMembers initial i
  registers : ∀ r ∈ [14, 26, 54, 57, 58, 65], s.nr r = initial.nr r
  natural : ∀ a < initial.nr 58, s.nm a = initial.nm a

/-- The filtered scan pays a linear overhead, then a linear cost for each selected
source. The measured count in register 27 is exactly the number of originals in the
new outer block. Memory preceding the cache tables stays intact. -/
theorem refreshMatchingNewOuterBlock_bound (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65)
    (repBefore : s.nr 57 + s.nr 55 ≤ s.nr 58) :
    ∃ t steps, BlockRuns refreshMatchingNewOuterBlock steps s t ∧ t.halted = false ∧
      t.nr 27 = matchingGrowthMembers s (s.nr 55) ∧ steps ≤ 11 * s.nr 55 + (s.nr 55 * 98 + 2) * t.nr 27 + 3 ∧
      (∀ a < s.nr 58, t.nm a = s.nm a) ∧ (∀ r ∈ [14, 26, 54, 57, 58, 65], t.nr r = s.nr r) := by
  let k := s.nr 55
  let seeded := {s with pc := 2, nr := Function.update (Function.update s.nr 24 0) 27 0}
  have seeds : BlockRuns initGrowthCacheScan 2 s seeded := by
    apply BlockRuns.of_running_exit
    · simp [seeded, arithmeticStep, initGrowthCacheScan, Function.iterate_succ_apply', entry, running]
    · exact running
    · rfl
  let start := {seeded with pc := 0}
  let charge := k * 98 + 2
  let potential := fun t : ArithmeticState => charge * (k - t.nr 27)
  have ready : GrowthCacheScan s 0 start := by
    refine ⟨rfl, running, by simp [start, seeded], by simp [start, seeded], by simpa [start, seeded] using one,
      by simp [start, seeded], by simp [start, seeded, matchingGrowthMembers], ?_, fun _ _ => rfl⟩
    intro r hr
    have a : r ≠ 24 := by simp at hr; omega
    have b : r ≠ 27 := by simp at hr; omega
    simp [start, seeded, Function.update_of_ne a, Function.update_of_ne b]
  have control (i : ℕ) (m : ArithmeticState) (valid : GrowthCacheScan s i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 24 = i ∧ m.nr 55 = k :=
    ⟨valid.entry, valid.live, valid.index, valid.dimension⟩
  have iteration (i : ℕ) (less : i < k) (m : ArithmeticState) (valid : GrowthCacheScan s i m) :
      ∃ t steps,
      let next := {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)}
      BlockRuns refreshGrowthCacheSourceBlock steps m t ∧ t.halted = false ∧
        GrowthCacheScan s (i + 1) next ∧ steps + potential next ≤ 8 + potential m := by
    have floor : m.nr 58 = s.nr 58 := valid.registers 58 (by decide)
    have mDict : m.nr 58 ≤ m.nr 54 := by simpa [floor, valid.registers 54 (by decide)] using dict
    have mBucket : m.nr 58 ≤ m.nr 65 := by simpa [floor, valid.registers 65 (by decide)] using bucket
    obtain ⟨t, steps, selected, ran, live, tOne, index, dimension, visits, short, picked, prior⟩ :=
      refreshGrowthCacheSourceBlock_spec m valid.entry valid.live valid.one mDict mBucket
    let next := {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)}
    have nextCount : next.nr 27 = m.nr 27 + selected.toNat := by simpa [next] using visits
    have selBound : selected.toNat ≤ 1 := by cases selected <;> decide
    have newCount : next.nr 27 ≤ i + 1 := by have old := valid.count; omega
    have balance : (k - next.nr 27) + selected.toNat = k - m.nr 27 := by omega
    have short' : steps ≤ 8 + charge * selected.toNat := by simpa [charge, valid.dimension] using short
    have read : m.nm (s.nr 57 + i) = s.nm (s.nr 57 + i) := valid.natural _ (by dsimp [k] at less; omega)
    have zeroAt : m.nr 14 = 0 := (valid.registers 14 (by decide)).trans zero
    have selection : selected = decide (s.nm (s.nr 57 + i) = s.nr 26) := by
      simpa only [valid.registers 57 (by decide), valid.registers 26 (by decide), valid.index, zeroAt, Nat.add_zero, read]
        using picked
    have exactCount : next.nr 27 = matchingGrowthMembers s (i + 1) := by
      rw [nextCount, matchingGrowthMembers_succ, selection, valid.countExact]
    refine ⟨t, steps, ran, live, ?_, ?_⟩
    · change GrowthCacheScan s (i + 1) next
      exact ⟨rfl, live, by simp [next, index, valid.index, tOne, valid.one],
        by simp [next, dimension, valid.dimension], by simp [next, tOne, valid.one], newCount, exactCount,
        fun r hr => by
          have away : r ≠ 24 := by simp at hr; omega
          simpa [next, Function.update_of_ne away] using (growthCacheSourceBlock_keeps ran hr).trans (valid.registers r hr),
        fun a ha => (prior a (floor.symm ▸ ha)).trans (valid.natural a ha)⟩
    · change steps + charge * (k - next.nr 27) ≤ 8 + charge * (k - m.nr 27)
      rw [← balance, Nat.mul_add]
      omega
  obtain ⟨last, steps, done, cost, complete⟩ := countedLoop_amortized 9 24 55 k 8
    refreshGrowthCacheSourceBlock (GrowthCacheScan s) potential ready control iteration
  have used := done.count
  have credits : charge * (k - last.nr 27) + charge * last.nr 27 = charge * k := by
    rw [← Nat.mul_add, Nat.sub_add_cancel used]
  have seededCount : start.nr 27 = 0 := by simp [start, seeded]
  change steps + charge * (k - last.nr 27) ≤ k * (8 + 3) + charge * (k - start.nr 27) + 1 at cost
  simp only [seededCount, Nat.sub_zero] at cost
  refine ⟨_, 2 + steps, seeds.append complete, done.live, done.countExact, ?_, done.natural, done.registers⟩
  change 2 + steps ≤ 11 * k + charge * last.nr 27 + 3
  rw [Nat.mul_comm 11 k]
  omega

end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowCacheRAM

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

/-- Executing the growth block produces an encoding of the next valid alternating forest. -/
theorem alternatingForestGrowBlock_valid {n : ℕ} {forest : AlternatingForestState (Fin n)}
    {base : ℕ} {s : ArithmeticState} (entry : s.pc = 0) (running : s.halted = false)
    (before : AlternatingForestMemory forest base s.nm)
    {mate : Fin n → Option (Fin n)} {tight : Fin n → Fin n → Prop} (valid : forest.valid mate tight)
    {source inner outer : Fin n} {parent : Option (Fin n)}
    (sourceArg : s.nr 0 = source.val) (innerArg : s.nr 1 = inner.val) (outerArg : s.nr 2 = outer.val)
    (roleBase : s.nr 3 = base) (parentBase : s.nr 4 = base + n) (depthBase : s.nr 5 = base + n + n)
    (sourceRole : forest.role source = .outer parent)
    (innerRole : forest.role inner = .unlabelled) (outerRole : forest.role outer = .unlabelled)
    (distinct : inner ≠ outer) (mateInner : mate inner = some outer) (mateOuter : mate outer = some inner)
    (tightIncoming : tight source inner) (tightMatched : tight inner outer) :
    let next := forest.grow source inner outer
    let result := (arithmeticStep alternatingForestGrowBlock)^[18] s
    BlockRuns alternatingForestGrowBlock 18 s result ∧
      AlternatingForestMemory next base result.nm ∧ next.valid mate tight := by
  obtain ⟨block, memory, _, _, _⟩ := alternatingForestGrowBlock_spec s entry running
  exact ⟨block, memory.symm ▸ alternatingForestGrownMemory_encodes before sourceArg innerArg outerArg
      roleBase parentBase depthBase distinct,
    AlternatingForestState.grow_valid valid sourceRole innerRole outerRole distinct mateInner mateOuter
      tightIncoming tightMatched⟩

end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestMemory

/-! matching/AlternatingStageRoots.lean -/
section RppSource_AlternatingStageRoots
namespace VehicleRoutingSurvey.Routing

/-- All exposed active nodes are roots. Active mates are distinct, reciprocal and tight. -/
structure AlternatingStageRoots {α : Type*} (state : AlternatingForestState α)
    (active : Finset α) (mate : α → Option α) (tight : α → α → Prop) : Prop where
  forest : state.valid mate tight
  exposedRoots : ∀ v ∈ active, mate v = none → state.role v = .outer none
  partners : ∀ v ∈ active, ∀ w, mate v = some w → w ∈ active ∧ v ≠ w ∧ mate w = some v ∧ tight v w

/-- Start the next augmenting search with exactly the exposed active nodes as roots. -/
def resetAlternatingForest {α : Type*} [DecidableEq α] (active : Finset α) (mate : α → Option α) :
    AlternatingForestState α where
  role v := if v ∈ active ∧ mate v = none then .outer none else .unlabelled
  depth _ := 0

theorem resetAlternatingForest_valid {α : Type*} [DecidableEq α]
    (active : Finset α) (mate : α → Option α) (tight : α → α → Prop)
    (partners : ∀ v ∈ active, ∀ w, mate v = some w → w ∈ active ∧ v ≠ w ∧ mate w = some v ∧ tight v w) :
    AlternatingStageRoots (resetAlternatingForest active mate) active mate tight where
  forest := by
    intro v
    by_cases root : v ∈ active ∧ mate v = none
    · simp [resetAlternatingForest, root]
    · simp [resetAlternatingForest, root]
  exposedRoots v hv free := by simp [resetAlternatingForest, hv, free]
  partners := partners





end VehicleRoutingSurvey.Routing
end RppSource_AlternatingStageRoots

/-! matching/MatchingCacheRealFrame.lean -/
section RppSource_MatchingCacheRealFrame
namespace VehicleRoutingSurvey.Routing

def updatedRealRegister : ArithmeticInstruction → Option ℕ
  | .realConst dst _ | .realAdd dst _ _ | .realSub dst _ _ | .realMul dst _ _
    | .realDiv dst _ _ | .realLoad dst _ => some dst
  | _ => none

private theorem arithmeticStep_keeps_cache_real {code : List ArithmeticInstruction} {r : ℕ}
    (avoids : ∀ ins ∈ code, updatedRealRegister ins ≠ some r) (s : ArithmeticState) :
    (arithmeticStep code s).rr r = s.rr r := by
  by_cases stopped : s.halted = true
  · simp [arithmeticStep, stopped]
  cases fetched : code[s.pc]? with
  | none => simp [arithmeticStep, stopped, fetched]
  | some ins =>
    have other := avoids ins (List.mem_of_getElem? fetched)
    cases ins <;> simp [updatedRealRegister] at other <;>
      simp (disch := omega) [arithmeticStep, stopped, fetched, Function.update_of_ne]

theorem BlockRuns.keeps_cache_real {code : List ArithmeticInstruction} {s t : ArithmeticState} {steps r : ℕ}
    (run : BlockRuns code steps s t) (avoids : code.all (fun ins => decide (updatedRealRegister ins ≠ some r)) = true) :
    t.rr r = s.rr r := by
  have writes : ∀ ins ∈ code, updatedRealRegister ins ≠ some r := fun ins present =>
    of_decide_eq_true (List.all_eq_true.mp avoids ins present)
  rw [← run.run]
  clear run
  induction steps with
  | zero => rfl
  | succ steps ih => rw [Function.iterate_succ_apply', arithmeticStep_keeps_cache_real writes, ih]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingCacheRealFrame

/-! matching/MatchingWarmPrimal.lean -/
section RppSource_MatchingWarmPrimal
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



theorem CompactMatchingPrimalDual.partialMate_some_iff {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) {v w : Fin k} : state.partialMate v = some w ↔
      s(v, w) ∈ state.edges := by
  by_cases covered : v ∈ state.covered
  · rw [CompactMatchingPrimalDual.partialMate, if_pos covered, Option.some.injEq]
    constructor
    · rintro rfl
      exact mateOfMatching_edge state.perfect covered
    · intro known
      have equal := (state.perfect.2 v covered).unique
        ⟨mateOfMatching_edge state.perfect covered, Sym2.mem_mk_left _ _⟩
        ⟨known, Sym2.mem_mk_left _ _⟩
      rcases Sym2.eq_iff.mp equal with direct | reversal
      · exact direct.2
      · exact reversal.2.trans reversal.1
  · rw [CompactMatchingPrimalDual.partialMate, if_neg covered]
    constructor
    · intro impossible
      cases impossible
    · intro impossible
      exact (covered ((state.perfect.1 _ impossible).2 v (Sym2.mem_mk_left _ _))).elim

theorem CompactMatchingPrimalDualMemory.partialMate_word {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {original s : ArithmeticState}
    (before : CompactMatchingPrimalDualMemory state original s) (v : Fin k) :
    s.nm (s.nr 50 + v.val) = (state.partialMate v).elim k Fin.val := by
  by_cases h : v ∈ state.covered <;> simp [before.mate, CompactMatchingPrimalDual.partialMate, h]



def CompactMatchingPartition.activeRepresentatives {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) : Finset (Fin k) :=
  Finset.univ.filter fun v => part.representative v = v

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



theorem CompactTopMatching.resetForest {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    (top : CompactTopMatching part) :
    let forest := resetAlternatingForest part.activeRepresentatives state.partialMate
    AlternatingStageRoots forest part.activeRepresentatives state.partialMate part.tightBetween ∧
      CompactMatchingSearchForest part forest state.partialMate part.tightBetween := by
  intro forest
  have roots := resetAlternatingForest_valid part.activeRepresentatives state.partialMate part.tightBetween
    (fun v active w mate => by
      have edge := (state.partialMate_some_iff).mp mate
      have separated := top.matchedBase ((part.mem_activeRepresentatives v).mp active) mate
      obtain ⟨vBase, wBase⟩ := top.crossing_endpoints edge separated
      exact ⟨(part.mem_activeRepresentatives w).mpr wBase, (fun eq => separated (congrArg part.blocks.block eq)),
        state.partialMate_some_iff.mpr (Sym2.eq_swap ▸ edge), v, w, vBase, wBase, state.tight _ edge⟩)
  refine ⟨roots, ⟨roots.forest, ?_, ?_⟩⟩
  · intro v w edge separated
    obtain ⟨vBase, wBase⟩ := top.crossing_endpoints edge separated
    rw [vBase, wBase]
    exact ⟨state.partialMate_some_iff.mpr edge, state.partialMate_some_iff.mpr (Sym2.eq_swap ▸ edge)⟩
  · intro v uncovered
    rw [part.exposed_fixed uncovered]
    apply roots.exposedRoots v ((part.mem_activeRepresentatives v).mpr (part.exposed_fixed uncovered))
    simp [CompactMatchingPrimalDual.partialMate, uncovered]




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









theorem saveMatchingGrowthOriginalEdge_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns saveMatchingGrowthOriginalEdge 6 s t ∧ t.halted = false ∧
      (t.nr 22, t.nr 23) = matchingOriginalGrowthEvent s ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ r, r ∉ [0, 6, 22, 23] → t.nr r = s.nr r) := by
  let t := (arithmeticStep saveMatchingGrowthOriginalEdge)^[6] s
  have exit : t.pc = saveMatchingGrowthOriginalEdge.length ∧ t.halted = false ∧
      (t.nr 22, t.nr 23) = matchingOriginalGrowthEvent s ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, saveMatchingGrowthOriginalEdge, matchingOriginalGrowthEvent, arithmeticStep, entry, running,
      one, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl exit.2.1 exit.1,
    exit.2.1, exit.2.2.1, exit.2.2.2.1, exit.2.2.2.2.1, exit.2.2.2.2.2, ?_⟩
  intro r away
  apply arithmeticRun_keeps_register
  simp [saveMatchingGrowthOriginalEdge, naturalDestination] at away ⊢ <;> omega

def matchingSavedGrowthEvent (s : ArithmeticState) : ℕ × ℕ := (s.nr 22, s.nr 23)



def matchingGrowthWitnessStored (s : ArithmeticState) : ℕ → ℕ :=
  writeMatchingForestWitness
    (writeMatchingForestWitness s.nm (s.nr 90) (s.nr 28) (matchingSavedGrowthEvent s))
    (s.nr 90) (s.nr 26) (s.nr 28, s.nr 26)

set_option maxRecDepth 4096 in
theorem storeMatchingGrowthWitnesses_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns storeMatchingGrowthWitnesses 10 s t ∧ t.halted = false ∧
      t.nm = matchingGrowthWitnessStored s ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ r, r ∉ [0, 6] → t.nr r = s.nr r) := by
  let t := (arithmeticStep storeMatchingGrowthWitnesses)^[10] s
  have computed : t.pc = storeMatchingGrowthWitnesses.length ∧ t.halted = false ∧
      t.nm = matchingGrowthWitnessStored s ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, storeMatchingGrowthWitnesses, arithmeticStep, Function.iterate_succ_apply', entry, running,
      one, matchingGrowthWitnessStored, writeMatchingForestWitness, forestWitnessAddress, matchingSavedGrowthEvent]
  refine ⟨t, BlockRuns.of_running_exit rfl computed.2.1 computed.1,
    computed.2.1, computed.2.2.1, computed.2.2.2.1, computed.2.2.2.2, ?_⟩
  intro r away
  apply arithmeticRun_keeps_register
  simp [storeMatchingGrowthWitnesses, naturalDestination] at away ⊢ <;> omega





def orientedMatchingGrowthEdge (s : ArithmeticState) : ℕ × ℕ :=
  if s.nm (s.nr 57 + s.nr 22) = s.nr 28 then (s.nr 23, s.nr 22) else (s.nr 22, s.nr 23)



private theorem orientMatchingGrowthEdge_spec (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t steps, steps ≤ 8 ∧ BlockRuns orientMatchingGrowthEdge steps s t ∧ t.halted = false ∧
      (t.nr 22, t.nr 23) = orientedMatchingGrowthEdge s ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 10, 14, 22, 23] → t.nr r = s.nr r := by
  have build (steps : ℕ) (cost : steps ≤ 8)
      (computed : let t := (arithmeticStep orientMatchingGrowthEdge)^[steps] s
        t.pc = orientMatchingGrowthEdge.length ∧ t.halted = false ∧
        (t.nr 22, t.nr 23) = orientedMatchingGrowthEdge s ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr) :
      ∃ t steps, steps ≤ 8 ∧ BlockRuns orientMatchingGrowthEdge steps s t ∧ t.halted = false ∧
        (t.nr 22, t.nr 23) = orientedMatchingGrowthEdge s ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
        ∀ r, r ∉ [0, 6, 10, 14, 22, 23] → t.nr r = s.nr r := by
    obtain ⟨exit, live, edge, natural, real, rr⟩ := computed
    exact ⟨_, steps, cost, BlockRuns.of_running_exit rfl live exit, live, edge, natural, real, rr,
      fun _ away => arithmeticRun_keeps_from_destination_list [0, 6, 10, 14, 22, 23] (by decide) away s steps⟩
  rcases lt_trichotomy (s.nm (s.nr 57 + s.nr 22)) (s.nr 28) with before | equal | after
  · apply build 4 (by decide)
    simp [orientMatchingGrowthEdge, orientedMatchingGrowthEdge, arithmeticStep, entry, running,
      before.le, before.ne, not_le.mpr before, Function.iterate_succ_apply']
  · apply build 8 le_rfl
    simp [orientMatchingGrowthEdge, orientedMatchingGrowthEdge, arithmeticStep, entry, running, equal,
      Function.iterate_succ_apply']
  · apply build 3 (by decide)
    simp [orientMatchingGrowthEdge, orientedMatchingGrowthEdge, arithmeticStep, entry, running,
      after.ne', not_le.mpr after, Function.iterate_succ_apply']



theorem storeOrientedMatchingGrowthWitnesses_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t steps, steps ≤ 18 ∧ BlockRuns storeOrientedMatchingGrowthWitnesses steps s t ∧ t.halted = false ∧
      t.nm = writeMatchingForestWitness
        (writeMatchingForestWitness s.nm (s.nr 90) (s.nr 28) (orientedMatchingGrowthEdge s))
        (s.nr 90) (s.nr 26) (s.nr 28, s.nr 26) ∧ t.rm = s.rm ∧ t.rr = s.rr := by
  obtain ⟨middle, ticks, short, first, live, edge, natural, real, rr, keep⟩ :=
    orientMatchingGrowthEdge_spec s entry running
  let ready := {middle with pc := 0}
  have unit : ready.nr 9 = 1 := (keep 9 (by decide)).trans one
  obtain ⟨t, second, tLive, packed, tReal, tRR, _⟩ := storeMatchingGrowthWitnesses_spec ready rfl live unit
  refine ⟨_, ticks + 10, by omega, first.append second, tLive, ?_, tReal.trans real, tRR.trans rr⟩
  change t.nm = _
  have saved : matchingSavedGrowthEvent ready = orientedMatchingGrowthEdge s := edge
  rw [packed]
  unfold matchingGrowthWitnessStored
  rw [show ready.nm = s.nm from natural, show ready.nr 90 = s.nr 90 from keep 90 (by decide),
    show ready.nr 28 = s.nr 28 from keep 28 (by decide), show ready.nr 26 = s.nr 26 from keep 26 (by decide), saved]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingForestWitnessRAM

/-! matching/MatchingBlossomDualRAM.lean -/
section RppSource_MatchingBlossomDualRAM
namespace VehicleRoutingSurvey.Routing



def blossomRoleAt (s : ArithmeticState) (i : ℕ) : ℕ :=
  s.nm (s.nr 51 + i)

noncomputable def blossomDualAfterDelta (s : ArithmeticState) (i : ℕ) : ℝ :=
  let old := s.rm (s.nr 75 + blossomNodeAt s i)
  if blossomRoleAt s i ≤ 1 then old + s.rr 1 else old - s.rr 1

noncomputable def modifyBlossomDualAt (s : ArithmeticState) (i : ℕ) : ℕ → ℝ :=
  if blossomNodeAt s i = 0 ∨ blossomRoleAt s i = 0 then s.rm
  else Function.update s.rm (s.nr 75 + blossomNodeAt s i) (blossomDualAfterDelta s i)



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



noncomputable def iterateBlossomDuals (s : ArithmeticState) : ℕ → (ℕ → ℝ)
  | 0 => s.rm
  | i + 1 => modifyBlossomDualAt {s with rm := iterateBlossomDuals s i} i

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

def effectiveRoleAt (s : ArithmeticState) (index : ℕ) : ℕ :=
  s.nm (s.nr 51 + s.nm (s.nr 57 + index))

noncomputable def effectivePotentialAfterDelta (s : ArithmeticState) (index : ℕ) : ℝ :=
  let role := effectiveRoleAt s index
  let old := s.rm (s.nr 62 + index)
  if role = 0 then old else if role ≤ 1 then old + s.rr 1 else old - s.rr 1



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

/-! matching/MatchingGrowCutRAM.lean -/
section RppSource_MatchingGrowCutRAM
namespace VehicleRoutingSurvey.Routing

def innerCutCandidateSlot (s : ArithmeticState) : ℕ :=
  s.nr 55 + s.nr 55 + s.nr 28

def matchingInnerNode (s : ArithmeticState) : ℕ :=
  s.nm (s.nr 74 + s.nr 28)









def readyGrowthInnerNode (s : ArithmeticState) : ArithmeticState :=
  {s with pc := 4, nr := Function.update (Function.update
    (Function.update (Function.update s.nr 6 (s.nr 74 + s.nr 28)) 10 (matchingInnerNode s))
    18 (s.nr 55 + s.nr 55)) 18 (innerCutCandidateSlot s)}

noncomputable def growthInnerCutData (s : ArithmeticState) : ArithmeticState :=
  {s with
    pc := 5
    nr := Function.update (Function.update
      (Function.update s.nr 6 (s.nr 75 + s.nr 10)) 15 (s.nr 28)) 16 (s.nr 55)
    rr := Function.update (Function.update s.rr 0 (s.rm (s.nr 75 + s.nr 10))) 4 1}

private theorem readyGrowthInnerNode_runs (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    BlockRuns readGrowthInnerNode 4 s (readyGrowthInnerNode s) := by
  apply BlockRuns.of_running_exit
  · simp [readyGrowthInnerNode, readGrowthInnerNode, matchingInnerNode, innerCutCandidateSlot, arithmeticStep,
      Function.iterate_succ_apply', entry, running]
  · exact running
  · rfl

private theorem growthInnerCutData_runs (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 14 = 0) :
    BlockRuns prepareGrowthInnerCut 5 s (growthInnerCutData s) := by
  apply BlockRuns.of_running_exit
  · simp [growthInnerCutData, prepareGrowthInnerCut, arithmeticStep, Function.iterate_succ_apply', entry, running, zero]
  · exact running
  · rfl

noncomputable def installedMatchingInnerCutNat (s : ArithmeticState) : ℕ → ℕ :=
  if matchingInnerNode s = 0 then Function.update s.nm (s.nr 58 + innerCutCandidateSlot s) 0
  else installedMatchingCandidateNat (growthInnerCutData (readyGrowthInnerNode s))

noncomputable def installedMatchingInnerCutReal (s : ArithmeticState) : ℕ → ℝ :=
  if matchingInnerNode s = 0 then s.rm
  else installedMatchingCandidateReal (growthInnerCutData (readyGrowthInnerNode s))

theorem installedMatchingInnerCutNat_preserves_prefix (s : ArithmeticState)
    (dict : s.nr 58 ≤ s.nr 54) (a : ℕ) (before : a < s.nr 58) :
    installedMatchingInnerCutNat s a = s.nm a := by
  by_cases empty : matchingInnerNode s = 0 <;>
    simp (disch := omega) [installedMatchingInnerCutNat, empty, installedMatchingCandidateNat,
      readyGrowthInnerNode, growthInnerCutData, Function.update_of_ne]

theorem activateMatchingInnerCut_keeps_register {s t : ArithmeticState} {steps r : ℕ}
    (run : BlockRuns activateMatchingInnerCut steps s t)
    (away : r ∉ [0, 6, 10, 15, 16, 18]) : t.nr r = s.nr r := by
  rw [← run.run]
  exact arithmeticRun_keeps_from_destination_list [0, 6, 10, 15, 16, 18] (by decide) away s steps

theorem activateMatchingInnerCut_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0) :
    ∃ t steps, steps ≤ 22 ∧ BlockRuns activateMatchingInnerCut steps s t ∧
      t.halted = false ∧ t.nm = installedMatchingInnerCutNat s ∧ t.rm = installedMatchingInnerCutReal s := by
  let read := {readyGrowthInnerNode s with pc := 0}
  have readNode := readyGrowthInnerNode_runs s entry running
  have readId : read.nr 10 = matchingInnerNode s := by simp [read, readyGrowthInnerNode]
  have readZero : read.nr 14 = 0 := by simp [read, readyGrowthInnerNode, zero]
  have readSlot : read.nr 18 = innerCutCandidateSlot s := by simp [read, readyGrowthInnerNode]
  by_cases empty : matchingInnerNode s = 0
  · let t := { read with
      pc := 2
      nr := Function.update read.nr 6 (s.nr 58 + innerCutCandidateSlot s)
      nm := Function.update s.nm (s.nr 58 + innerCutCandidateSlot s) 0 }
    have cleared : BlockRuns clearGrowthInnerCut 2 read t := by
      apply BlockRuns.of_running_exit
      · simp [t, clearGrowthInnerCut, arithmeticStep, Function.iterate_succ_apply', readZero,
          readSlot, read, readyGrowthInnerNode, running, zero]
      · exact running
      · rfl
    have left := branchOnAtMost_left 10 14 clearGrowthInnerCut
      (appendBlock prepareGrowthInnerCut storeMatchingCandidateCell) (s := read) rfl running
      (by rw [readId, readZero, empty]) cleared running
    refine ⟨_, 8, by decide, readNode.append left, running, ?_, ?_⟩
    · change t.nm = installedMatchingInnerCutNat s
      simp [t, installedMatchingInnerCutNat, empty]
    · change t.rm = installedMatchingInnerCutReal s
      simp [t, read, readyGrowthInnerNode, installedMatchingInnerCutReal, empty]
  · let data := {growthInnerCutData read with pc := 0}
    have prep := growthInnerCutData_runs read rfl running readZero
    have oneAt : data.nr 9 = 1 := by simp [data, growthInnerCutData, read, readyGrowthInnerNode, one]
    let written := (arithmeticStep storeMatchingCandidateCell)^[12] data
    obtain ⟨write, live, natEffect, realEffect⟩ := storeMatchingCandidateCell_spec data rfl running oneAt
    have wrote : BlockRuns (appendBlock prepareGrowthInnerCut storeMatchingCandidateCell) 17 read
        (relocateState prepareGrowthInnerCut.length written) := prep.append write
    have runningAfter : (relocateState prepareGrowthInnerCut.length written).halted = false := live
    have right := branchOnAtMost_right 10 14 clearGrowthInnerCut
      (appendBlock prepareGrowthInnerCut storeMatchingCandidateCell) (s := read) rfl running
      (by rw [readId, readZero]; exact Nat.pos_of_ne_zero empty) wrote runningAfter
    refine ⟨_, 22, le_rfl, readNode.append right, live, ?_, ?_⟩
    · change written.nm = installedMatchingInnerCutNat s
      have effect : written.nm = installedMatchingCandidateNat data := natEffect
      rw [effect, installedMatchingInnerCutNat, if_neg empty] <;> rfl
    · change written.rm = installedMatchingInnerCutReal s
      have effect : written.rm = installedMatchingCandidateReal data := realEffect
      rw [effect, installedMatchingInnerCutReal, if_neg empty] <;> rfl

end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowCutRAM

/-! matching/MatchingGrowEventRAM.lean -/
section RppSource_MatchingGrowEventRAM
namespace VehicleRoutingSurvey.Routing

def matchingChosenEdgeAddress (s : ArithmeticState) : ℕ :=
  s.nr 54 + ((s.nr 1 - 1) + (s.nr 1 - 1))

def matchingChosenLeftBlock (s : ArithmeticState) : ℕ :=
  s.nm (s.nr 57 + s.nm (matchingChosenEdgeAddress s))

def matchingChosenRightBlock (s : ArithmeticState) : ℕ :=
  s.nm (s.nr 57 + s.nm (matchingChosenEdgeAddress s + 1))

def matchingChosenGrowSource (s : ArithmeticState) : ℕ :=
  if s.nm (s.nr 51 + matchingChosenLeftBlock s) = 0 then matchingChosenRightBlock s
  else matchingChosenLeftBlock s

def matchingChosenGrowTarget (s : ArithmeticState) : ℕ :=
  if s.nm (s.nr 51 + matchingChosenLeftBlock s) = 0 then matchingChosenLeftBlock s
  else matchingChosenRightBlock s



set_option maxRecDepth 4096 in
private theorem readMatchingGrowEdge_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t, BlockRuns readMatchingGrowEdge 13 s t ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      t.nr 10 = matchingChosenLeftBlock s ∧ t.nr 11 = matchingChosenRightBlock s ∧
      t.nr 12 = s.nm (s.nr 51 + matchingChosenLeftBlock s) ∧ t.nr 14 = 0 ∧
      ∀ r ≥ 50, t.nr r = s.nr r := by
  let t := (arithmeticStep readMatchingGrowEdge)^[13] s
  have computed : t.pc = readMatchingGrowEdge.length ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      t.nr 10 = matchingChosenLeftBlock s ∧ t.nr 11 = matchingChosenRightBlock s ∧
      t.nr 12 = s.nm (s.nr 51 + matchingChosenLeftBlock s) ∧ t.nr 14 = 0 := by
    simp [t, arithmeticStep, readMatchingGrowEdge, Function.iterate_succ_apply', entry, running, one,
      matchingChosenLeftBlock, matchingChosenRightBlock, matchingChosenEdgeAddress]
  refine ⟨t, BlockRuns.of_running_exit rfl computed.2.1 computed.1, ?_⟩
  rcases computed.2 with ⟨live, natMemory, realMemory, left, right, label, zero⟩
  refine ⟨live, natMemory, realMemory, left, right, label, zero, ?_⟩
  intro r high
  have away6 : r ≠ 6 := by omega
  have away10 : r ≠ 10 := by omega
  have away11 : r ≠ 11 := by omega
  have away12 : r ≠ 12 := by omega
  have away14 : r ≠ 14 := by omega
  simp [t, arithmeticStep, readMatchingGrowEdge, Function.iterate_succ_apply', entry, running,
    away6, away10, away11, away12, away14]



private theorem copyGrowEndpoints_spec (x y : ℕ) (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 14 = 0) (unaffected : y ≠ 0) :
    BlockRuns (copyGrowEndpoints x y) 2 s
      {s with pc := 2, nr := Function.update (Function.update s.nr 0 (s.nr x)) 1 (s.nr y)} := by
  apply BlockRuns.of_running_exit
  · simp [copyGrowEndpoints, arithmeticStep, Function.iterate_succ_apply', entry, running, zero, unaffected]
  · exact running
  · rfl



private theorem orientGrowEndpoints_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 14 = 0) :
    ∃ t ticks, ticks ≤ 4 ∧ BlockRuns orientGrowEndpoints ticks s t ∧ t.halted = false ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.nr 0 = (if s.nr 12 = 0 then s.nr 11 else s.nr 10) ∧
      t.nr 1 = (if s.nr 12 = 0 then s.nr 10 else s.nr 11) ∧ t.nr 14 = 0 ∧
      ∀ r ≥ 50, t.nr r = s.nr r := by
  by_cases leftDormant : s.nr 12 = 0
  · have run := branchOnAtMost_left 12 14 (copyGrowEndpoints 11 10) (copyGrowEndpoints 10 11)
      entry running (by simp [leftDormant, zero]) (copyGrowEndpoints_spec 11 10 s entry running zero (by decide))
      (by exact running)
    refine ⟨_, 4, le_rfl, run, running, rfl, rfl, by simp [leftDormant], by simp [leftDormant], by simp [zero], ?_⟩
    intro r high
    simp [Function.update_of_ne (show r ≠ 1 by omega), Function.update_of_ne (show r ≠ 0 by omega)]
  · have run := branchOnAtMost_right 12 14 (copyGrowEndpoints 11 10) (copyGrowEndpoints 10 11)
      entry running (by omega) (copyGrowEndpoints_spec 10 11 s entry running zero (by decide)) (by exact running)
    refine ⟨_, 3, by decide, run, running, rfl, rfl, by simp [leftDormant], by simp [leftDormant], by simp [zero], ?_⟩
    intro r high
    simp [Function.update_of_ne (show r ≠ 1 by omega), Function.update_of_ne (show r ≠ 0 by omega)]



private theorem readGrowMateAndBases_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 14 = 0) :
    ∃ t, BlockRuns readGrowMateAndBases 5 s t ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      t.nr 0 = s.nr 0 ∧ t.nr 1 = s.nr 1 ∧ t.nr 2 = s.nm (s.nr 50 + s.nr 1) ∧
      t.nr 3 = s.nr 51 ∧ t.nr 4 = s.nr 52 ∧ t.nr 5 = s.nr 53 := by
  let t := (arithmeticStep readGrowMateAndBases)^[5] s
  have computes : t.pc = readGrowMateAndBases.length ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      t.nr 0 = s.nr 0 ∧ t.nr 1 = s.nr 1 ∧ t.nr 2 = s.nm (s.nr 50 + s.nr 1) ∧
      t.nr 3 = s.nr 51 ∧ t.nr 4 = s.nr 52 ∧ t.nr 5 = s.nr 53 := by
    simp [t, arithmeticStep, readGrowMateAndBases, Function.iterate_succ_apply', entry, running, zero]
  exact ⟨t, BlockRuns.of_running_exit rfl computes.2.1 computes.1, computes.2⟩



theorem prepareMatchingGrowBlock_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t ticks, ticks ≤ 22 ∧ BlockRuns prepareMatchingGrowBlock ticks s t ∧ t.halted = false ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.nr 0 = matchingChosenGrowSource s ∧ t.nr 1 = matchingChosenGrowTarget s ∧
      t.nr 2 = s.nm (s.nr 50 + matchingChosenGrowTarget s) ∧ t.nr 3 = s.nr 51 ∧
      t.nr 4 = s.nr 52 ∧ t.nr 5 = s.nr 53 := by
  obtain ⟨read, fetched, live, oldNat, oldReal, left, right, role, zero, stable⟩ :=
    readMatchingGrowEdge_spec s entry running one
  let orientedInput := {read with pc := 0}
  obtain ⟨oriented, ticks, small, chose, stillLive, natSame, realSame, src, dst, zeroAgain, fixed⟩ :=
    orientGrowEndpoints_spec orientedInput rfl live zero
  have sourceEq : oriented.nr 0 = matchingChosenGrowSource s := by
    simpa [orientedInput, matchingChosenGrowSource, role, left, right] using src
  have targetEq : oriented.nr 1 = matchingChosenGrowTarget s := by
    simpa [orientedInput, matchingChosenGrowTarget, role, left, right] using dst
  let loadedInput := {relocateState readMatchingGrowEdge.length oriented with pc := 0}
  obtain ⟨out, loaded, outLive, outNat, outReal, srcArg, dstArg, mateArg, roleBase, parentBase, depthBase⟩ :=
    readGrowMateAndBases_spec loadedInput rfl stillLive zeroAgain
  have codeRun := (fetched.append chose).append loaded
  have keep (r : ℕ) (high : 50 ≤ r) : loadedInput.nr r = s.nr r :=
    (fixed r high).trans (stable r high)
  refine ⟨_, 13 + ticks + 5, by omega, codeRun, outLive,
    outNat.trans (natSame.trans oldNat), outReal.trans (realSame.trans oldReal), srcArg.trans sourceEq,
    dstArg.trans targetEq, ?_, roleBase.trans (keep 51 (by decide)), parentBase.trans (keep 52 (by decide)),
    depthBase.trans (keep 53 (by decide))⟩
  have readsNat : loadedInput.nm = s.nm := natSame.trans oldNat
  have readsTarget : loadedInput.nr 1 = matchingChosenGrowTarget s := targetEq
  change out.nr 2 = s.nm (s.nr 50 + matchingChosenGrowTarget s)
  rw [mateArg, readsNat, keep 50 (by decide), readsTarget]



/-- Decode the selected outer-to-unlabelled edge and perform its typed forest update. -/
theorem applyMatchingGrowEventBlock_valid {n : ℕ} {forest : AlternatingForestState (Fin n)}
    {mate : Fin n → Option (Fin n)} {tight : Fin n → Fin n → Prop} (valid : forest.valid mate tight)
    (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (table : AlternatingForestMemory forest (s.nr 51) s.nm)
    (parentBase : s.nr 52 = s.nr 51 + n) (depthBase : s.nr 53 = s.nr 51 + n + n)
    {source target peer : Fin n} {parent : Option (Fin n)}
    (sourceIndex : matchingChosenGrowSource s = source.val)
    (targetIndex : matchingChosenGrowTarget s = target.val) (peerIndex : s.nm (s.nr 50 + target.val) = peer.val)
    (sourceOuter : forest.role source = .outer parent) (targetDormant : forest.role target = .unlabelled)
    (peerDormant : forest.role peer = .unlabelled) (distinct : target ≠ peer)
    (mateTarget : mate target = some peer) (matePeer : mate peer = some target)
    (incoming : tight source target) (matched : tight target peer) :
    ∃ result steps, steps ≤ 40 ∧ BlockRuns applyMatchingGrowEventBlock steps s result ∧
      result.halted = false ∧
      AlternatingForestMemory (forest.grow source target peer) (s.nr 51) result.nm ∧
      (forest.grow source target peer).valid mate tight ∧
      result.nr 1 = target.val ∧ result.nr 2 = peer.val ∧ result.nr 9 = 1 ∧ result.rm = s.rm ∧
      (∀ a, a < s.nr 51 ∨ s.nr 53 + n ≤ a → result.nm a = s.nm a) ∧
      ∀ r ≥ 15, result.nr r = s.nr r := by
  obtain ⟨t, ticks, short, decoded, live, nat, real, sourceArg, targetArg, peerArg, role, parentAt, depth⟩ :=
    prepareMatchingGrowBlock_spec s entry running one
  let ready := {t with pc := 0}
  have memory : AlternatingForestMemory forest (s.nr 51) ready.nm := nat.symm ▸ table
  have preparedMate : ready.nr 2 = peer.val := by
    show t.nr 2 = peer.val
    rw [peerArg, targetIndex, peerIndex]
  obtain ⟨grown, afterMemory, afterValid⟩ := alternatingForestGrowBlock_valid (s := ready) rfl live memory valid
    (sourceArg.trans sourceIndex) (targetArg.trans targetIndex) preparedMate role (parentAt.trans parentBase)
    (depth.trans depthBase) sourceOuter targetDormant peerDormant distinct mateTarget matePeer incoming matched
  have alive := no_halt_from_running (s := ready) live grown.inside (by simp [alternatingForestGrowBlock])
  obtain ⟨_, growNat, growReal, _, keep⟩ := alternatingForestGrowBlock_spec ready rfl live
  have run := decoded.append grown
  refine ⟨_, ticks + 18, by omega, run, alive, afterMemory, afterValid,
    (keep 1 (by decide)).trans (targetArg.trans targetIndex), (keep 2 (by decide)).trans preparedMate,
    ?_, growReal.trans real, ?_, ?_⟩
  · rw [← run.run, arithmeticRun_keeps_register _ _ _, one]
    simp [applyMatchingGrowEventBlock, prepareMatchingGrowBlock, appendBlock, readMatchingGrowEdge,
      orientGrowEndpoints, branchOnAtMost, copyGrowEndpoints, readGrowMateAndBases, alternatingForestGrowBlock,
      relocateInstruction, naturalDestination]
  · intro a outside
    change ((arithmeticStep alternatingForestGrowBlock)^[18] ready).nm a = s.nm a
    have src : ready.nr 0 = source.val := sourceArg.trans sourceIndex
    have dst : ready.nr 1 = target.val := targetArg.trans targetIndex
    have mateAt : ready.nr 2 = peer.val := preparedMate
    have roleReg : ready.nr 3 = s.nr 51 := role
    have parentReg : ready.nr 4 = s.nr 52 := parentAt
    have depthReg : ready.nr 5 = s.nr 53 := depth
    have same : ready.nm = s.nm := nat
    rw [growNat]
    have ltSrc := source.isLt
    have ltDst := target.isLt
    have ltPeer := peer.isLt
    simp (disch := omega) [alternatingForestGrownMemory, src, dst, mateAt, roleReg, parentReg, depthReg,
      same, Function.update_of_ne]
  · intro r high
    have writes : ∀ ins ∈ applyMatchingGrowEventBlock, naturalDestination ins < r := by
      simp [applyMatchingGrowEventBlock, prepareMatchingGrowBlock, appendBlock, readMatchingGrowEdge,
        orientGrowEndpoints, branchOnAtMost, copyGrowEndpoints, readGrowMateAndBases, alternatingForestGrowBlock,
        relocateInstruction, naturalDestination] <;> omega
    have preserved := arithmeticRun_keeps_high_register writes s (ticks + 18)
    exact run.run ▸ preserved

end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowEventRAM

/-! matching/MatchingGrowRerateRAM.lean -/
section RppSource_MatchingGrowRerateRAM
namespace VehicleRoutingSurvey.Routing

private def growthRowRepresentative (s : ArithmeticState) : ℕ :=
  s.nm (s.nr 57 + s.nr 7)



private def reratedGrowthNat (s : ArithmeticState) : ℕ → ℕ :=
  if growthRowRepresentative s = s.nr 26 then
    Function.update s.nm (s.nr 58 + (s.nr 55 + s.nr 7)) 0
  else s.nm

private def reratedGrowthReal (s : ArithmeticState) : ℕ → ℝ :=
  if growthRowRepresentative s ≠ s.nr 26 ∧ growthRowRepresentative s = s.nr 28 then
    Function.update s.rm (s.nr 60 + (s.nr 55 + s.nr 7)) 0
  else s.rm

private structure ReratedGrowthCell (s t : ArithmeticState) (steps : ℕ) : Prop where
  run : BlockRuns rerateGrowthIncomingCell steps s t
  live : t.halted = false
  natMemory : t.nm = reratedGrowthNat s
  realMemory : t.rm = reratedGrowthReal s

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
private theorem rerateGrowthIncomingCell_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 14 = 0) :
    ∃ t steps, steps ≤ 11 ∧ ReratedGrowthCell s t steps := by
  rcases lt_trichotomy (s.nm (s.nr 57 + s.nr 7)) (s.nr 26) with before | equal | after
  · have reversed := not_le.mpr before
    by_cases inner : s.nm (s.nr 57 + s.nr 7) = s.nr 28
    · have beforeInner : s.nr 28 ≤ s.nr 26 := by simpa only [inner] using before.le
      have reverseInner : ¬s.nr 26 ≤ s.nr 28 := by simpa only [inner] using reversed
      have different : s.nr 28 ≠ s.nr 26 := by simpa only [inner] using before.ne
      let t := (arithmeticStep rerateGrowthIncomingCell)^[11] s
      have computes : t.pc = rerateGrowthIncomingCell.length ∧ t.halted = false ∧
          t.nm = reratedGrowthNat s ∧ t.rm = reratedGrowthReal s := by
        simp [t, rerateGrowthIncomingCell, arithmeticStep, Function.iterate_succ_apply', entry, running,
          reratedGrowthNat, reratedGrowthReal, growthRowRepresentative, before.le, before.ne, reversed,
          inner, beforeInner, reverseInner, different]
      exact ⟨t, 11, le_rfl, BlockRuns.of_running_exit rfl computes.2.1 computes.1,
        computes.2.1, computes.2.2.1, computes.2.2.2⟩
    · by_cases lower : s.nm (s.nr 57 + s.nr 7) ≤ s.nr 28
      · have upper : ¬s.nr 28 ≤ s.nm (s.nr 57 + s.nr 7) := by omega
        let t := (arithmeticStep rerateGrowthIncomingCell)^[7] s
        have computes : t.pc = rerateGrowthIncomingCell.length ∧ t.halted = false ∧
            t.nm = reratedGrowthNat s ∧ t.rm = reratedGrowthReal s := by
          simp [t, rerateGrowthIncomingCell, arithmeticStep, Function.iterate_succ_apply', entry, running,
            reratedGrowthNat, reratedGrowthReal, growthRowRepresentative, before.le, before.ne, reversed, inner, lower, upper]
        exact ⟨t, 7, by decide, BlockRuns.of_running_exit rfl computes.2.1 computes.1,
          computes.2.1, computes.2.2.1, computes.2.2.2⟩
      · let t := (arithmeticStep rerateGrowthIncomingCell)^[6] s
        have computes : t.pc = rerateGrowthIncomingCell.length ∧ t.halted = false ∧
            t.nm = reratedGrowthNat s ∧ t.rm = reratedGrowthReal s := by
          simp [t, rerateGrowthIncomingCell, arithmeticStep, Function.iterate_succ_apply', entry, running,
            reratedGrowthNat, reratedGrowthReal, growthRowRepresentative, before.le, before.ne, reversed, inner, lower]
        exact ⟨t, 6, by decide, BlockRuns.of_running_exit rfl computes.2.1 computes.1,
          computes.2.1, computes.2.2.1, computes.2.2.2⟩
  · let t := (arithmeticStep rerateGrowthIncomingCell)^[8] s
    have computes : t.pc = rerateGrowthIncomingCell.length ∧ t.halted = false ∧
        t.nm = reratedGrowthNat s ∧ t.rm = reratedGrowthReal s := by
      simp [t, rerateGrowthIncomingCell, arithmeticStep, Function.iterate_succ_apply', entry, running,
        reratedGrowthNat, reratedGrowthReal, growthRowRepresentative, equal, zero]
    exact ⟨t, 8, by decide, BlockRuns.of_running_exit rfl computes.2.1 computes.1,
      computes.2.1, computes.2.2.1, computes.2.2.2⟩
  · have reversed := not_le.mpr after
    by_cases inner : s.nm (s.nr 57 + s.nr 7) = s.nr 28
    · have reverseInner : ¬s.nr 28 ≤ s.nr 26 := by simpa only [inner] using reversed
      have different : s.nr 28 ≠ s.nr 26 := by simpa only [inner] using after.ne'
      let t := (arithmeticStep rerateGrowthIncomingCell)^[10] s
      have computes : t.pc = rerateGrowthIncomingCell.length ∧ t.halted = false ∧
          t.nm = reratedGrowthNat s ∧ t.rm = reratedGrowthReal s := by
        simp [t, rerateGrowthIncomingCell, arithmeticStep, Function.iterate_succ_apply', entry, running,
          reratedGrowthNat, reratedGrowthReal, growthRowRepresentative, after.ne', reversed, inner, reverseInner, different]
      exact ⟨t, 10, by decide, BlockRuns.of_running_exit rfl computes.2.1 computes.1,
        computes.2.1, computes.2.2.1, computes.2.2.2⟩
    · by_cases lower : s.nm (s.nr 57 + s.nr 7) ≤ s.nr 28
      · have upper : ¬s.nr 28 ≤ s.nm (s.nr 57 + s.nr 7) := by omega
        let t := (arithmeticStep rerateGrowthIncomingCell)^[6] s
        have computes : t.pc = rerateGrowthIncomingCell.length ∧ t.halted = false ∧
            t.nm = reratedGrowthNat s ∧ t.rm = reratedGrowthReal s := by
          simp [t, rerateGrowthIncomingCell, arithmeticStep, Function.iterate_succ_apply', entry, running,
            reratedGrowthNat, reratedGrowthReal, growthRowRepresentative, after.ne', reversed, inner, lower, upper]
        exact ⟨t, 6, by decide, BlockRuns.of_running_exit rfl computes.2.1 computes.1,
          computes.2.1, computes.2.2.1, computes.2.2.2⟩
      · let t := (arithmeticStep rerateGrowthIncomingCell)^[5] s
        have computes : t.pc = rerateGrowthIncomingCell.length ∧ t.halted = false ∧
            t.nm = reratedGrowthNat s ∧ t.rm = reratedGrowthReal s := by
          simp [t, rerateGrowthIncomingCell, arithmeticStep, Function.iterate_succ_apply', entry, running,
            reratedGrowthNat, reratedGrowthReal, growthRowRepresentative, after.ne', reversed, inner, lower]
        exact ⟨t, 5, by decide, BlockRuns.of_running_exit rfl computes.2.1 computes.1,
          computes.2.1, computes.2.2.1, computes.2.2.2⟩



theorem rerateGrowthIncoming_keeps_register {s t : ArithmeticState} {steps r : ℕ}
    (run : BlockRuns rerateGrowthIncomingBlock steps s t) (away : r ∉ [0, 6, 7, 10, 11]) :
    t.nr r = s.nr r := by
  rw [← run.run]
  exact arithmeticRun_keeps_from_destination_list [0, 6, 7, 10, 11] (by decide) away s steps

open Classical in
/-- Update the incoming candidate rows after growth. The candidate identifier table
follows the representative table, so the latter stays available throughout the pass. -/
theorem rerateGrowthIncomingBlock_correct (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (separate : s.nr 57 + s.nr 55 ≤ s.nr 58) :
    ∃ t steps, steps ≤ s.nr 55 * 14 + 2 ∧ BlockRuns rerateGrowthIncomingBlock steps s t ∧
      t.halted = false ∧
      (∀ a, t.nm a = if ∃ j < s.nr 55, a = s.nr 58 + (s.nr 55 + j) ∧ s.nm (s.nr 57 + j) = s.nr 26
        then 0 else s.nm a) ∧
      (∀ a, t.rm a = if ∃ j < s.nr 55, a = s.nr 60 + (s.nr 55 + j) ∧
        s.nm (s.nr 57 + j) ≠ s.nr 26 ∧ s.nm (s.nr 57 + j) = s.nr 28 then 0 else s.rm a) := by
  classical
  let natChanged (i a : ℕ) := ∃ j < i, a = s.nr 58 + (s.nr 55 + j) ∧ s.nm (s.nr 57 + j) = s.nr 26
  let realChanged (i a : ℕ) := ∃ j < i, a = s.nr 60 + (s.nr 55 + j) ∧
    s.nm (s.nr 57 + j) ≠ s.nr 26 ∧ s.nm (s.nr 57 + j) = s.nr 28
  let inv (i : ℕ) (m : ArithmeticState) := m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧
    (∀ r, r ≠ 0 → r ≠ 6 → r ≠ 7 → r ≠ 10 → r ≠ 11 → m.nr r = s.nr r) ∧
    (∀ a, m.nm a = if natChanged i a then 0 else s.nm a) ∧
    ∀ a, m.rm a = if realChanged i a then 0 else s.rm a
  have init : inv 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, ?_, ?_⟩
    · intro r _ _ away _ _
      simp [Function.update_of_ne away]
    · intro a
      simp [natChanged]
    · intro a
      simp [realChanged]
  have control (i : ℕ) (m : ArithmeticState) (valid : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 55 = s.nr 55 :=
    ⟨valid.1, valid.2.1, valid.2.2.1,
      valid.2.2.2.1 55 (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  have iteration (i : ℕ) (more : i < s.nr 55) (m : ArithmeticState) (valid : inv i m) :
      ∃ t steps, steps ≤ 11 ∧ BlockRuns rerateGrowthIncomingCell steps m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    obtain ⟨atStart, ready, index, fixed, oldNat, oldReal⟩ := valid
    have kept {r : ℕ} (other : r ∉ [0, 6, 7, 10, 11]) : m.nr r = s.nr r := by
      simp at other
      exact fixed r (by omega) (by omega) (by omega) (by omega) (by omega)
    obtain ⟨t, ticks, short, changed⟩ := rerateGrowthIncomingCell_spec m atStart ready ((kept (by decide)).trans zero)
    have frame {r : ℕ} (other : r ∉ [0, 6, 10, 11]) : t.nr r = m.nr r := by
      rw [← changed.run.run]
      apply arithmeticRun_keeps_register _ m ticks
      simp [rerateGrowthIncomingCell, naturalDestination] at other ⊢
      omega
    have read : growthRowRepresentative m = s.nm (s.nr 57 + i) := by
      have untouched : ¬natChanged i (s.nr 57 + i) := by
        rintro ⟨j, hj, address, _⟩
        omega
      rw [growthRowRepresentative, kept (r := 57) (by decide), index, oldNat, if_neg untouched]
    have natStep a : natChanged (i + 1) a ↔
        natChanged i a ∨ (a = s.nr 58 + (s.nr 55 + i) ∧ s.nm (s.nr 57 + i) = s.nr 26) := by
      constructor
      · rintro ⟨j, hj, h⟩
        obtain prior | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)
        · exact Or.inl ⟨j, prior, h⟩
        · exact Or.inr h
      · rintro (⟨j, hj, h⟩ | h)
        · exact ⟨j, by omega, h⟩
        · exact ⟨i, by omega, h⟩
    have realStep a : realChanged (i + 1) a ↔ realChanged i a ∨
        (a = s.nr 60 + (s.nr 55 + i) ∧ s.nm (s.nr 57 + i) ≠ s.nr 26 ∧ s.nm (s.nr 57 + i) = s.nr 28) := by
      constructor
      · rintro ⟨j, hj, h⟩
        obtain prior | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)
        · exact Or.inl ⟨j, prior, h⟩
        · exact Or.inr h
      · rintro (⟨j, hj, h⟩ | h)
        · exact ⟨j, by omega, h⟩
        · exact ⟨i, by omega, h⟩
    refine ⟨t, ticks, short, changed.run, changed.live, rfl, changed.live, ?_, ?_, ?_, ?_⟩
    · change Function.update t.nr 7 (t.nr 7 + t.nr 9) 7 = i + 1
      rw [show (Function.update t.nr 7 (t.nr 7 + t.nr 9)) 7 = t.nr 7 + t.nr 9 by simp,
        frame (r := 7) (by decide), frame (r := 9) (by decide), index, kept (r := 9) (by decide), one]
    · intro r other0 other6 other7 other10 other11
      change Function.update t.nr 7 (t.nr 7 + t.nr 9) r = s.nr r
      rw [show (Function.update t.nr 7 (t.nr 7 + t.nr 9)) r = t.nr r from Function.update_of_ne other7 _ _]
      exact (frame (by simp [other0, other6, other10, other11])).trans
        (fixed r other0 other6 other7 other10 other11)
    · intro a
      change t.nm a = _
      rw [changed.natMemory, reratedGrowthNat, read, kept (r := 26) (by decide), kept (r := 58) (by decide),
        kept (r := 55) (by decide), index]
      by_cases outer : s.nm (s.nr 57 + i) = s.nr 26 <;>
        by_cases target : a = s.nr 58 + (s.nr 55 + i) <;>
        simp [natStep, outer, target, oldNat, Function.update_apply]
    · intro a
      change t.rm a = _
      rw [changed.realMemory, reratedGrowthReal, read, kept (r := 26) (by decide), kept (r := 28) (by decide),
        kept (r := 60) (by decide), kept (r := 55) (by decide), index]
      by_cases outer : s.nm (s.nr 57 + i) = s.nr 26
      · simp [realStep, outer, oldReal]
      · by_cases inner : s.nm (s.nr 57 + i) = s.nr 28
        · have distinct : s.nr 28 ≠ s.nr 26 := fun equal => outer (inner.trans equal)
          by_cases target : a = s.nr 60 + (s.nr 55 + i) <;>
            simp [realStep, outer, inner, target, distinct, oldReal, Function.update_apply]
        · simp [realStep, outer, inner, oldReal]
  obtain ⟨t, steps, finished, short, ran⟩ := countedLoopFromZero_bounded 9 7 55 (s.nr 55) 11
    rerateGrowthIncomingCell inv entry running init control iteration
  exact ⟨_, steps, by omega, ran, finished.2.1, finished.2.2.2.2.1, finished.2.2.2.2.2⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowRerateRAM

/-! matching/MatchingGrowHandler.lean -/
section RppSource_MatchingGrowHandler
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

noncomputable def advancedEffectiveMemory (s : ArithmeticState) : ℕ → ℝ :=
  fun a => if s.nr 62 ≤ a ∧ a < s.nr 62 + s.nr 55 then
    effectivePotentialAfterDelta s (a - s.nr 62) else s.rm a

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

theorem saveMatchingGrowthBlocks_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    let t := {s with
      pc := 3
      nr := Function.update (Function.update (Function.update s.nr 14 0) 26 (s.nr 2)) 28 (s.nr 1) }
    BlockRuns saveMatchingGrowthBlocks 3 s t := by
  dsimp only
  apply BlockRuns.of_running_exit
  · simp [saveMatchingGrowthBlocks, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · exact running
  · rfl

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

def matchingNewOuterCard (s : ArithmeticState) (peer : ℕ) : ℕ :=
  ((List.range (s.nr 55)).filter fun v => decide (s.nm (s.nr 57 + v) = peer)).length





/-- Execute the complete fixed growth instruction block. The budget accounts for the
original vertices entering the outer forest. The candidate writes preserve the new
forest encoding and all prior memory cells preceding the forest or lying in the representative table. -/
theorem matchingGrowHandlerBlock_runs {n : ℕ} {forest : AlternatingForestState (Fin n)}
    {mate : Fin n → Option (Fin n)} {tight : Fin n → Fin n → Prop} (valid : forest.valid mate tight)
    (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (size : s.nr 55 = n) (table : AlternatingForestMemory forest (s.nr 51) s.nm)
    (parentBase : s.nr 52 = s.nr 51 + n) (depthBase : s.nr 53 = s.nr 51 + n + n)
    (repAfter : s.nr 53 + n ≤ s.nr 57) (repBefore : s.nr 57 + n ≤ s.nr 58)
    (dictionary : s.nr 58 ≤ s.nr 54) (buckets : s.nr 58 ≤ s.nr 65)
    {source target peer : Fin n} {parent : Option (Fin n)}
    (sourceIndex : matchingChosenGrowSource s = source.val)
    (targetIndex : matchingChosenGrowTarget s = target.val) (peerIndex : s.nm (s.nr 50 + target.val) = peer.val)
    (sourceOuter : forest.role source = .outer parent) (targetDormant : forest.role target = .unlabelled)
    (peerDormant : forest.role peer = .unlabelled) (distinct : target ≠ peer)
    (mateTarget : mate target = some peer) (matePeer : mate peer = some target)
    (incoming : tight source target) (matched : tight target peer) :
    ∃ result ticks, ticks ≤ 56 * n + (n * 98 + 2) * matchingNewOuterCard s peer.val + 81 ∧
      BlockRuns matchingGrowHandlerBlock ticks s result ∧ result.halted = false ∧ result.nr 1 = 0 ∧
      AlternatingForestMemory (forest.grow source target peer) (s.nr 51) result.nm ∧
      (forest.grow source target peer).valid mate tight ∧
      (∀ a, a < s.nr 58 → (a < s.nr 51 ∨ s.nr 53 + n ≤ a) → result.nm a = s.nm a) ∧
      (∀ r, 29 ≤ r ∨ r = 22 ∨ r = 23 → result.nr r = s.nr r) ∧
      result.nr 26 = peer.val ∧ result.nr 28 = target.val ∧ result.nr 9 = 1 ∧
      result.nr 3 = s.nr 58 ∧ result.nr 4 = s.nr 59 ∧ result.nr 5 = s.nr 60 ∧ result.nr 8 = s.nr 61 := by
  obtain ⟨dual, dualTicks, dualBudget, dualRun, dualLive, dualNat, _, _, _, dualKeep, _⟩ :=
    advanceMatchingEventDuals_spec s entry running one
  let d := {dual with pc := 0}
  have dOne : d.nr 9 = 1 := (dualKeep 9 (by decide)).trans one
  have dRole : d.nr 51 = s.nr 51 := dualKeep 51 (by decide)
  have dParent : d.nr 52 = s.nr 52 := dualKeep 52 (by decide)
  have dDepth : d.nr 53 = s.nr 53 := dualKeep 53 (by decide)
  have dNat : d.nm = s.nm := dualNat
  have decodeSame : matchingChosenLeftBlock d = matchingChosenLeftBlock s ∧
      matchingChosenRightBlock d = matchingChosenRightBlock s := by
    have event : d.nr 1 = s.nr 1 := dualKeep 1 (by decide)
    have dict : d.nr 54 = s.nr 54 := dualKeep 54 (by decide)
    have rep : d.nr 57 = s.nr 57 := dualKeep 57 (by decide)
    simp [matchingChosenLeftBlock, matchingChosenRightBlock, matchingChosenEdgeAddress, event, dict, rep, dNat]
  have dSource : matchingChosenGrowSource d = source.val := by
    simpa [matchingChosenGrowSource, dNat, dRole, decodeSame.1, decodeSame.2] using sourceIndex
  have dTarget : matchingChosenGrowTarget d = target.val := by
    simpa [matchingChosenGrowTarget, dNat, dRole, decodeSame.1, decodeSame.2] using targetIndex
  have dMate : d.nm (d.nr 50 + target.val) = peer.val := by
    simpa [dNat, show d.nr 50 = s.nr 50 from dualKeep 50 (by decide)] using peerIndex
  have dTable : AlternatingForestMemory forest (d.nr 51) d.nm := by simpa [dNat, dRole] using table
  obtain ⟨grown, growTicks, growBudget, growRun, growLive, afterForest, afterValid, grownTarget, grownPeer,
    grownOne, _, grownFrame, grownKeep⟩ :=
    applyMatchingGrowEventBlock_valid valid d rfl dualLive dOne dTable (dParent.trans (parentBase.trans
      (congrArg (fun a => a + n) dRole.symm))) (dDepth.trans (depthBase.trans
      (congrArg (fun a => a + n + n) dRole.symm))) dSource dTarget dMate
      sourceOuter targetDormant peerDormant distinct mateTarget matePeer incoming matched
  let g := {grown with pc := 0}
  let saved := {g with
    pc := 3
    nr := Function.update (Function.update (Function.update g.nr 14 0) 26 (g.nr 2)) 28 (g.nr 1) }
  have saveRun : BlockRuns saveMatchingGrowthBlocks 3 g saved := saveMatchingGrowthBlocks_spec g rfl growLive
  let a := {saved with pc := 0}
  have aOne : a.nr 9 = 1 := by simpa [a, saved, g] using grownOne
  have aZero : a.nr 14 = 0 := by simp [a, saved]
  have aPeer : a.nr 26 = peer.val := by simpa [a, saved, g] using grownPeer
  have aTarget : a.nr 28 = target.val := by simpa [a, saved, g] using grownTarget
  have aBase (r : ℕ) (large : 15 ≤ r) (away : r ∉ [0, 6, 7, 10, 11, 12, 14, 26, 28]) :
      a.nr r = s.nr r := by
    have dSame : d.nr r = s.nr r := dualKeep r (by simp at away ⊢; omega)
    have growSame : g.nr r = s.nr r := (grownKeep r large).trans dSame
    have b14 : r ≠ 14 := by simp at away; omega
    have b26 : r ≠ 26 := by simp at away; omega
    have b28 : r ≠ 28 := by simp at away; omega
    simpa [a, saved, Function.update_of_ne b14, Function.update_of_ne b26, Function.update_of_ne b28] using growSame
  have aSize : a.nr 55 = n := (aBase 55 (by decide) (by decide)).trans size
  have aRep : a.nr 57 = s.nr 57 := aBase 57 (by decide) (by decide)
  have aFloor : a.nr 58 = s.nr 58 := aBase 58 (by decide) (by decide)
  have aDict : a.nr 58 ≤ a.nr 54 := by simpa [aFloor, aBase 54 (by decide) (by decide)] using dictionary
  have aBucket : a.nr 58 ≤ a.nr 65 := by simpa [aFloor, aBase 65 (by decide) (by decide)] using buckets
  have aSeparation : a.nr 57 + a.nr 55 ≤ a.nr 58 := by simpa [aRep, aSize, aFloor] using repBefore
  obtain ⟨rerated, ratesTicks, ratesBudget, ratesRun, ratesLive, rerateNat, _⟩ :=
    rerateGrowthIncomingBlock_correct a rfl growLive aOne aZero aSeparation
  let b := {rerated with pc := 0}
  have bBase (r : ℕ) (out : r ∉ [0, 6, 7, 10, 11]) : b.nr r = a.nr r :=
    rerateGrowthIncoming_keeps_register (t := rerated) ratesRun out
  have bZero : b.nr 14 = 0 := (bBase 14 (by decide)).trans aZero
  have bOne : b.nr 9 = 1 := (bBase 9 (by decide)).trans aOne
  have bDict : b.nr 58 ≤ b.nr 54 := by simpa [bBase 58 (by decide), bBase 54 (by decide)] using aDict
  obtain ⟨cut, cutTicks, cutBudget, cutRun, cutLive, cutNat, _⟩ := activateMatchingInnerCut_spec b rfl ratesLive bOne bZero
  let c := {cut with pc := 0}
  have cBase (r : ℕ) (out : r ∉ [0, 6, 10, 15, 16, 18]) : c.nr r = b.nr r :=
    activateMatchingInnerCut_keeps_register (t := cut) cutRun out
  have cKeep (r : ℕ) (out : r ∉ [0, 6, 7, 10, 11, 15, 16, 18]) : c.nr r = a.nr r :=
    (cBase r (by simp at out ⊢; omega)).trans (bBase r (by simp at out ⊢; omega))
  have cZero : c.nr 14 = 0 := (cKeep 14 (by decide)).trans aZero
  have cOne : c.nr 9 = 1 := (cKeep 9 (by decide)).trans aOne
  have cSize : c.nr 55 = n := (cKeep 55 (by decide)).trans aSize
  have cFloor : c.nr 58 = s.nr 58 := (cKeep 58 (by decide)).trans aFloor
  have cRep : c.nr 57 = s.nr 57 := (cKeep 57 (by decide)).trans aRep
  have cPeer : c.nr 26 = peer.val := (cKeep 26 (by decide)).trans aPeer
  have cDict : c.nr 58 ≤ c.nr 54 := by simpa [cKeep 58 (by decide), cKeep 54 (by decide)] using aDict
  have cBucket : c.nr 58 ≤ c.nr 65 := by simpa [cKeep 58 (by decide), cKeep 65 (by decide)] using aBucket
  have cSeparation : c.nr 57 + c.nr 55 ≤ c.nr 58 := by simpa [cRep, cSize, cFloor] using repBefore
  have earlier (addr : ℕ) (below : addr < s.nr 58) : c.nm addr = grown.nm addr := by
    have untouched : ¬∃ j < a.nr 55, addr = a.nr 58 + (a.nr 55 + j) ∧ a.nm (a.nr 57 + j) = a.nr 26 := by
      rintro ⟨j, _, address, _⟩
      omega
    have bMemory : b.nm addr = grown.nm addr := by
      change rerated.nm addr = grown.nm addr
      exact (rerateNat addr).trans (if_neg untouched)
    change cut.nm addr = grown.nm addr
    rw [cutNat]
    exact (installedMatchingInnerCutNat_preserves_prefix b bDict addr
      (by rw [bBase 58 (by decide), aFloor]; exact below)).trans bMemory
  have memberCount : matchingGrowthMembers c (c.nr 55) = matchingNewOuterCard s peer.val := by
    rw [matchingGrowthMembers, matchingNewOuterCard, cSize, size, cRep, cPeer]
    apply congrArg List.length
    apply List.filter_congr
    intro j hj
    have small : j < n := List.mem_range.mp hj
    have repAddress : s.nr 57 + j < s.nr 58 := by omega
    have unchanged : c.nm (s.nr 57 + j) = s.nm (s.nr 57 + j) :=
      (earlier _ repAddress).trans ((grownFrame _ (Or.inr (by omega))).trans (congrFun dNat _))
    rw [unchanged]
  obtain ⟨scanned, scanTicks, scanRun, scanLive, count, scanBudget, scanNat, scanKeep⟩ :=
    refreshMatchingNewOuterBlock_bound c rfl cutLive cOne cZero cDict cBucket cSeparation
  let e := {scanned with pc := 0}
  have eZero : e.nr 14 = 0 := (scanKeep 14 (by decide)).trans cZero
  obtain ⟨result, resetRun, finalLive, finalNat, _, resetId, idBase, slackBase, rateBase, rowCount⟩ :=
    resetMatchingSelector_spec e rfl scanLive eZero
  have finalKept (r : ℕ) (safe : r ∉ [0, 1, 3, 4, 5, 8]) : result.nr r = e.nr r := by
    rw [← resetRun.run]
    exact arithmeticRun_keeps_from_destination_list [0, 1, 3, 4, 5, 8] (by decide) safe e 5
  have highBase (r : ℕ) (large : 50 ≤ r) : e.nr r = s.nr r := by
    exact (refreshMatchingNewOuterBlock_keeps (t := scanned) scanRun (by simp; omega)).trans
      ((cKeep r (by simp; omega)).trans (aBase r (by omega) (by simp; omega)))
  have joined := dualRun.append (growRun.append (saveRun.append (ratesRun.append (cutRun.append (scanRun.append resetRun)))))
  have newForest (addr : ℕ) (below : addr < s.nr 58) : result.nm addr = grown.nm addr :=
    (congrFun finalNat addr).trans ((scanNat addr (cFloor.symm ▸ below)).trans (earlier addr below))
  refine ⟨_, dualTicks + (growTicks + (3 + (ratesTicks + (cutTicks + (scanTicks + 5))))), ?_,
    joined, finalLive, resetId, ?_, afterValid, ?_, ?_, ?_, ?_, ?_,
    idBase.trans (highBase 58 (by decide)), slackBase.trans (highBase 59 (by decide)),
    rateBase.trans (highBase 60 (by decide)), rowCount.trans (highBase 61 (by decide))⟩
  · rw [size] at dualBudget
    rw [aSize] at ratesBudget
    rw [cSize, count, memberCount] at scanBudget
    omega
  · rw [dRole] at afterForest
    intro v
    have bounded := v.isLt
    obtain ⟨role, parentCode, level⟩ := afterForest v
    exact ⟨(newForest _ (by omega)).trans role, (newForest _ (by omega)).trans parentCode,
      (newForest _ (by omega)).trans level⟩
  · intro addr below outside
    exact (newForest addr below).trans ((grownFrame addr (by simpa [dRole, dDepth] using outside)).trans (congrFun dNat addr))
  · intro r safe
    have scanFrame : e.nr r = c.nr r :=
      refreshMatchingNewOuterBlock_keeps (t := scanned) scanRun (by simp; omega)
    exact (finalKept r (by simp; omega)).trans
      (scanFrame.trans ((cKeep r (by simp; omega)).trans (aBase r (by omega) (by simp; omega))))
  · exact (finalKept 26 (by decide)).trans ((scanKeep 26 (by decide)).trans ((cKeep 26 (by decide)).trans aPeer))
  · exact (finalKept 28 (by decide)).trans ((refreshMatchingNewOuterBlock_keeps (t := scanned) scanRun (by decide)).trans
      ((cKeep 28 (by decide)).trans aTarget))
  · exact (finalKept 9 (by decide)).trans ((refreshMatchingNewOuterBlock_keeps (t := scanned) scanRun (by decide)).trans cOne)

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

/-! matching/MatchingCacheInsertion.lean -/
section RppSource_MatchingCacheInsertion
namespace VehicleRoutingSurvey.Routing

/-- Retain the earlier witness on ties, as in the cache instructions. -/
noncomputable def insertSlackCandidate {Event : Type*}
    (candidate : DualSlack Event) : Option (DualSlack Event) → Option (DualSlack Event)
  | none => some candidate
  | some old => if candidate.slack < old.slack then some candidate else some old

theorem LeastSlackEntry.insert {Event : Type*} {full : List (DualSlack Event)}
    {cached : Option (DualSlack Event)} (before : LeastSlackEntry full cached) (edge : DualSlack Event) :
    LeastSlackEntry (edge :: full) (insertSlackCandidate edge cached) := by
  cases cached with
  | none =>
    have empty : ∀ x, x ∉ full := by
      intro x member
      obtain ⟨rep, represented, _⟩ := before.covers x member
      simp at represented
    constructor
    · intro rep encoded
      simp [insertSlackCandidate] at encoded
      exact List.mem_cons.mpr (Or.inl encoded.symm)
    · intro x member
      obtain rfl | available := List.mem_cons.mp member
      · exact ⟨x, rfl, le_rfl⟩
      · exact (empty x available).elim
  | some oldEdge =>
    by_cases better : edge.slack < oldEdge.slack
    · simp only [insertSlackCandidate, if_pos better]
      constructor
      · intro rep encoded
        have same := Option.some.inj encoded
        exact List.mem_cons.mpr (Or.inl same.symm)
      · intro x member
        obtain rfl | available := List.mem_cons.mp member
        · exact ⟨x, rfl, le_rfl⟩
        · obtain ⟨rep, represented, lower⟩ := before.covers x available
          have repEq : oldEdge = rep := Option.some.inj represented
          exact ⟨edge, rfl, better.le.trans (repEq.symm ▸ lower)⟩
    · simp only [insertSlackCandidate, if_neg better]
      constructor
      · intro rep encoded
        exact List.mem_cons.mpr (Or.inr (before.sound encoded))
      · intro x member
        obtain rfl | available := List.mem_cons.mp member
        · exact ⟨oldEdge, rfl, le_of_not_gt better⟩
        · obtain ⟨rep, represented, lower⟩ := before.covers x available
          exact ⟨rep, represented, lower⟩

noncomputable def insertSlackCandidates {Event : Type*}
    (new : List (DualSlack Event)) (cached : Option (DualSlack Event)) : Option (DualSlack Event) :=
  new.foldl (fun prior edge => insertSlackCandidate edge prior) cached

/-- Refreshing a group by scanning its newly admitted edges preserves the least-slack
invariant. The scan visits each new edge once. -/
theorem LeastSlackEntry.insert_many {Event : Type*}
    {full : List (DualSlack Event)} {cached : Option (DualSlack Event)}
    (before : LeastSlackEntry full cached) (new : List (DualSlack Event)) :
    LeastSlackEntry (new.reverse ++ full) (insertSlackCandidates new cached) := by
  induction new generalizing full cached with
  | nil => simpa [insertSlackCandidates] using before
  | cons edge tail ih =>
    simpa [insertSlackCandidates, List.reverse_cons, List.append_assoc]
      using ih (before.insert edge)





end VehicleRoutingSurvey.Routing
end RppSource_MatchingCacheInsertion

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

/-! matching/MatchingCandidateMemory.lean -/
section RppSource_MatchingCandidateMemory
namespace VehicleRoutingSurvey.Routing





private theorem readMatchingCandidate_empty {k i : ℕ} {cutAt : Fin k → Finset (Fin k)}
    {s : ArithmeticState} (empty : s.nm (s.nr 58 + i) = 0) :
    readMatchingCandidate cutAt s i = none := by
  simp [readMatchingCandidate, empty, decodeMatchingDictionaryEvent]



/-- An update preserves every other decoded row and implements insertion by raw slack
in its chosen row. Endpoints with second coordinate `k` may denote a cut. -/
theorem improveMatchingCandidateBlock_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (inside : s.nr 18 < s.nr 61) (dictAfter : s.nr 58 + s.nr 61 ≤ s.nr 54)
    (rateAfter : s.nr 59 + s.nr 61 ≤ s.nr 60)
    {event : MatchingDualEvent k} (record : MatchingEventRecord cutAt (s.nr 15, s.nr 16) event)
    (valid : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i) :
    let edge : DualSlack (MatchingDualEvent k) := ⟨event, s.rr 0, s.rr 4⟩
    ∃ t steps, steps ≤ 19 ∧ BlockRuns improveMatchingCandidateBlock steps s t ∧ t.halted = false ∧
      (∀ r ≥ 15, t.nr r = s.nr r) ∧
      ∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧
        readMatchingCandidate cutAt t i = if i = s.nr 18 then
          insertSlackCandidate edge (readMatchingCandidate cutAt s i) else readMatchingCandidate cutAt s i := by
  classical
  intro edge
  obtain ⟨t, steps, bound, ran, live, write, ignore, keeps⟩ :=
    improveMatchingCandidateBlock_spec s entry running one
  refine ⟨t, steps, bound, ran, live, keeps, ?_⟩
  have r54 := keeps 54 (by decide)
  have r58 := keeps 58 (by decide)
  have r59 := keeps 59 (by decide)
  have r60 := keeps 60 (by decide)
  let target := s.nr 18
  let dict (i : ℕ) := s.nr 54 + (i + i)
  have chosen : (if matchingCandidateImproves s then some edge else readMatchingCandidate cutAt s target) =
      insertSlackCandidate edge (readMatchingCandidate cutAt s target) := by
    rcases valid target inside with empty | ⟨own, found, decoded⟩
    · have absence := readMatchingCandidate_empty (cutAt := cutAt) empty
      simp [matchingCandidateImproves, target, empty, absence, insertSlackCandidate]
    · have idNonzero : s.nm (s.nr 58 + target) ≠ 0 := by rw [own]; omega
      have present : readMatchingCandidate cutAt s target =
          some ⟨found, s.rm (s.nr 59 + target), s.rm (s.nr 60 + target)⟩ := by
        simp [readMatchingCandidate, decoded]
      simpa only [target, matchingCandidateImproves, idNonzero, false_or, present,
        insertSlackCandidate, edge]
  intro i hi
  by_cases improves : matchingCandidateImproves s
  · obtain ⟨natEffect, realEffect⟩ := write improves
    have writeId (r : ℕ) (hr : r < s.nr 61) :
        t.nm (t.nr 58 + r) = if r = target then target + 1 else s.nm (s.nr 58 + r) := by
      have first : s.nr 58 + r ≠ dict target := by dsimp [dict]; omega
      have second : s.nr 58 + r ≠ dict target + 1 := by dsimp [dict]; omega
      by_cases same : r = target
      · subst r
        simp [r58, natEffect, installedMatchingCandidateNat, target, dict,
          Function.update_of_ne first, Function.update_of_ne second]
      · have different : s.nr 58 + r ≠ s.nr 58 + target := by omega
        simp [r58, natEffect, installedMatchingCandidateNat, target, dict,
          Function.update_of_ne first, Function.update_of_ne second, Function.update_of_ne different, same]
    have ownFirst : t.nm (dict target) = s.nr 15 := by
      have different : dict target ≠ dict target + 1 := by omega
      simp [natEffect, installedMatchingCandidateNat, dict, target, Function.update_of_ne different]
    have ownSecond : t.nm (dict target + 1) = s.nr 16 := by
      simp [natEffect, installedMatchingCandidateNat, dict, target]
    by_cases same : i = target
    · subst i
      have id : t.nm (t.nr 58 + target) = target + 1 := by simp [writeId target hi]
      have decoded : decodeMatchingDictionaryEvent k cutAt t (target + 1) = some event := by
        have first : t.nm (t.nr 54 + (target + target)) = s.nr 15 := by simpa only [r54, dict] using ownFirst
        have second : t.nm (t.nr 54 + (target + target) + 1) = s.nr 16 := by
          simpa only [r54, dict] using ownSecond
        cases event with
        | edge e =>
          obtain ⟨u, v, ports, rfl⟩ := record
          have a : s.nr 15 = u.val := congrArg Prod.fst ports
          have b : s.nr 16 = v.val := congrArg Prod.snd ports
          simp [decodeMatchingDictionaryEvent, first, second, a, b, u.isLt, v.isLt]
        | cut B =>
          obtain ⟨u, ports, rfl⟩ := record
          have a : s.nr 15 = u.val := congrArg Prod.fst ports
          have b : s.nr 16 = k := congrArg Prod.snd ports
          simp [decodeMatchingDictionaryEvent, first, second, a, b, u.isLt]
      have slack : t.rm (t.nr 59 + target) = s.rr 0 := by
        have outside : s.nr 59 + target ≠ s.nr 60 + target := by omega
        simp [realEffect, r59, installedMatchingCandidateReal, target, Function.update_of_ne outside]
      have rate : t.rm (t.nr 60 + target) = s.rr 4 := by
        simp [realEffect, r60, installedMatchingCandidateReal, target]
      refine ⟨Or.inr ⟨id, event, by rw [id]; exact decoded⟩, ?_⟩
      have value : readMatchingCandidate cutAt t target = some edge := by
        simp [readMatchingCandidate, id, decoded, slack, rate, edge]
      rw [if_pos (show target = s.nr 18 from rfl), value]
      simpa only [if_pos improves] using chosen
    · have id : t.nm (t.nr 58 + i) = s.nm (s.nr 58 + i) := by simp [writeId i hi, same]
      have readWord (offset : ℕ) (small : offset ≤ 1) : t.nm (dict i + offset) = s.nm (dict i + offset) := by
        have outsideFirst : dict i + offset ≠ dict target := by dsimp [dict]; omega
        have outsideSecond : dict i + offset ≠ dict target + 1 := by dsimp [dict]; omega
        have outsideId : dict i + offset ≠ s.nr 58 + target := by dsimp [dict]; omega
        simp [natEffect, installedMatchingCandidateNat, target, dict, Function.update_of_ne outsideFirst,
          Function.update_of_ne outsideSecond, Function.update_of_ne outsideId]
      have decoded : decodeMatchingDictionaryEvent k cutAt t (s.nm (s.nr 58 + i)) =
          decodeMatchingDictionaryEvent k cutAt s (s.nm (s.nr 58 + i)) := by
        rcases valid i hi with empty | ⟨own, _, _⟩
        · simp [empty, decodeMatchingDictionaryEvent]
        · have a : t.nm (s.nr 54 + (i + i)) = s.nm (s.nr 54 + (i + i)) := by
            simpa [dict] using readWord 0 (by decide)
          have b : t.nm (s.nr 54 + (i + i) + 1) = s.nm (s.nr 54 + (i + i) + 1) := readWord 1 (by decide)
          simp [own, decodeMatchingDictionaryEvent, r54, a, b]
      have slack : t.rm (t.nr 59 + i) = s.rm (s.nr 59 + i) := by
        have notSlack : s.nr 59 + i ≠ s.nr 59 + target := by omega
        have notRate : s.nr 59 + i ≠ s.nr 60 + target := by omega
        simp [r59, realEffect, installedMatchingCandidateReal, target,
          Function.update_of_ne notSlack, Function.update_of_ne notRate]
      have rate : t.rm (t.nr 60 + i) = s.rm (s.nr 60 + i) := by
        have notSlack : s.nr 60 + i ≠ s.nr 59 + target := by omega
        have notRate : s.nr 60 + i ≠ s.nr 60 + target := by omega
        simp [r60, realEffect, installedMatchingCandidateReal, target,
          Function.update_of_ne notSlack, Function.update_of_ne notRate]
      exact ⟨by simpa only [MatchingCandidateRowValid, id, decoded] using valid i hi,
        by simp only [readMatchingCandidate, id, decoded, slack, rate, if_neg (show i ≠ s.nr 18 from same)]⟩
  · obtain ⟨natEffect, realEffect⟩ := ignore improves
    have sameDecode (id : ℕ) : decodeMatchingDictionaryEvent k cutAt t id =
        decodeMatchingDictionaryEvent k cutAt s id := by simp [decodeMatchingDictionaryEvent, natEffect, r54]
    refine ⟨by simpa only [MatchingCandidateRowValid, r58, natEffect, sameDecode] using valid i hi, ?_⟩
    have sameRead : readMatchingCandidate cutAt t i = readMatchingCandidate cutAt s i := by
      simp only [readMatchingCandidate, r58, r59, r60, natEffect, realEffect, sameDecode]
    by_cases same : i = target
    · subst i
      rw [if_pos (show target = s.nr 18 from rfl), sameRead]
      simpa only [if_neg improves] using chosen
    · rw [if_neg (show i ≠ s.nr 18 from same)]
      exact sameRead


end VehicleRoutingSurvey.Routing
end RppSource_MatchingCandidateMemory

/-! matching/MatchingPairBucketMemory.lean -/
section RppSource_MatchingPairBucketMemory
namespace VehicleRoutingSurvey.Routing





theorem improveMatchingPairBucketCell_buckets {k : ℕ} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (size : s.nr 55 = k)
    {u v : Fin k} (source : s.nr 15 = u.val) (target : s.nr 16 = v.val)
    (inside : s.nr 18 < k * k) (valid : ∀ i < k * k, MatchingPairBucketValid k s i) :
    let candidate : DualSlack (MatchingDualEvent k) := ⟨.edge s(u, v), s.rr 5, 2⟩
    ∃ t steps, steps ≤ 12 ∧ BlockRuns improveMatchingPairBucketCell steps s t ∧ t.halted = false ∧
      (∀ r ≥ 15, t.nr r = s.nr r) ∧
      ∀ i < k * k, MatchingPairBucketValid k t i ∧
        readMatchingPairBucket (k := k) t i = if i = s.nr 18 then
          insertSlackCandidate candidate (readMatchingPairBucket (k := k) s i)
          else readMatchingPairBucket (k := k) s i := by
  classical
  intro candidate
  obtain ⟨t, steps, bound, run, live, writes, retains, keeps⟩ :=
    improveMatchingPairBucketCell_spec s entry running one
  refine ⟨t, steps, bound, run, live, keeps, ?_⟩
  have base := keeps 65 (by decide)
  have keys := keeps 66 (by decide)
  let addr (i : ℕ) := s.nr 65 + (i + i)
  have id : matchingPairBucketAddress s = addr (s.nr 18) := rfl
  have choose : (if matchingPairBucketImproves s then some candidate
      else readMatchingPairBucket (k := k) s (s.nr 18)) =
      insertSlackCandidate candidate (readMatchingPairBucket (k := k) s (s.nr 18)) := by
    by_cases present : s.nm (s.nr 65 + (s.nr 18 + s.nr 18)) < k
    · have other : s.nm (s.nr 65 + (s.nr 18 + s.nr 18) + 1) < k := valid (s.nr 18) inside present
      have cannot : ¬k ≤ s.nm (s.nr 65 + (s.nr 18 + s.nr 18)) := not_le_of_gt present
      simp [matchingPairBucketImproves, matchingPairBucketAddress, size, readMatchingPairBucket, present,
        other, cannot, insertSlackCandidate, candidate]
    · have missing : k ≤ s.nm (s.nr 65 + (s.nr 18 + s.nr 18)) := Nat.le_of_not_gt present
      simp [matchingPairBucketImproves, matchingPairBucketAddress, size, readMatchingPairBucket, present,
        missing, insertSlackCandidate]
  intro i hi
  by_cases improves : matchingPairBucketImproves s
  · obtain ⟨newNat, newReal⟩ := writes improves
    by_cases same : i = s.nr 18
    · subst i
      have a : t.nm (t.nr 65 + (s.nr 18 + s.nr 18)) = u.val := by
        rw [base, newNat, installedMatchingPairBucketNat, id]
        change Function.update (Function.update s.nm (addr (s.nr 18)) (s.nr 15))
          (addr (s.nr 18) + 1) (s.nr 16) (addr (s.nr 18)) = _
        simp [Function.update_of_ne (show addr (s.nr 18) ≠ addr (s.nr 18) + 1 by omega), source]
      have b : t.nm (t.nr 65 + (s.nr 18 + s.nr 18) + 1) = v.val := by
        simp [base, newNat, installedMatchingPairBucketNat, matchingPairBucketAddress, target]
      have slack : t.rm (t.nr 66 + s.nr 18) = s.rr 5 := by
        simp [keys, newReal, installedMatchingPairBucketReal]
      have new : readMatchingPairBucket (k := k) t (s.nr 18) = some candidate := by
        simp [readMatchingPairBucket, a, b, slack, u.isLt, v.isLt, candidate]
      refine ⟨by simp [MatchingPairBucketValid, a, b, v.isLt], ?_⟩
      rw [if_pos (rfl : s.nr 18 = s.nr 18), new]
      simpa only [if_pos improves] using choose
    · have bytes (offset : ℕ) (limited : offset ≤ 1) :
          t.nm (t.nr 65 + (i + i) + offset) = s.nm (addr i + offset) := by
        have before : addr i + offset ≠ addr (s.nr 18) := by dsimp [addr]; omega
        have after : addr i + offset ≠ addr (s.nr 18) + 1 := by dsimp [addr]; omega
        rw [base, newNat, installedMatchingPairBucketNat, id]
        change Function.update (Function.update s.nm (addr (s.nr 18)) (s.nr 15))
          (addr (s.nr 18) + 1) (s.nr 16) (addr i + offset) = _
        rw [Function.update_of_ne after, Function.update_of_ne before]
      have a : t.nm (t.nr 65 + (i + i)) = s.nm (s.nr 65 + (i + i)) := by
        simpa [addr] using bytes 0 (by decide)
      have b : t.nm (t.nr 65 + (i + i) + 1) = s.nm (s.nr 65 + (i + i) + 1) := bytes 1 (by decide)
      have real : t.rm (t.nr 66 + i) = s.rm (s.nr 66 + i) := by
        simp [keys, newReal, installedMatchingPairBucketReal, Function.update_of_ne (by omega :
          s.nr 66 + i ≠ s.nr 66 + s.nr 18)]
      exact ⟨by simpa only [MatchingPairBucketValid, a, b] using valid i hi,
        by simp only [readMatchingPairBucket, a, b, real, if_neg same]⟩
  · obtain ⟨natSame, realSame⟩ := retains improves
    have readSame : readMatchingPairBucket (k := k) t i = readMatchingPairBucket (k := k) s i := by
      simp only [readMatchingPairBucket, natSame, realSame, base, keys]
    refine ⟨by simpa only [MatchingPairBucketValid, natSame, base] using valid i hi, ?_⟩
    by_cases same : i = s.nr 18
    · subst i
      rw [if_pos (rfl : s.nr 18 = s.nr 18), readSame]
      simpa only [if_neg improves] using choose
    · rw [if_neg same, readSame]

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

/-- Updating the pair bucket leaves the separately allocated selector rows intact. -/
theorem improveMatchingPairBucketCell_preservesCandidates {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s t : ArithmeticState} {ticks : ℕ} (ran : BlockRuns improveMatchingPairBucketCell ticks s t)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (idsBefore : s.nr 58 + s.nr 61 ≤ s.nr 54) (recordsBefore : s.nr 54 + 2 * s.nr 61 ≤ s.nr 65)
    (slacksBefore : s.nr 59 + s.nr 61 ≤ s.nr 60) (ratesBefore : s.nr 60 + s.nr 61 ≤ s.nr 66)
    {i : ℕ} (inside : i < s.nr 61) (valid : MatchingCandidateRowValid cutAt s i) :
    MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i = readMatchingCandidate cutAt s i := by
  obtain ⟨z, steps, _, checked, _, writes, retains, fixed⟩ :=
    improveMatchingPairBucketCell_spec s entry running one
  rw [(ran.same_exit checked).2]
  have nr54 := fixed 54 (by decide)
  have nr58 := fixed 58 (by decide)
  have nr59 := fixed 59 (by decide)
  have nr60 := fixed 60 (by decide)
  have natural (a : ℕ) (before : a < s.nr 65) : z.nm a = s.nm a := by
    by_cases update : matchingPairBucketImproves s
    · rw [(writes update).1]
      have h₁ : a ≠ matchingPairBucketAddress s := by unfold matchingPairBucketAddress; omega
      have h₂ : a ≠ matchingPairBucketAddress s + 1 := by unfold matchingPairBucketAddress; omega
      simp only [installedMatchingPairBucketNat, Function.update_of_ne h₁, Function.update_of_ne h₂]
    · rw [(retains update).1]
  have real (a : ℕ) (before : a < s.nr 66) : z.rm a = s.rm a := by
    by_cases update : matchingPairBucketImproves s
    · rw [(writes update).2]
      simp only [installedMatchingPairBucketReal, Function.update_of_ne (show a ≠ s.nr 66 + s.nr 18 by omega)]
    · rw [(retains update).2]
  have id : z.nm (z.nr 58 + i) = s.nm (s.nr 58 + i) := by rw [nr58]; exact natural _ (by omega)
  have rawSlack : z.rm (z.nr 59 + i) = s.rm (s.nr 59 + i) := by rw [nr59]; exact real _ (by omega)
  have rawRate : z.rm (z.nr 60 + i) = s.rm (s.nr 60 + i) := by rw [nr60]; exact real _ (by omega)
  have decode : decodeMatchingDictionaryEvent k cutAt z (s.nm (s.nr 58 + i)) =
      decodeMatchingDictionaryEvent k cutAt s (s.nm (s.nr 58 + i)) := by
    rcases valid with empty | ⟨own, _, _⟩
    · simp [decodeMatchingDictionaryEvent, empty]
    · have first := natural (s.nr 54 + (i + i)) (by omega)
      have second := natural (s.nr 54 + (i + i) + 1) (by omega)
      simp [decodeMatchingDictionaryEvent, own, nr54, first, second]
  exact ⟨by simpa only [MatchingCandidateRowValid, id, decode] using valid,
    by simp only [readMatchingCandidate, id, decode, rawSlack, rawRate]⟩

/-- Inserting an event row also leaves the pair-bucket endpoint and key cells intact. -/
theorem improveMatchingCandidateBlock_preservesBuckets {k : ℕ} {s t : ArithmeticState} {ticks : ℕ}
    (ran : BlockRuns improveMatchingCandidateBlock ticks s t)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (slot : s.nr 18 < s.nr 61)
    (idsBefore : s.nr 58 + s.nr 61 ≤ s.nr 54) (recordsBefore : s.nr 54 + 2 * s.nr 61 ≤ s.nr 65)
    (slacksBefore : s.nr 59 + s.nr 61 ≤ s.nr 60) (ratesBefore : s.nr 60 + s.nr 61 ≤ s.nr 66)
    (i : ℕ) (valid : MatchingPairBucketValid k s i) :
    MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i = readMatchingPairBucket (k := k) s i := by
  obtain ⟨z, steps, _, checked, _, writes, retains, fixed⟩ :=
    improveMatchingCandidateBlock_spec s entry running one
  rw [(ran.same_exit checked).2]
  have nr65 := fixed 65 (by decide)
  have nr66 := fixed 66 (by decide)
  have natural (a : ℕ) (later : s.nr 65 ≤ a) : z.nm a = s.nm a := by
    by_cases update : matchingCandidateImproves s
    · rw [(writes update).1]
      have h₁ : a ≠ s.nr 58 + s.nr 18 := by omega
      have h₂ : a ≠ s.nr 54 + (s.nr 18 + s.nr 18) := by omega
      have h₃ : a ≠ s.nr 54 + (s.nr 18 + s.nr 18) + 1 := by omega
      simp only [installedMatchingCandidateNat, Function.update_of_ne h₁, Function.update_of_ne h₂,
        Function.update_of_ne h₃]
    · rw [(retains update).1]
  have real (a : ℕ) (later : s.nr 66 ≤ a) : z.rm a = s.rm a := by
    by_cases update : matchingCandidateImproves s
    · rw [(writes update).2]
      have h₁ : a ≠ s.nr 59 + s.nr 18 := by omega
      have h₂ : a ≠ s.nr 60 + s.nr 18 := by omega
      simp only [installedMatchingCandidateReal, Function.update_of_ne h₁, Function.update_of_ne h₂]
    · rw [(retains update).2]
  have first : z.nm (z.nr 65 + (i + i)) = s.nm (s.nr 65 + (i + i)) := by rw [nr65]; exact natural _ (by omega)
  have second : z.nm (z.nr 65 + (i + i) + 1) = s.nm (s.nr 65 + (i + i) + 1) := by
    rw [nr65]
    exact natural _ (by omega)
  have key : z.rm (z.nr 66 + i) = s.rm (s.nr 66 + i) := by rw [nr66]; exact real _ (by omega)
  exact ⟨by simpa only [MatchingPairBucketValid, first, second] using valid,
    by simp only [readMatchingPairBucket, first, second, key]⟩


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

/-- In a nonouter neighbor's incoming row, compare the raw slack. Retain all the other
candidate rows and pair buckets, including those already populated in this search. -/
theorem growIncomingCache_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k)) (rate : ℚ) {s : ArithmeticState}
    {u v : Fin k} (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (layout : MatchingCacheLayout k s) (source : s.nr 15 = u.val) (toward : s.nr 16 = v.val)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k * k, MatchingPairBucketValid k s i) :
    let d : DualSlack (MatchingDualEvent k) := ⟨.edge s(u, v), s.rr 0, rate⟩
    ∃ t ticks, ticks ≤ 21 ∧ BlockRuns (growIncomingCache rate) ticks s t ∧ t.halted = false ∧
      MatchingCacheLayout k t ∧ (∀ r ≥ 15, r ≠ 18 → t.nr r = s.nr r) ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧
        readMatchingCandidate cutAt t i = if i = k + v.val then
          insertSlackCandidate d (readMatchingCandidate cutAt s i) else readMatchingCandidate cutAt s i) ∧
      (∀ i < k * k, MatchingPairBucketValid k t i ∧
        readMatchingPairBucket (k := k) t i = readMatchingPairBucket (k := k) s i) := by
  intro d
  let a := {s with
    pc := 2
    nr := Function.update s.nr 18 (s.nr 55 + s.nr 16)
    rr := Function.update s.rr 4 (rate : ℝ) }
  have seed : BlockRuns [.natAdd 18 55 16, .realConst 4 rate] 2 s a := by
    apply BlockRuns.of_running_exit
    · simp [a, arithmeticStep, entry, running, Function.iterate_succ_apply']
    · exact running
    · rfl
  let start := {a with pc := 0}
  have same (r : ℕ) (away : r ≠ 18 := by decide) : start.nr r = s.nr r := by simp [start, a, away]
  have row : start.nr 18 = k + v.val := by simp [start, a, layout.dimension, toward]
  have size : start.nr 61 = 3 * k := (same 61).trans layout.rows
  have bounded : start.nr 18 < start.nr 61 := by rw [row, size]; have := v.isLt; omega
  have newLayout : MatchingCacheLayout k start := layout.keeps (fun r high => same r (by omega))
  have table (i : ℕ) (inTable : i < start.nr 61) : MatchingCandidateRowValid cutAt start i := by
    have hi : i < s.nr 61 := by rwa [same 61] at inTable
    simpa [MatchingCandidateRowValid, decodeMatchingDictionaryEvent, same 54, same 58, start, a] using rows i hi
  have encode : MatchingEventRecord cutAt (start.nr 15, start.nr 16) (.edge s(u, v)) :=
    ⟨u, v, Prod.ext ((same 15).trans source) ((same 16).trans toward), rfl⟩
  obtain ⟨b, ticks, cap, insert, live, fixed, effects⟩ := improveMatchingCandidateBlock_rows cutAt (s := start)
    rfl running ((same 9).trans one) bounded newLayout.idsBefore newLayout.slacksBefore encode table
  have newRows (i : ℕ) : readMatchingCandidate cutAt start i = readMatchingCandidate cutAt s i := by
    simp [readMatchingCandidate, decodeMatchingDictionaryEvent, same 54, same 58, same 59, same 60, start, a]
  have newBuckets (i : ℕ) : readMatchingPairBucket (k := k) start i = readMatchingPairBucket (k := k) s i := by
    simp [readMatchingPairBucket, same 65, same 66, start, a]
  let t := relocateState 2 b
  refine ⟨t, 2 + ticks, by omega, seed.append insert, live, ?_, ?_, ?_, ?_⟩
  · exact newLayout.keeps (fun r high => fixed r (by omega))
  · intro r high away
    exact (fixed r high).trans (same r away)
  · intro i hi
    have within : i < start.nr 61 := by rwa [same 61]
    have value : (⟨MatchingDualEvent.edge s(u, v), start.rr 0, start.rr 4⟩ : DualSlack _) = d := by
      simp [start, a, d]
    change MatchingCandidateRowValid cutAt b i ∧ readMatchingCandidate cutAt b i = _
    simpa only [row, value, newRows] using effects i within
  · intro i hi
    have holds : MatchingPairBucketValid k start i := by
      simpa only [MatchingPairBucketValid, same 65] using buckets i hi
    obtain ⟨kept, read⟩ := improveMatchingCandidateBlock_preservesBuckets (k := k) insert rfl running
      ((same 9).trans one) bounded newLayout.idsBefore newLayout.recordsBefore newLayout.slacksBefore
      newLayout.ratesBefore i holds
    exact ⟨kept, read.trans (newBuckets i)⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowCacheRows

/-! matching/MatchingCacheFootprint.lean -/
section RppSource_MatchingCacheFootprint
namespace VehicleRoutingSurvey.Routing

/-- A cache write lies in the contiguous range containing candidate data and
outer-pair buckets. Registry, witnesses, and effective potentials are outside. -/
structure MatchingCacheFootprint (k : ℕ) (s t : ArithmeticState) : Prop where
  natural : ∀ a, (a < s.nr 58 ∨ s.nr 65 + 2 * (k * k) ≤ a) → t.nm a = s.nm a
  real : ∀ a, (a < s.nr 59 ∨ s.nr 66 + k * k ≤ a) → t.rm a = s.rm a

theorem MatchingCacheFootprint.chain {k : ℕ} {s m t : ArithmeticState}
    (first : MatchingCacheFootprint k s m) (last : MatchingCacheFootprint k m t)
    (bases : ∀ r ∈ ([58, 59, 65, 66] : List ℕ), m.nr r = s.nr r) : MatchingCacheFootprint k s t := by
  constructor
  · intro a safe
    exact (last.natural a (by rwa [bases 58 (by decide), bases 65 (by decide)])).trans (first.natural a safe)
  · intro a safe
    exact (last.real a (by rwa [bases 59 (by decide), bases 66 (by decide)])).trans (first.real a safe)

theorem MatchingCacheFootprint.unchanged {k : ℕ} {s t : ArithmeticState} (natural : t.nm = s.nm)
    (real : t.rm = s.rm) : MatchingCacheFootprint k s t :=
  ⟨fun a _ => congrFun natural a, fun a _ => congrFun real a⟩

theorem installedCandidate_cacheFootprint {k : ℕ} {s t : ArithmeticState}
    (layout : MatchingCacheLayout k s) (slot : s.nr 18 < s.nr 61)
    (natural : t.nm = installedMatchingCandidateNat s) (real : t.rm = installedMatchingCandidateReal s) :
    MatchingCacheFootprint k s t := by
  have ids := layout.idsBefore
  have pairs := layout.recordsBefore
  have slacks := layout.slacksBefore
  have rates := layout.ratesBefore
  constructor
  · intro a outside
    rw [natural]
    simp (disch := omega) [installedMatchingCandidateNat, Function.update_of_ne]
  · intro a outside
    rw [real]
    simp (disch := omega) [installedMatchingCandidateReal, Function.update_of_ne]

theorem improveMatchingCandidateBlock_footprint {k : ℕ} {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (layout : MatchingCacheLayout k s) (slot : s.nr 18 < s.nr 61) :
    ∃ t steps, BlockRuns improveMatchingCandidateBlock steps s t ∧ t.halted = false ∧ steps ≤ 19 ∧
      MatchingCacheFootprint k s t ∧ ∀ r ≥ 15, t.nr r = s.nr r := by
  obtain ⟨t, steps, cost, runs, live, improves, stable, regs⟩ := improveMatchingCandidateBlock_spec s entry running one
  refine ⟨t, steps, runs, live, cost, ?_, regs⟩
  by_cases improve : matchingCandidateImproves s
  · exact installedCandidate_cacheFootprint layout slot (improves improve).1 (improves improve).2
  · exact MatchingCacheFootprint.unchanged (stable improve).1 (stable improve).2

theorem improveMatchingPairBucketCell_footprint {k : ℕ} {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (layout : MatchingCacheLayout k s) (slot : s.nr 18 < k * k) :
    ∃ t steps, BlockRuns improveMatchingPairBucketCell steps s t ∧ t.halted = false ∧ steps ≤ 12 ∧
      MatchingCacheFootprint k s t ∧ ∀ r ≥ 15, t.nr r = s.nr r := by
  obtain ⟨t, steps, cost, runs, live, improves, stable, regs⟩ := improveMatchingPairBucketCell_spec s entry running one
  refine ⟨t, steps, runs, live, cost, ?_, regs⟩
  by_cases improve : matchingPairBucketImproves s
  · obtain ⟨nat, real⟩ := improves improve
    have ids := layout.idsBefore
    have pairs := layout.recordsBefore
    have slacks := layout.slacksBefore
    have rates := layout.ratesBefore
    constructor
    · intro a outside
      rw [nat]
      simp (disch := omega) [installedMatchingPairBucketNat, matchingPairBucketAddress, Function.update_of_ne]
    · intro a outside
      rw [real]
      simp (disch := omega) [installedMatchingPairBucketReal, Function.update_of_ne]
  · exact MatchingCacheFootprint.unchanged (stable improve).1 (stable improve).2

theorem cachePairSlot_lt {k u v : ℕ} (uWithin : u < k) (vWithin : v < k) : k * u + v < k * k := by
  have next := Nat.mul_le_mul_left k (Nat.succ_le_of_lt uWithin)
  rw [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] at next
  omega

end VehicleRoutingSurvey.Routing
end RppSource_MatchingCacheFootprint

/-! matching/MatchingOuterCacheFootprint.lean -/
section RppSource_MatchingOuterCacheFootprint
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

structure MatchingCacheOffsets (k : ℕ) (s : ArithmeticState) : Prop where
  addresses : ∀ v < k, s.nr 21 + v < s.nr 58
  offsets : ∀ v < k, s.nm (s.nr 21 + v) = k * v

theorem MatchingCacheOffsets.keeps {k : ℕ} {s t : ArithmeticState}
    (offsets : MatchingCacheOffsets k s) (footprint : MatchingCacheFootprint k s t)
    (row : t.nr 21 = s.nr 21) (ids : t.nr 58 = s.nr 58) : MatchingCacheOffsets k t := by
  constructor
  · intro v within
    rw [row, ids]
    exact offsets.addresses v within
  · intro v within
    rw [row, footprint.natural _ (.inl (offsets.addresses v within))]
    exact offsets.offsets v within

theorem growIncomingCache_footprint {k : ℕ} {s : ArithmeticState} (rate : ℚ) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (layout : MatchingCacheLayout k s) (target : s.nr 16 < k) :
    ∃ t steps, BlockRuns (growIncomingCache rate) steps s t ∧ t.halted = false ∧ steps ≤ 21 ∧
      MatchingCacheFootprint k s t := by
  let a := { s with
    pc := 0
    nr := Function.update s.nr 18 (s.nr 55 + s.nr 16)
    rr := Function.update s.rr 4 (rate : ℝ) }
  have setup : BlockRuns (growIncomingArgs rate) 2 s {a with pc := 2} := by
    apply BlockRuns.of_running_exit
    · simp [a, growIncomingArgs, arithmeticStep, entry, running, Function.iterate_succ_apply']
    · exact running
    · rfl
  have stays (r : ℕ) (away : r ≠ 18 := by decide) : a.nr r = s.nr r := by simp [a, Function.update_of_ne away]
  have slot : a.nr 18 < a.nr 61 := by simp [a, layout.dimension, layout.rows]; omega
  obtain ⟨t, steps, runs, live, cost, footprint, _⟩ := improveMatchingCandidateBlock_footprint (s := a)
    rfl running ((stays 9).trans one) (layout.keeps (fun r hr => stays r (by omega))) slot
  have before : MatchingCacheFootprint k s a := MatchingCacheFootprint.unchanged rfl rfl
  have whole := before.chain footprint (fun r inBases => stays r (by simp at inBases; omega))
  exact ⟨_, _, setup.append runs, live, by omega, whole.natural, whole.real⟩

private theorem growOuterCacheSide_footprint {k : ℕ} {s : ArithmeticState} {source target : ℕ}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (layout : MatchingCacheLayout k s) (offsets : MatchingCacheOffsets k s)
    (u : s.nr source < k) (v : s.nr target < k) (sourceReg : 15 ≤ source) (targetReg : 15 ≤ target)
    (sourceAway : source ≠ 18) :
    ∃ t steps, BlockRuns (growOuterCacheSide source target) steps s t ∧ t.halted = false ∧ steps ≤ 35 ∧
      MatchingCacheFootprint k s t ∧ ∀ r ≥ 15, r ≠ 18 → t.nr r = s.nr r := by
  let address := s.nr 21 + s.nr source
  let loaded := Function.update (Function.update s.nr 6 address) 10 (s.nm address)
  let a := { s with pc := 0, nr := Function.update loaded 18 (s.nm address + s.nr target) }
  have prepare : BlockRuns (growBucketArgs source target) 3 s {a with pc := 3} := by
    apply BlockRuns.of_running_exit
    · have target6 : target ≠ 6 := by omega
      have target10 : target ≠ 10 := by omega
      simp [a, loaded, growBucketArgs, arithmeticStep, entry, running, address, Function.iterate_succ_apply',
        Function.update_of_ne target6, Function.update_of_ne target10]
    · exact running
    · rfl
  have keep (r : ℕ) (not6 : r ≠ 6 := by decide) (not10 : r ≠ 10 := by decide) (not18 : r ≠ 18 := by decide) :
      a.nr r = s.nr r := by simp [a, loaded, Function.update_of_ne not6, Function.update_of_ne not10, Function.update_of_ne not18]
  have flatSlot : a.nr 18 < k * k := by
    simpa [a, address, offsets.offsets (s.nr source) u] using cachePairSlot_lt u v
  have layoutA : MatchingCacheLayout k a := layout.keeps (fun r hr => keep r (by omega) (by omega) (by omega))
  have aFootprint : MatchingCacheFootprint k s a := MatchingCacheFootprint.unchanged rfl rfl
  obtain ⟨p, pairSteps, pairs, pLive, pBound, pairFrame, pKeeps⟩ :=
    improveMatchingPairBucketCell_footprint (s := a) rfl running ((keep 9).trans one) layoutA flatSlot
  let b := {p with pc := 0}
  have readStable (r : ℕ) (high : 15 ≤ r) (aside : r ≠ 18) : b.nr r = s.nr r :=
    (pKeeps r high).trans (keep r (by omega) (by omega) aside)
  have bOne : b.nr 9 = 1 := by
    change p.nr 9 = 1
    rw [← pairs.run, arithmeticRun_keeps_from_destination_list [0, 6, 10, 11] (by decide) (by decide) a pairSteps]
    exact (keep 9).trans one
  have bZero : b.nr 14 = 0 := by
    change p.nr 14 = 0
    rw [← pairs.run, arithmeticRun_keeps_from_destination_list [0, 6, 10, 11] (by decide) (by decide) a pairSteps]
    exact (keep 14).trans zero
  have pZero : p.nr 14 = 0 := bZero
  let c := {b with pc := 0, nr := Function.update b.nr 18 (b.nr source)}
  have row : BlockRuns (growOuterRowArgs source) 1 b {c with pc := 1} := by
    apply BlockRuns.of_running_exit
    · simp [c, growOuterRowArgs, arithmeticStep, pLive, b, pZero]
    · exact pLive
    · rfl
  have cFixed (r : ℕ) (away : r ≠ 18 := by decide) : c.nr r = b.nr r := by simp [c, Function.update_of_ne away]
  have cLayout : MatchingCacheLayout k c := layout.keeps
    (fun r high => (cFixed r (by omega)).trans (readStable r (by omega) (by omega)))
  have cSlot : c.nr 18 < c.nr 61 := by
    rw [show c.nr 18 = b.nr source by simp [c], readStable source sourceReg sourceAway, cLayout.rows]
    omega
  obtain ⟨t, rowSteps, rows, live, rowCost, rowFrame, tKeeps⟩ := improveMatchingCandidateBlock_footprint (s := c)
    rfl pLive ((cFixed 9).trans bOne) cLayout cSlot
  have keptBefore : MatchingCacheFootprint k s p := aFootprint.chain pairFrame
    (fun r hr => keep r (by simp at hr; omega) (by simp at hr; omega) (by simp at hr; omega))
  have uptoRow : MatchingCacheFootprint k s c := ⟨keptBefore.natural, keptBefore.real⟩
  have whole := uptoRow.chain rowFrame (fun r hr =>
    (cFixed r (by simp at hr; omega)).trans (readStable r (by simp at hr; omega) (by simp at hr; omega)))
  refine ⟨_, _, (prepare.append pairs).append (row.append rows), live, by omega, ⟨whole.natural, whole.real⟩, ?_⟩
  intro r high away
  exact (tKeeps r high).trans ((cFixed r away).trans (readStable r high away))

theorem insertMatchingOuterEdgeBlock_footprint {k : ℕ} {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (layout : MatchingCacheLayout k s) (offsets : MatchingCacheOffsets k s)
    (source : s.nr 26 < k) (target : s.nr 17 < k) :
    ∃ t steps, BlockRuns insertMatchingOuterEdgeBlock steps s t ∧ t.halted = false ∧ steps ≤ 73 ∧
      MatchingCacheFootprint k s t := by
  let score := Function.update s.rr 5 (s.rr 15 + s.rr 15 + s.rr 0)
  let a := { s with pc := 0, rr := Function.update score 4 2 }
  have normalize : BlockRuns normalizeGrowthSlack 3 s {a with pc := 3} := by
    apply BlockRuns.of_running_exit
    · simp [a, score, normalizeGrowthSlack, arithmeticStep, entry, running, Function.iterate_succ_apply', Function.update_idem]
    · exact running
    · rfl
  have unchanged : MatchingCacheFootprint k s a := MatchingCacheFootprint.unchanged rfl rfl
  have aLayout : MatchingCacheLayout k a := layout.keeps (fun _ _ => rfl)
  have aOffsets : MatchingCacheOffsets k a := offsets.keeps unchanged rfl rfl
  obtain ⟨u, firstSteps, first, live, firstCost, firstFrame, firstRegs⟩ :=
    growOuterCacheSide_footprint (s := a) (source := 26) (target := 17) rfl running one zero aLayout aOffsets
      source target (by decide) (by decide) (by decide)
  let b := {u with pc := 0}
  have stable (r : ℕ) (high : 15 ≤ r := by decide) (away : r ≠ 18 := by decide) : b.nr r = s.nr r :=
    firstRegs r high away
  have controls (r : ℕ) (safe : r ∉ [0, 6, 10, 11, 18]) : b.nr r = s.nr r := by
    change u.nr r = a.nr r
    rw [← first.run]
    exact arithmeticRun_keeps_from_destination_list _ (by decide) safe a firstSteps
  have bLayout : MatchingCacheLayout k b := layout.keeps (fun r hr => stable r (by omega) (by omega))
  have stay : MatchingCacheFootprint k s b := ⟨firstFrame.natural, firstFrame.real⟩
  have bOffsets : MatchingCacheOffsets k b := offsets.keeps stay (stable 21) (stable 58)
  obtain ⟨t, secondSteps, second, stillLive, secondCost, secondFrame, _⟩ :=
    growOuterCacheSide_footprint (s := b) (source := 17) (target := 26) rfl live
      ((controls 9 (by decide)).trans one) ((controls 14 (by decide)).trans zero) bLayout bOffsets
      (by rwa [stable 17]) (by rwa [stable 26]) (by decide) (by decide) (by decide)
  have whole := stay.chain secondFrame (fun r safe => stable r (by simp at safe; omega) (by simp at safe; omega))
  exact ⟨_, _, normalize.append (first.append second), stillLive, by omega, whole.natural, whole.real⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingOuterCacheFootprint

/-! matching/MatchingNeighborFootprint.lean -/
section RppSource_MatchingNeighborFootprint
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

structure MatchingCacheRepresentatives (k : ℕ) (s : ArithmeticState) : Prop where
  address : ∀ v < k, s.nr 57 + v < s.nr 58
  rep : ∀ v < k, s.nm (s.nr 57 + v) < k

theorem MatchingCacheRepresentatives.keeps {k : ℕ} {s t : ArithmeticState}
    (reps : MatchingCacheRepresentatives k s) (frame : MatchingCacheFootprint k s t)
    (representatives : t.nr 57 = s.nr 57) (cache : t.nr 58 = s.nr 58) : MatchingCacheRepresentatives k t := by
  constructor
  · intro v within
    rw [representatives, cache]
    exact reps.address v within
  · intro v within
    rw [representatives, frame.natural _ (.inl (reps.address v within))]
    exact reps.rep v within

private theorem cacheBranch_footprint {k : ℕ} {s : ArithmeticState}
    {left right : List ArithmeticInstruction} {l r x y : ℕ}
    (entry : s.pc = 0) (running : s.halted = false)
    (leftBranch : s.nr x ≤ s.nr y → ∃ t steps, BlockRuns left steps s t ∧ t.halted = false ∧ steps ≤ l ∧
      MatchingCacheFootprint k s t)
    (rightBranch : s.nr y < s.nr x → ∃ t steps, BlockRuns right steps s t ∧ t.halted = false ∧ steps ≤ r ∧
      MatchingCacheFootprint k s t) :
    ∃ t steps, BlockRuns (branchOnAtMost x y left right) steps s t ∧ t.halted = false ∧
      steps ≤ max l r + 2 ∧ MatchingCacheFootprint k s t := by
  by_cases choose : s.nr x ≤ s.nr y
  · obtain ⟨t, steps, runs, live, cost, keep⟩ := leftBranch choose
    have short := le_max_left l r
    exact ⟨_, _, branchOnAtMost_left x y left right entry running choose runs live,
      live, by omega, keep.natural, keep.real⟩
  · have other := Nat.lt_of_not_ge choose
    obtain ⟨t, steps, runs, live, cost, keep⟩ := rightBranch other
    have short := le_max_right l r
    exact ⟨_, _, branchOnAtMost_right x y left right entry running other runs live,
      live, by omega, keep.natural, keep.real⟩

private theorem chooseGrowthCache_footprint {k : ℕ} {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (layout : MatchingCacheLayout k s) (offsets : MatchingCacheOffsets k s)
    (source : s.nr 26 < k) (target : s.nr 17 < k) (originalTarget : s.nr 16 < k) :
    ∃ t steps, BlockRuns chooseGrowthCache steps s t ∧ t.halted = false ∧ steps ≤ 77 ∧ MatchingCacheFootprint k s t := by
  exact cacheBranch_footprint (x := 19) (y := 14) (l := 21) (r := 75) entry running
    (fun _ => growIncomingCache_footprint 1 entry running one layout originalTarget)
    (fun _ => cacheBranch_footprint (x := 19) (y := 9) (l := 73) (r := 21) entry running
      (fun _ => insertMatchingOuterEdgeBlock_footprint entry running one zero layout offsets source target)
      (fun _ => growIncomingCache_footprint 0 entry running one layout originalTarget))

theorem refreshGrowthNeighborBlock_footprint {k : ℕ} {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (layout : MatchingCacheLayout k s) (offsets : MatchingCacheOffsets k s) (reps : MatchingCacheRepresentatives k s)
    (source : s.nr 26 < k) (target : s.nr 25 < k) :
    ∃ t steps, BlockRuns refreshGrowthNeighborBlock steps s t ∧ t.halted = false ∧ steps ≤ 95 ∧
      MatchingCacheFootprint k s t := by
  let representative := s.nm (s.nr 57 + s.nr 25)
  let loaded := Function.update (Function.update (Function.update s.nr 16 (s.nr 25)) 6 (s.nr 57 + s.nr 25)) 17 representative
  let withRole := Function.update (Function.update loaded 6 (s.nr 51 + representative)) 19 (s.nm (s.nr 51 + representative))
  let a := { s with pc := 0, nr := withRole }
  have loads : BlockRuns readGrowthCacheNeighbor 5 s {a with pc := 5} := by
    apply BlockRuns.of_running_exit
    · simp [a, loaded, withRole, representative, readGrowthCacheNeighbor, arithmeticStep, entry, running, zero,
        Function.iterate_succ_apply']
    · exact running
    · rfl
  by_cases internal : a.nr 26 = a.nr 17
  · have skips := branchOnUnequal_skip 26 17 (appendBlock readExternalSlackBlock chooseGrowthCache) a rfl running internal
    exact ⟨_, _, loads.append skips, running, by decide, MatchingCacheFootprint.unchanged rfl rfl⟩
  · have read := readExternalSlackBlock_spec a rfl running
    dsimp only at read
    obtain ⟨readsSlack, live, nat, real, _, _, fixed⟩ := read
    let b := {(arithmeticStep readExternalSlackBlock)^[11] a with pc := 0}
    have stable (r : ℕ) (safe : r ∉ [6, 10, 16, 17, 19] := by decide) : b.nr r = s.nr r := by
      have f := fixed r (by simp at safe; omega) (by simp at safe; omega)
      exact f.trans (by simp [a, loaded, withRole, Function.update_of_ne (by simp at safe; omega : r ≠ 6),
        Function.update_of_ne (by simp at safe; omega : r ≠ 16), Function.update_of_ne (by simp at safe; omega : r ≠ 17),
        Function.update_of_ne (by simp at safe; omega : r ≠ 19)])
    have bSource : b.nr 26 < k := by rwa [stable 26]
    have bTarget : b.nr 17 < k := by
      change ((arithmeticStep readExternalSlackBlock)^[11] a).nr 17 < k
      rw [fixed 17 (by decide) (by decide)]
      simpa [a, loaded, withRole, representative] using reps.rep (s.nr 25) target
    have bOriginal : b.nr 16 < k := by
      change ((arithmeticStep readExternalSlackBlock)^[11] a).nr 16 < k
      rw [fixed 16 (by decide) (by decide)]
      simpa [a, loaded, withRole] using target
    have bFrame : MatchingCacheFootprint k s b := MatchingCacheFootprint.unchanged nat real
    have bLayout : MatchingCacheLayout k b := layout.keeps (fun r high => stable r (by simp; omega))
    have bOffsets : MatchingCacheOffsets k b := offsets.keeps bFrame (stable 21) (stable 58)
    obtain ⟨t, steps, chooses, stillLive, cost, changed⟩ := chooseGrowthCache_footprint (s := b) rfl live
      ((stable 9).trans one) ((stable 14).trans zero) bLayout bOffsets bSource bTarget bOriginal
    have takes := branchOnUnequal_take 26 17 (appendBlock readExternalSlackBlock chooseGrowthCache)
      (s := a) rfl running internal (readsSlack.append chooses)
    have complete := bFrame.chain changed (fun r listed => stable r (by simp at listed ⊢; omega))
    exact ⟨_, _, loads.append takes, stillLive, by omega, complete.natural, complete.real⟩

private structure NeighborFootprintScan (k : ℕ) (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  live : s.halted = false
  index : s.nr 25 = i
  fixed : ∀ r, r ∉ [0, 6, 10, 11, 16, 17, 18, 19, 25] → s.nr r = initial.nr r
  footprint : MatchingCacheFootprint k initial s

theorem refreshSelectedOuterVertex_footprint {k : ℕ} {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (layout : MatchingCacheLayout k s) (offsets : MatchingCacheOffsets k s) (reps : MatchingCacheRepresentatives k s)
    (source : s.nr 26 < k) :
    ∃ t steps, BlockRuns refreshSelectedOuterVertex steps s t ∧ t.halted = false ∧ steps ≤ 98 * k + 2 ∧
      MatchingCacheFootprint k s t := by
  have dim := layout.dimension
  let inv := NeighborFootprintScan k s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 25 0} := by
    refine ⟨rfl, running, by simp, ?_, MatchingCacheFootprint.unchanged rfl rfl⟩
    intro r safe
    exact Function.update_of_ne (by simp at safe; omega) _ _
  have control (i : ℕ) (m : ArithmeticState) (h : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 25 = i ∧ m.nr 55 = k :=
    ⟨h.entry, h.live, h.index, (h.fixed 55 (by decide)).trans dim⟩
  have next (i : ℕ) (within : i < k) (m : ArithmeticState) (h : inv i m) :
      ∃ t steps, steps ≤ 95 ∧ BlockRuns refreshGrowthNeighborBlock steps m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 25 (t.nr 25 + t.nr 9)} := by
    have fixed (r : ℕ) (safe : r ∉ [0, 6, 10, 11, 16, 17, 18, 19, 25] := by decide) : m.nr r = s.nr r := h.fixed r safe
    obtain ⟨t, steps, runs, live, cost, written⟩ := refreshGrowthNeighborBlock_footprint h.entry h.live
      ((fixed 9).trans one) ((fixed 14).trans zero) (layout.keeps (fun r hr => fixed r (by simp; omega)))
      (offsets.keeps h.footprint (fixed 21) (fixed 58)) (reps.keeps h.footprint (fixed 57) (fixed 58))
      (by rwa [fixed 26]) (by rwa [h.index])
    have kept (r : ℕ) (safe : r ∉ [0, 6, 10, 11, 16, 17, 18, 19]) : t.nr r = m.nr r := by
      rw [← runs.run]
      exact arithmeticRun_keeps_from_destination_list _ (by decide) safe m steps
    have combined := h.footprint.chain written (fun r b => fixed r (by simp at b ⊢; omega))
    refine ⟨t, steps, cost, runs, live, rfl, live, ?_, ?_, combined.natural, combined.real⟩
    · simp [kept 25 (by decide), kept 9 (by decide), h.index, fixed 9, one]
    · intro r safe
      change Function.update t.nr 25 (t.nr 25 + t.nr 9) r = s.nr r
      rw [Function.update_of_ne (by simp at safe; omega : r ≠ 25)]
      exact (kept r (by simp at safe ⊢; omega)).trans (fixed r safe)
  obtain ⟨_, steps, done, cost, runs⟩ := countedLoopFromZero_bounded 9 25 55 k 95
    refreshGrowthNeighborBlock inv entry running initial control next
  exact ⟨_, steps, runs, done.live, by omega, done.footprint.natural, done.footprint.real⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingNeighborFootprint

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

/-! matching/MatchingGrowOuterRows.lean -/
section RppSource_MatchingGrowOuterRows
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096 in
/-- Update the one directed block bucket and its source's candidate row. The bucket
compares normalized keys and the selector row compares raw slacks. -/
theorem growOuterCacheSide_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k)) (source target : ℕ)
    {s : ArithmeticState} {u v src dst : Fin k} (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 9 = 1) (zero : s.nr 14 = 0) (layout : MatchingCacheLayout k s)
    (fromHigh : 15 ≤ source) (toHigh : 15 ≤ target) (fromSafe : source ≠ 18)
    (fromBlock : s.nr source = src.val) (toBlock : s.nr target = dst.val)
    (fromPort : s.nr 15 = u.val) (toPort : s.nr 16 = v.val) (rate : s.rr 4 = 2)
    (offset : s.nm (s.nr 21 + src.val) = k * src.val)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k * k, MatchingPairBucketValid k s i) :
    let raw : DualSlack (MatchingDualEvent k) := ⟨.edge s(u, v), s.rr 0, 2⟩
    let key : DualSlack (MatchingDualEvent k) := ⟨.edge s(u, v), s.rr 5, 2⟩
    let column := k * src.val + dst.val
    ∃ t ticks, ticks ≤ 35 ∧ BlockRuns (growOuterCacheSide source target) ticks s t ∧ t.halted = false ∧
      MatchingCacheLayout k t ∧ (∀ r ≥ 15, r ≠ 18 → t.nr r = s.nr r) ∧
      (∀ r ∈ [0, 4, 5, 15], t.rr r = s.rr r) ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧
        readMatchingCandidate cutAt t i = if i = src.val then
          insertSlackCandidate raw (readMatchingCandidate cutAt s i) else readMatchingCandidate cutAt s i) ∧
      (∀ i < k * k, MatchingPairBucketValid k t i ∧
        readMatchingPairBucket (k := k) t i = if i = column then
          insertSlackCandidate key (readMatchingPairBucket (k := k) s i) else readMatchingPairBucket (k := k) s i) := by
  intro raw key column
  let args := {s with
    pc := 3
    nr := Function.update (Function.update (Function.update s.nr 6 (s.nr 21 + src.val)) 10 (k * src.val)) 18 column}
  have chooseBucket : BlockRuns (growBucketArgs source target) 3 s args := by
    apply BlockRuns.of_running_exit
    · simp [growBucketArgs, args, arithmeticStep, Function.iterate_succ_apply', entry, running,
        fromBlock, toBlock, offset, Function.update_of_ne (show target ≠ 6 by omega),
        Function.update_of_ne (show target ≠ 10 by omega), column]
    · exact running
    · rfl
  let a := {args with pc := 0}
  have aFixed (r : ℕ) (away : r ∉ [6, 10, 18] := by decide) : a.nr r = s.nr r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at away
    obtain ⟨h6, h10, h18⟩ := away
    simp [a, args, h6, h10, h18]
  have aLayout : MatchingCacheLayout k a := layout.keeps (fun r high => aFixed r (by simp; omega))
  have index : a.nr 18 = column := by simp [a, args]
  have inside : a.nr 18 < k * k := by
    have room := Nat.mul_le_mul_left k (Nat.succ_le_of_lt src.isLt)
    rw [Nat.mul_succ] at room
    rw [index]
    have := dst.isLt
    dsimp [column]
    omega
  have aBuckets (i : ℕ) (hi : i < k * k) : MatchingPairBucketValid k a i := by
    simpa only [MatchingPairBucketValid, aFixed 65] using buckets i hi
  obtain ⟨b, bucketTicks, bucketCost, bucketRun, bLive, bHigh, bEffects⟩ :=
    improveMatchingPairBucketCell_buckets (s := a) rfl running ((aFixed 9).trans one) aLayout.dimension
      ((aFixed 15).trans fromPort) ((aFixed 16).trans toPort) inside aBuckets
  have bFixed (r : ℕ) (safe : r ∉ [0, 6, 10, 11] := by decide)
      (away : r ∉ [6, 10, 18] := by decide) : b.nr r = s.nr r := by
    rw [← bucketRun.run]
    exact (arithmeticRun_keeps_from_destination_list _ (by decide) safe a bucketTicks).trans (aFixed r away)
  have bZero : b.nr 14 = 0 := (bFixed 14).trans zero
  have bSource : b.nr source = src.val := by
    exact ((bHigh source fromHigh).trans (aFixed source (by simp [fromSafe]; omega))).trans fromBlock
  let bInput := {b with pc := 0}
  let rowArgs := {bInput with pc := 1, nr := Function.update bInput.nr 18 src.val}
  have chooseRow : BlockRuns (growOuterRowArgs source) 1 bInput rowArgs := by
    apply BlockRuns.of_running_exit
    · have openState : bInput.halted = false := bLive
      have rowZero : bInput.nr 14 = 0 := bZero
      have rowRep : bInput.nr source = src.val := bSource
      simp [rowArgs, arithmeticStep, growOuterRowArgs, openState, rowZero, rowRep, show bInput.pc = 0 from rfl]
    · exact bLive
    · rfl
  let c := {rowArgs with pc := 0}
  have cFixed (r : ℕ) (away : r ≠ 18 := by decide) : c.nr r = b.nr r := by simp [c, rowArgs, bInput, away]
  have cLayout : MatchingCacheLayout k c := aLayout.keeps
    (fun r high => (cFixed r (by omega)).trans (bHigh r (by omega)))
  have cRow : c.nr 18 = src.val := by simp [c, rowArgs]
  have room : c.nr 18 < c.nr 61 := by rw [cRow, cLayout.rows]; have := src.isLt; omega
  have cEncode : MatchingEventRecord cutAt (c.nr 15, c.nr 16) (.edge s(u, v)) := by
    exact ⟨u, v, Prod.ext (((cFixed 15).trans (bFixed 15)).trans fromPort)
      (((cFixed 16).trans (bFixed 16)).trans toPort), rfl⟩
  have aRows (i : ℕ) (hi : i < s.nr 61) : MatchingCandidateRowValid cutAt a i := by
    have decode (id : ℕ) : decodeMatchingDictionaryEvent k cutAt a id = decodeMatchingDictionaryEvent k cutAt s id := by
      simp only [decodeMatchingDictionaryEvent, aFixed 54, show a.nm = s.nm from rfl]
    simpa only [MatchingCandidateRowValid, aFixed 58, show a.nm = s.nm from rfl, decode] using rows i hi
  have aRead (i : ℕ) : readMatchingCandidate cutAt a i = readMatchingCandidate cutAt s i := by
    simp only [readMatchingCandidate, decodeMatchingDictionaryEvent, aFixed 54, aFixed 58, aFixed 59, aFixed 60,
      show a.nm = s.nm from rfl, show a.rm = s.rm from rfl]
  have bRows (i : ℕ) (hi : i < s.nr 61) :
      MatchingCandidateRowValid cutAt b i ∧ readMatchingCandidate cutAt b i = readMatchingCandidate cutAt s i := by
    obtain ⟨valid, read⟩ := improveMatchingPairBucketCell_preservesCandidates cutAt bucketRun rfl running
      ((aFixed 9).trans one) aLayout.idsBefore aLayout.recordsBefore aLayout.slacksBefore aLayout.ratesBefore
      (by rwa [aFixed 61]) (aRows i hi)
    exact ⟨valid, read.trans (aRead i)⟩
  have cDecode (id : ℕ) : decodeMatchingDictionaryEvent k cutAt c id = decodeMatchingDictionaryEvent k cutAt b id := by
    simp only [decodeMatchingDictionaryEvent, cFixed 54, show c.nm = b.nm from rfl]
  have cRows (i : ℕ) (hi : i < c.nr 61) : MatchingCandidateRowValid cutAt c i := by
    rw [cLayout.rows, ← layout.rows] at hi
    simpa only [MatchingCandidateRowValid, cFixed 58, show c.nm = b.nm from rfl, cDecode] using (bRows i hi).1
  have cRead (i : ℕ) (hi : i < s.nr 61) : readMatchingCandidate cutAt c i = readMatchingCandidate cutAt s i := by
    simpa only [readMatchingCandidate, cFixed 58, cFixed 59, cFixed 60, show c.nm = b.nm from rfl,
      show c.rm = b.rm from rfl, cDecode] using (bRows i hi).2
  have cOne : c.nr 9 = 1 := ((cFixed 9).trans (bFixed 9)).trans one
  obtain ⟨d, rowTicks, rowCost, rowRun, live, dHigh, dEffects⟩ :=
    improveMatchingCandidateBlock_rows cutAt (s := c) rfl bLive cOne room cLayout.idsBefore cLayout.slacksBefore cEncode cRows
  have joined : BlockRuns (growOuterCacheSide source target) ((3 + bucketTicks) + (1 + rowTicks)) s _ :=
    (chooseBucket.append bucketRun).append (chooseRow.append rowRun)
  have keepReals (r : ℕ) (among : r ∈ [0, 4, 5, 15]) : d.rr r = s.rr r := by
    have keptBucket : b.rr r = a.rr r := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at among
      rcases among with rfl | rfl | rfl | rfl <;> exact bucketRun.keeps_cache_real (by decide)
    have keptRow : d.rr r = c.rr r := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at among
      rcases among with rfl | rfl | rfl | rfl <;> exact rowRun.keeps_cache_real (by decide)
    exact keptRow.trans keptBucket
  refine ⟨_, _, by omega, joined, live, cLayout.keeps (fun r high => dHigh r (by omega)), ?_, keepReals, ?_, ?_⟩
  · intro r high notRow
    exact (dHigh r high).trans ((cFixed r notRow).trans ((bHigh r high).trans (aFixed r (by simp [notRow]; omega))))
  · intro i hi
    have hiC : i < c.nr 61 := by simpa only [cLayout.rows, ← layout.rows] using hi
    have cell : (⟨MatchingDualEvent.edge s(u, v), c.rr 0, c.rr 4⟩ : DualSlack _) = raw := by
      have slack : c.rr 0 = s.rr 0 := bucketRun.keeps_cache_real (by decide)
      have speed : c.rr 4 = s.rr 4 := bucketRun.keeps_cache_real (by decide)
      simp only [slack, speed, rate, raw]
    change MatchingCandidateRowValid cutAt d i ∧ readMatchingCandidate cutAt d i = _
    simpa only [cRow, cell, cRead i hi] using dEffects i hiC
  · intro i hi
    have rowBucket : MatchingPairBucketValid k c i := by
      simpa only [MatchingPairBucketValid, cFixed 65, show c.nm = b.nm from rfl] using (bEffects i hi).1
    have readC : readMatchingPairBucket (k := k) c i = readMatchingPairBucket (k := k) b i := by
      simp only [readMatchingPairBucket, cFixed 65, cFixed 66, show c.nm = b.nm from rfl, show c.rm = b.rm from rfl]
    have readA : readMatchingPairBucket (k := k) a i = readMatchingPairBucket (k := k) s i := by
      simp only [readMatchingPairBucket, aFixed 65, aFixed 66, show a.nm = s.nm from rfl, show a.rm = s.rm from rfl]
    obtain ⟨sound, readD⟩ := improveMatchingCandidateBlock_preservesBuckets (k := k) rowRun rfl bLive cOne room
      cLayout.idsBefore cLayout.recordsBefore cLayout.slacksBefore cLayout.ratesBefore i rowBucket
    refine ⟨sound, (readD.trans readC).trans ?_⟩
    simpa only [readA, index, show a.rr 5 = s.rr 5 from rfl, key] using (bEffects i hi).2


end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowOuterRows

/-! matching/MatchingOuterCacheRows.lean -/
section RppSource_MatchingOuterCacheRows
namespace VehicleRoutingSurvey.Routing

private theorem directedBucket_slots_distinct {k : ℕ} {a b : Fin k} (separate : a ≠ b) :
    k * a.val + b.val ≠ k * b.val + a.val := by
  intro same
  exact separate (Fin.ext ((denseMatrixOffset_eq_iff b.isLt a.isLt).mp same).1)

set_option maxRecDepth 4096 in
/-- Insert one original edge into both directed buckets and both candidate
rows. Bucket scores use the common outer offset, and selector slacks stay raw. -/
theorem insertMatchingOuterEdgeBlock_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} {u v src dst : Fin k} (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 9 = 1) (zero : s.nr 14 = 0) (layout : MatchingCacheLayout k s)
    (fromBlock : s.nr 26 = src.val) (toBlock : s.nr 17 = dst.val) (separate : src ≠ dst)
    (fromPort : s.nr 15 = u.val) (toPort : s.nr 16 = v.val)
    (offsets : ∀ x : Fin k, s.nm (s.nr 21 + x.val) = k * x.val)
    (offsetsBefore : s.nr 21 + k ≤ s.nr 58)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k * k, MatchingPairBucketValid k s i) :
    let raw : DualSlack (MatchingDualEvent k) := ⟨.edge s(u, v), s.rr 0, 2⟩
    let keyed : DualSlack (MatchingDualEvent k) := ⟨.edge s(u, v), s.rr 15 + s.rr 15 + s.rr 0, 2⟩
    ∃ t ticks, ticks ≤ 73 ∧ BlockRuns insertMatchingOuterEdgeBlock ticks s t ∧ t.halted = false ∧
      MatchingCacheLayout k t ∧ (∀ r ≥ 15, r ≠ 18 → t.nr r = s.nr r) ∧
      (t.rr 0 = s.rr 0 ∧ t.rr 15 = s.rr 15) ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧
        readMatchingCandidate cutAt t i = if i = src.val ∨ i = dst.val then
          insertSlackCandidate raw (readMatchingCandidate cutAt s i) else readMatchingCandidate cutAt s i) ∧
      (∀ i < k * k, MatchingPairBucketValid k t i ∧
        readMatchingPairBucket (k := k) t i = if i = k * src.val + dst.val ∨ i = k * dst.val + src.val then
          insertSlackCandidate keyed (readMatchingPairBucket (k := k) s i) else readMatchingPairBucket (k := k) s i) := by
  intro raw keyed
  let seeded := { s with
    pc := 3
    rr := Function.update (Function.update s.rr 5 (s.rr 15 + s.rr 15 + s.rr 0)) 4 2 }
  have seed : BlockRuns normalizeGrowthSlack 3 s seeded := by
    apply BlockRuns.of_running_exit
    · simp [seeded, normalizeGrowthSlack, arithmeticStep, entry, running, Function.iterate_succ_apply', Function.update_idem]
    · exact running
    · rfl
  let a := {seeded with pc := 0}
  have aRate : a.rr 4 = 2 := by simp [a, seeded]
  have aLayout : MatchingCacheLayout k a := layout.keeps (fun _ _ => rfl)
  have aRows (i : ℕ) (hi : i < a.nr 61) : MatchingCandidateRowValid cutAt a i := rows i hi
  have aBuckets (i : ℕ) (hi : i < k * k) : MatchingPairBucketValid k a i := buckets i hi
  obtain ⟨first, firstTicks, firstBound, firstRun, firstLive, firstLayout, firstFixed, firstReals, firstRows, firstBuckets⟩ :=
    growOuterCacheSide_rows cutAt 26 17 (s := a) rfl running one zero aLayout (by decide) (by decide) (by decide)
      fromBlock toBlock fromPort toPort aRate (offsets src) aRows aBuckets
  let b := {first with pc := 0}
  have bLayout : MatchingCacheLayout k b := by
    constructor <;> first
      | exact firstLayout.dimension | exact firstLayout.rows | exact firstLayout.idsBefore
      | exact firstLayout.recordsBefore | exact firstLayout.slacksBefore | exact firstLayout.ratesBefore
  have keep (r : ℕ) (high : 15 ≤ r := by decide) (away : r ≠ 18 := by decide) : b.nr r = s.nr r := firstFixed r high away
  have keepLow (r : ℕ) (outside : r ∉ [0, 6, 10, 11, 18] := by decide) : b.nr r = s.nr r := by
    change first.nr r = _
    rw [← firstRun.run]
    exact arithmeticRun_keeps_from_destination_list [0, 6, 10, 11, 18] (by decide) outside a firstTicks
  have bRate : b.rr 4 = 2 := (firstReals 4 (by decide)).trans aRate
  have dict : a.nr 58 ≤ a.nr 54 := by have h := aLayout.idsBefore; omega
  have pairAfter : a.nr 58 ≤ a.nr 65 := by
    have h₁ := aLayout.idsBefore
    have h₂ := aLayout.recordsBefore
    omega
  obtain ⟨checked, _, _, checkedRun, _, firstFrame⟩ := growOuterCacheSide_frames 26 17 a rfl running one dict pairAfter
  have sameExit : checked = first := (checkedRun.same_exit firstRun).2
  rw [sameExit] at firstFrame
  have bOffset : b.nm (b.nr 21 + dst.val) = k * dst.val := by
    rw [keep 21]
    have earlier : s.nr 21 + dst.val < a.nr 58 := by
      change s.nr 21 + dst.val < s.nr 58
      have bound := dst.isLt
      omega
    exact (firstFrame.natural _ earlier).trans (offsets dst)
  have bRows (i : ℕ) (hi : i < b.nr 61) : MatchingCandidateRowValid cutAt b i := by
    rw [keep 61] at hi
    exact (firstRows i hi).1
  have bBuckets (i : ℕ) (hi : i < k * k) : MatchingPairBucketValid k b i := (firstBuckets i hi).1
  obtain ⟨t, secondTicks, secondBound, secondRun, live, endLayout, secondFixed, secondReals, secondRows, secondBuckets⟩ :=
    growOuterCacheSide_rows cutAt 17 26 (s := b) rfl firstLive ((keepLow 9).trans one) ((keepLow 14).trans zero)
      bLayout (by decide) (by decide) (by decide) ((keep 17).trans toBlock) ((keep 26).trans fromBlock)
      ((keep 15).trans fromPort) ((keep 16).trans toPort) bRate bOffset bRows bBuckets
  have aZero : a.rr 0 = s.rr 0 := by simp [a, seeded]
  have aTime : a.rr 15 = s.rr 15 := by simp [a, seeded]
  have aKey : a.rr 5 = s.rr 15 + s.rr 15 + s.rr 0 := by simp [a, seeded]
  have bZero : b.rr 0 = s.rr 0 := (firstReals 0 (by decide)).trans aZero
  have bTime : b.rr 15 = s.rr 15 := (firstReals 15 (by decide)).trans aTime
  have bKey : b.rr 5 = s.rr 15 + s.rr 15 + s.rr 0 := (firstReals 5 (by decide)).trans aKey
  have aCandidate (i : ℕ) : readMatchingCandidate cutAt a i = readMatchingCandidate cutAt s i := rfl
  have aPair (i : ℕ) : readMatchingPairBucket (k := k) a i = readMatchingPairBucket (k := k) s i := rfl
  have pairSlots := directedBucket_slots_distinct separate
  have slots : src.val ≠ dst.val := fun eq => separate (Fin.ext eq)
  have complete : BlockRuns insertMatchingOuterEdgeBlock (3 + (firstTicks + secondTicks)) s _ :=
    seed.append (firstRun.append secondRun)
  refine ⟨_, _, by omega, complete, live, ?_, ?_, ⟨(secondReals 0 (by decide)).trans bZero,
    (secondReals 15 (by decide)).trans bTime⟩, ?_, ?_⟩
  · constructor <;> first
      | exact endLayout.dimension | exact endLayout.rows | exact endLayout.idsBefore
      | exact endLayout.recordsBefore | exact endLayout.slacksBefore | exact endLayout.ratesBefore
  · intro r high away
    exact (secondFixed r high away).trans (keep r high away)
  · intro i hi
    have within : i < b.nr 61 := by rwa [keep 61]
    have old : readMatchingCandidate cutAt b i = if i = src.val then
        insertSlackCandidate raw (readMatchingCandidate cutAt s i) else readMatchingCandidate cutAt s i := by
      change readMatchingCandidate cutAt first i = _
      simpa only [aCandidate i, aZero, raw] using (firstRows i hi).2
    obtain ⟨sound, read⟩ := secondRows i within
    change MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i = _
    refine ⟨sound, read.trans ?_⟩
    rw [old]
    by_cases atDst : i = dst.val
    · simp [atDst, Ne.symm slots, bZero, raw]
    · by_cases atSrc : i = src.val <;> simp [atDst, atSrc, slots, bZero, raw]
  · intro i hi
    have old : readMatchingPairBucket (k := k) b i = if i = k * src.val + dst.val then
        insertSlackCandidate keyed (readMatchingPairBucket (k := k) s i) else readMatchingPairBucket (k := k) s i := by
      change readMatchingPairBucket (k := k) first i = _
      simpa only [aPair i, aKey, keyed] using (firstBuckets i hi).2
    obtain ⟨sound, read⟩ := secondBuckets i hi
    change MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i = _
    refine ⟨sound, read.trans ?_⟩
    rw [old]
    by_cases atDst : i = k * dst.val + src.val
    · simp [atDst, Ne.symm pairSlots, bKey, keyed]
    · by_cases atSrc : i = k * src.val + dst.val <;> simp [atDst, atSrc, pairSlots, bKey, keyed]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingOuterCacheRows

/-! matching/MatchingRefreshInputs.lean -/
section RppSource_MatchingRefreshInputs
namespace VehicleRoutingSurvey.Routing

noncomputable def outerNeighborRowCandidate {k : ℕ} (u v src dst : Fin k) (role : ℕ) (slack : ℝ) (i : ℕ) :
    Option (DualSlack (MatchingDualEvent k)) :=
  if role = 1 then
    if i = src.val ∨ i = dst.val then some ⟨.edge s(u, v), slack, 2⟩ else none
  else if i = k + v.val then some ⟨.edge s(u, v), slack, if role = 0 then 1 else 0⟩ else none

noncomputable def outerNeighborPairCandidate {k : ℕ} (u v src dst : Fin k) (role : ℕ) (key : ℝ) (i : ℕ) :
    Option (DualSlack (MatchingDualEvent k)) :=
  if role = 1 ∧ (i = k * src.val + dst.val ∨ i = k * dst.val + src.val) then
    some ⟨.edge s(u, v), key, 2⟩ else none

/-- The candidate and normalized key offered by an outer original to one cache row. -/
noncomputable def outerRefreshRowInput {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (u v : Fin k) (row : ℕ) :
    Option (DualSlack (MatchingDualEvent k)) :=
  if rep u = rep v then none else outerNeighborRowCandidate u v (rep u) (rep v) (role (rep v))
    (cost u v - effective u - effective v) row

noncomputable def outerRefreshPairInput {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (time : ℝ) (u v : Fin k) (slot : ℕ) :
    Option (DualSlack (MatchingDualEvent k)) :=
  if rep u = rep v then none else outerNeighborPairCandidate u v (rep u) (rep v) (role (rep v))
    (time + time + (cost u v - effective u - effective v)) slot

end VehicleRoutingSurvey.Routing
end RppSource_MatchingRefreshInputs

/-! matching/MatchingChooseCacheRows.lean -/
section RppSource_MatchingChooseCacheRows
namespace VehicleRoutingSurvey.Routing

/-- Exact candidate and normalized-bucket refinement for the three neighbor
labels. The actual code assigns rates two, one, and zero to outer, unlabelled,
and inner neighbors, respectively. -/
theorem chooseGrowthCache_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} {u v src dst : Fin k} (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 9 = 1) (zero : s.nr 14 = 0) (layout : MatchingCacheLayout k s)
    (fromBlock : s.nr 26 = src.val) (toBlock : s.nr 17 = dst.val) (separate : src ≠ dst)
    (fromPort : s.nr 15 = u.val) (toPort : s.nr 16 = v.val)
    (offsets : ∀ x : Fin k, s.nm (s.nr 21 + x.val) = k * x.val) (offsetsBefore : s.nr 21 + k ≤ s.nr 58)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k * k, MatchingPairBucketValid k s i) :
    ∃ t steps, steps ≤ 77 ∧ BlockRuns chooseGrowthCache steps s t ∧ t.halted = false ∧
      MatchingCacheLayout k t ∧ (∀ r ≥ 15, r ≠ 18 → t.nr r = s.nr r) ∧ t.rr 15 = s.rr 15 ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧
        readMatchingCandidate cutAt t i = (outerNeighborRowCandidate u v src dst (s.nr 19) (s.rr 0) i).elim
          (readMatchingCandidate cutAt s i) (fun d => insertSlackCandidate d (readMatchingCandidate cutAt s i))) ∧
      (∀ i < k * k, MatchingPairBucketValid k t i ∧
        readMatchingPairBucket (k := k) t i =
          (outerNeighborPairCandidate u v src dst (s.nr 19) (s.rr 15 + s.rr 15 + s.rr 0) i).elim
            (readMatchingPairBucket (k := k) s i) (fun d => insertSlackCandidate d (readMatchingPairBucket (k := k) s i))) := by
  let later := branchOnAtMost 19 9 insertMatchingOuterEdgeBlock (growIncomingCache 0)
  by_cases unlabelled : s.nr 19 = 0
  · obtain ⟨t, ticks, bound, ran, live, _, fixed, candidates, pair⟩ :=
      growIncomingCache_rows cutAt 1 (s := s) entry running one layout fromPort toPort rows buckets
    have route := branchOnAtMost_left 19 14 (growIncomingCache 1) later (s := s) entry running
      (by rw [unlabelled, zero]) ran live
    have time := ran.keeps_cache_real (r := 15) (by decide)
    refine ⟨_, _, by omega, route, live, layout.keeps (fun r hr => fixed r (by omega) (by omega)), fixed, time, ?_, ?_⟩
    · intro i hi
      change MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i = _
      by_cases write : i = k + v.val <;> simpa [outerNeighborRowCandidate, unlabelled, write] using candidates i hi
    · intro i hi
      change MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i = _
      simpa [outerNeighborPairCandidate, unlabelled] using pair i hi
  · have skipZero : s.nr 14 < s.nr 19 := by rw [zero]; omega
    by_cases outer : s.nr 19 = 1
    · obtain ⟨t, ticks, bound, ran, live, _, fixed, time, candidates, pair⟩ :=
        insertMatchingOuterEdgeBlock_rows cutAt (s := s) entry running one zero layout fromBlock toBlock separate fromPort toPort
          offsets offsetsBefore rows buckets
      have choose := branchOnAtMost_left 19 9 insertMatchingOuterEdgeBlock (growIncomingCache 0) (s := s) entry running
        (by rw [outer, one]) ran live
      have route := branchOnAtMost_right 19 14 (growIncomingCache 1) later (s := s) entry running skipZero choose live
      refine ⟨_, _, by omega, route, live, layout.keeps (fun r hr => fixed r (by omega) (by omega)), fixed, time.2, ?_, ?_⟩
      · intro i hi
        change MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i = _
        by_cases write : i = src.val ∨ i = dst.val <;> simpa [outerNeighborRowCandidate, outer, write] using candidates i hi
      · intro i hi
        change MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i = _
        by_cases write : i = k * src.val + dst.val ∨ i = k * dst.val + src.val <;>
          simpa [outerNeighborPairCandidate, outer, write] using pair i hi
    · have inner : s.nr 9 < s.nr 19 := by rw [one]; omega
      obtain ⟨t, ticks, bound, ran, live, _, fixed, candidates, pair⟩ :=
        growIncomingCache_rows cutAt 0 (s := s) entry running one layout fromPort toPort rows buckets
      have choose := branchOnAtMost_right 19 9 insertMatchingOuterEdgeBlock (growIncomingCache 0) (s := s) entry running inner ran live
      have route := branchOnAtMost_right 19 14 (growIncomingCache 1) later (s := s) entry running skipZero choose live
      have time := ran.keeps_cache_real (r := 15) (by decide)
      refine ⟨_, _, by omega, route, live, layout.keeps (fun r hr => fixed r (by omega) (by omega)), fixed, time, ?_, ?_⟩
      · intro i hi
        change MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i = _
        by_cases write : i = k + v.val <;> simpa [outerNeighborRowCandidate, outer, unlabelled, write] using candidates i hi
      · intro i hi
        change MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i = _
        simpa [outerNeighborPairCandidate, outer] using pair i hi

end VehicleRoutingSurvey.Routing
end RppSource_MatchingChooseCacheRows

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

theorem refreshGrowthNeighborBlock_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} {rep : Fin k → Fin k} {role : Fin k → ℕ}
    {cost : Fin k → Fin k → ℝ} {effective : Fin k → ℝ} {u v : Fin k}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (input : MatchingRefreshInput s rep role cost effective)
    (origin : s.nr 15 = u.val) (neighbor : s.nr 25 = v.val) (source : s.nr 26 = (rep u).val)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k*k, MatchingPairBucketValid k s i) :
    ∃ t steps, steps ≤ 95 ∧ BlockRuns refreshGrowthNeighborBlock steps s t ∧ t.halted = false ∧
      (∀ r, r ∉ [0, 6, 10, 11, 16, 17, 18, 19] → t.nr r = s.nr r) ∧ t.rr 15 = s.rr 15 ∧
      CacheMemoryFrame s t ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧
        readMatchingCandidate cutAt t i = (outerRefreshRowInput rep role cost effective u v i).elim
          (readMatchingCandidate cutAt s i) (fun d => insertSlackCandidate d (readMatchingCandidate cutAt s i))) ∧
      (∀ i < k*k, MatchingPairBucketValid k t i ∧
        readMatchingPairBucket (k := k) t i = (outerRefreshPairInput rep role cost effective (s.rr 15) u v i).elim
          (readMatchingPairBucket (k := k) s i) (fun d => insertSlackCandidate d (readMatchingPairBucket (k := k) s i))) := by
  let addresses := Function.update (Function.update (Function.update s.nr 16 v.val)
    6 (s.nr 51 + (rep v).val)) 17 (rep v).val
  let loaded := {s with pc := 5, nr := Function.update addresses 19 (role (rep v))}
  have load : BlockRuns readGrowthCacheNeighbor 5 s loaded := by
    apply BlockRuns.of_running_exit
    · simp [loaded, addresses, readGrowthCacheNeighbor, arithmeticStep, entry, running, zero, neighbor,
        input.representatives v, input.roles (rep v), Function.iterate_succ_apply', Function.update_idem, Function.update_comm]
    · exact running
    · rfl
  let a := {loaded with pc := 0}
  have aKeep (r : ℕ) (safe : r ∉ [6, 16, 17, 19] := by decide) : a.nr r = s.nr r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at safe
    obtain ⟨r6, r16, r17, r19⟩ := safe
    simp [a, loaded, addresses, r6, r16, r17, r19]
  have aOther : a.nr 17 = (rep v).val := by simp [a, loaded, addresses]
  have aSource : a.nr 26 = (rep u).val := (aKeep 26).trans source
  have aNeighbor : a.nr 16 = v.val := by simp [a, loaded, addresses]
  have aLabel : a.nr 19 = role (rep v) := by simp [a, loaded, addresses]
  have fixed (r : ℕ) (safe : r ∉ [0, 6, 10, 11, 16, 17, 18, 19]) {t : ArithmeticState} {ticks : ℕ}
      (run : BlockRuns refreshGrowthNeighborBlock ticks s t) : t.nr r = s.nr r := by
    rw [← run.run]
    exact arithmeticRun_keeps_from_destination_list _ (by decide) safe s ticks
  let visit := appendBlock readExternalSlackBlock chooseGrowthCache
  by_cases internal : rep u = rep v
  · have same : a.nr 26 = a.nr 17 := by rw [aSource, aOther, internal]
    have skip := branchOnUnequal_skip 26 17 visit a rfl running same
    have run : BlockRuns refreshGrowthNeighborBlock 7 s _ := load.append skip
    refine ⟨_, _, by decide, run, running, fun r hr => fixed r hr run, rfl, ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩, ?_, ?_⟩
    · intro i hi
      change MatchingCandidateRowValid cutAt a i ∧ readMatchingCandidate cutAt a i = _
      simpa only [outerRefreshRowInput, if_pos internal, Option.elim_none, MatchingCandidateRowValid,
        readMatchingCandidate, decodeMatchingDictionaryEvent, aKeep 54, aKeep 58, aKeep 59, aKeep 60,
        show a.nm = s.nm from rfl, show a.rm = s.rm from rfl] using
        (⟨rows i hi, rfl⟩ : MatchingCandidateRowValid cutAt s i ∧ readMatchingCandidate cutAt s i = readMatchingCandidate cutAt s i)
    · intro i hi
      change MatchingPairBucketValid k a i ∧ readMatchingPairBucket (k := k) a i = _
      simpa only [outerRefreshPairInput, if_pos internal, Option.elim_none, MatchingPairBucketValid,
        readMatchingPairBucket, aKeep 65, aKeep 66, show a.nm = s.nm from rfl, show a.rm = s.rm from rfl] using
        (⟨buckets i hi, rfl⟩ : MatchingPairBucketValid k s i ∧ readMatchingPairBucket (k := k) s i = readMatchingPairBucket s i)
  · have different : a.nr 26 ≠ a.nr 17 := by
      rw [aSource, aOther]
      exact fun h => internal (Fin.ext h)
    let read := (arithmeticStep readExternalSlackBlock)^[11] a
    let b := {read with pc := 0}
    obtain ⟨fetch, fetchLive, natural, real, _, value, kept⟩ := readExternalSlackBlock_spec a rfl running
    have bKeep (r : ℕ) (safe : r ∉ [6, 10, 16, 17, 19] := by decide) : b.nr r = s.nr r :=
      (kept r (by simp at safe; omega) (by simp at safe; omega)).trans (aKeep r (by simp at safe ⊢; omega))
    have bNat : b.nm = s.nm := natural
    have bReal : b.rm = s.rm := real
    have bTime : b.rr 15 = s.rr 15 := fetch.keeps_cache_real (by decide)
    have bSlack : b.rr 0 = cost u v - effective u - effective v := by
      change read.rr 0 = _
      rw [value, aKeep 20, aKeep 21, aKeep 62, aKeep 15, origin, aNeighbor,
        show a.nm = s.nm from rfl, show a.rm = s.rm from rfl, input.offsets u, input.metric u v,
        input.potentials u, input.potentials v]
    have bLayout : MatchingCacheLayout k b := input.layout.keeps (fun r hr => bKeep r (by simp; omega))
    have bRole : b.nr 19 = role (rep v) := (kept 19 (by decide) (by decide)).trans aLabel
    have bRows (i : ℕ) (hi : i < b.nr 61) : MatchingCandidateRowValid cutAt b i := by
      rw [bKeep 61] at hi
      simpa only [MatchingCandidateRowValid, decodeMatchingDictionaryEvent, bNat, bKeep 54, bKeep 58] using rows i hi
    have bBuckets (i : ℕ) (hi : i < k*k) : MatchingPairBucketValid k b i := by
      simpa only [MatchingPairBucketValid, bNat, bKeep 65] using buckets i hi
    obtain ⟨t, ticks, bound, insert, live, _, _, time, nextRows, nextBuckets⟩ :=
      chooseGrowthCache_rows cutAt (s := b) rfl fetchLive ((bKeep 9).trans one) ((bKeep 14).trans zero)
        bLayout ((bKeep 26).trans source) ((kept 17 (by decide) (by decide)).trans aOther) internal
        ((bKeep 15).trans origin) ((kept 16 (by decide) (by decide)).trans aNeighbor)
        (by intro j; rw [bNat, bKeep 21]; exact input.offsets j)
        (by rw [bKeep 21, bKeep 58]; exact input.offsetsBefore) bRows bBuckets
    have branch := branchOnUnequal_take 26 17 visit (s := a) rfl running different (fetch.append insert)
    have run : BlockRuns refreshGrowthNeighborBlock (5 + (2 + (11 + ticks))) s _ := load.append branch
    have dict : s.nr 58 ≤ s.nr 54 := by have h := input.layout.idsBefore; omega
    have pair : s.nr 58 ≤ s.nr 65 := by
      have h₁ := input.layout.idsBefore
      have h₂ := input.layout.recordsBefore
      omega
    obtain ⟨other, _, _, checked, _, footprint⟩ := refreshGrowthNeighborBlock_memory s entry running one dict pair
    have same := (checked.same_exit run).2
    rw [same] at footprint
    refine ⟨_, _, by omega, run, live, fun r hr => fixed r hr run, time.trans bTime, footprint, ?_, ?_⟩
    · intro i hi
      have within : i < b.nr 61 := by rwa [bKeep 61]
      have readBefore : readMatchingCandidate cutAt b i = readMatchingCandidate cutAt s i := by
        simp only [readMatchingCandidate, decodeMatchingDictionaryEvent, bNat, bReal, bKeep 54, bKeep 58, bKeep 59, bKeep 60]
      change MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i = _
      simpa only [outerRefreshRowInput, if_neg internal, readBefore, bSlack, bRole] using nextRows i within
    · intro i hi
      have readBefore : readMatchingPairBucket (k := k) b i = readMatchingPairBucket (k := k) s i := by
        simp only [readMatchingPairBucket, bNat, bReal, bKeep 65, bKeep 66]
      change MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i = _
      simpa only [outerRefreshPairInput, if_neg internal, readBefore, bSlack, bRole, bTime] using nextBuckets i hi

private theorem insertSlackCandidates_finRange_succ {k : ℕ} {Event : Type*}
    (query : Fin k → Option (DualSlack Event)) (old : Option (DualSlack Event)) (i : ℕ) (inside : i < k) :
    let candidate := query ⟨i, inside⟩
    let prior := insertSlackCandidates (((List.finRange k).take i).filterMap query) old
    insertSlackCandidates (((List.finRange k).take (i+1)).filterMap query) old =
      candidate.elim prior (fun edge => insertSlackCandidate edge prior) := by
  intro candidate prior
  have bound : i < (List.finRange k).length := by simpa using inside
  have selected : (List.finRange k)[i] = (⟨i, inside⟩ : Fin k) := by
    rw [List.getElem_finRange]
    rfl
  rw [List.take_succ_eq_append_getElem bound, selected, List.filterMap_append]
  cases found : query ⟨i, inside⟩ <;> simp [candidate, prior, found, insertSlackCandidates, List.foldl_append]

private structure MatchingRefreshScan {k : ℕ} (cutAt : Fin k → Finset (Fin k)) (s : ArithmeticState)
    (rep : Fin k → Fin k) (role : Fin k → ℕ) (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ)
    (u : Fin k) (seen : ℕ) (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  live : m.halted = false
  cursor : m.nr 25 = seen
  fixed : ∀ r, r ∉ [0, 6, 10, 11, 16, 17, 18, 19, 25] → m.nr r = s.nr r
  time : m.rr 15 = s.rr 15
  input : MatchingRefreshInput m rep role cost effective
  rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt m i ∧
    readMatchingCandidate cutAt m i = insertSlackCandidates (((List.finRange k).take seen).filterMap
      (fun v => outerRefreshRowInput rep role cost effective u v i)) (readMatchingCandidate cutAt s i)
  buckets : ∀ i < k*k, MatchingPairBucketValid k m i ∧
    readMatchingPairBucket (k := k) m i = insertSlackCandidates (((List.finRange k).take seen).filterMap
      (fun v => outerRefreshPairInput rep role cost effective (s.rr 15) u v i)) (readMatchingPairBucket (k := k) s i)

/-- Refresh one outer original against every compact vertex. The returned rows and
buckets are exactly the folds of the corresponding original-edge insertions,
so any previously valid least-entry invariant extends to this source's edges. -/
theorem refreshSelectedOuterVertex_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} {rep : Fin k → Fin k} {role : Fin k → ℕ}
    {cost : Fin k → Fin k → ℝ} {effective : Fin k → ℝ} {u : Fin k}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (input : MatchingRefreshInput s rep role cost effective)
    (origin : s.nr 15 = u.val) (source : s.nr 26 = (rep u).val)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k*k, MatchingPairBucketValid k s i) :
    ∃ t steps, steps ≤ 98 * k + 2 ∧ BlockRuns refreshSelectedOuterVertex steps s t ∧ t.halted = false ∧
      (∀ r, r ∉ [0, 6, 10, 11, 16, 17, 18, 19, 25] → t.nr r = s.nr r) ∧ t.rr 15 = s.rr 15 ∧
      MatchingRefreshInput t rep role cost effective ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧
        readMatchingCandidate cutAt t i = insertSlackCandidates ((List.finRange k).filterMap
          (fun v => outerRefreshRowInput rep role cost effective u v i)) (readMatchingCandidate cutAt s i)) ∧
      (∀ i < k*k, MatchingPairBucketValid k t i ∧
        readMatchingPairBucket (k := k) t i = insertSlackCandidates ((List.finRange k).filterMap
          (fun v => outerRefreshPairInput rep role cost effective (s.rr 15) u v i)) (readMatchingPairBucket (k := k) s i)) := by
  let inv := MatchingRefreshScan cutAt s rep role cost effective u
  let seeded := {s with pc := 0, nr := Function.update s.nr 25 0}
  have seedKeep (r : ℕ) (away : r ≠ 25) : seeded.nr r = s.nr r := Function.update_of_ne away _ _
  have rawInput : MatchingRefreshInput seeded rep role cost effective :=
    input.keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun r listed => seedKeep r (by simp [matchingRefreshTableRegisters] at listed; omega))
  have initial : inv 0 seeded := by
    refine ⟨rfl, running, by simp [seeded], ?_, rfl, rawInput, ?_, ?_⟩
    · intro r safe
      exact seedKeep r (by simp at safe; omega)
    · intro i hi
      have validity : MatchingCandidateRowValid cutAt seeded i := by
        simp only [MatchingCandidateRowValid, decodeMatchingDictionaryEvent, seedKeep 54 (by decide), seedKeep 58 (by decide),
          show seeded.nm = s.nm from rfl]
        exact rows i hi
      refine ⟨validity, ?_⟩
      simp only [readMatchingCandidate, decodeMatchingDictionaryEvent, seedKeep 54 (by decide), seedKeep 58 (by decide),
        seedKeep 59 (by decide), seedKeep 60 (by decide), show seeded.nm = s.nm from rfl,
        show seeded.rm = s.rm from rfl, List.take_zero, List.filterMap_nil, insertSlackCandidates, List.foldl_nil]
    · intro i hi
      have validity : MatchingPairBucketValid k seeded i := by
        simpa only [MatchingPairBucketValid, seedKeep 65 (by decide), show seeded.nm = s.nm from rfl] using buckets i hi
      refine ⟨validity, ?_⟩
      simp only [readMatchingPairBucket, seedKeep 65 (by decide), seedKeep 66 (by decide), show seeded.nm = s.nm from rfl,
        show seeded.rm = s.rm from rfl, List.take_zero, List.filterMap_nil, insertSlackCandidates, List.foldl_nil]
  have next (i : ℕ) (inside : i < k) (m : ArithmeticState) (h : inv i m) :
      ∃ t steps, steps ≤ 95 ∧ BlockRuns refreshGrowthNeighborBlock steps m t ∧ t.halted = false ∧
        inv (i+1) {t with pc := 0, nr := Function.update t.nr 25 (t.nr 25 + t.nr 9)} := by
    let v : Fin k := ⟨i, inside⟩
    have unit : m.nr 9 = 1 := (h.fixed 9 (by decide)).trans one
    have atZero : m.nr 14 = 0 := (h.fixed 14 (by decide)).trans zero
    have first : m.nr 15 = u.val := (h.fixed 15 (by decide)).trans origin
    have fromBlock : m.nr 26 = (rep u).val := (h.fixed 26 (by decide)).trans source
    have mRows (p : ℕ) (hi : p < m.nr 61) : MatchingCandidateRowValid cutAt m p :=
      (h.rows p (by rwa [h.fixed 61 (by decide)] at hi)).1
    obtain ⟨t, steps, short, run, live, keep, clock, memory, changedRows, changedBuckets⟩ :=
      refreshGrowthNeighborBlock_rows cutAt (v := v) h.entry h.live unit atZero h.input first h.cursor fromBlock
        mRows (fun j valid => (h.buckets j valid).1)
    let advanced := {t with pc := 0, nr := Function.update t.nr 25 (t.nr 25 + t.nr 9)}
    have nextInput : MatchingRefreshInput advanced rep role cost effective := h.input.keeps ⟨memory.natural, memory.real⟩
      (fun r listed => (Function.update_of_ne (by simp [matchingRefreshTableRegisters] at listed; omega) _ _).trans
        (keep r (by simp [matchingRefreshTableRegisters] at listed ⊢; omega)))
    refine ⟨t, steps, short, run, live, rfl, live, ?_, ?_, clock.trans h.time, nextInput, ?_, ?_⟩
    · simp [keep 25 (by decide), keep 9 (by decide), unit, h.cursor]
    · intro r safe
      have away : r ≠ 25 := by simp at safe; omega
      exact (Function.update_of_ne away _ _).trans ((keep r (by simp at safe ⊢; omega)).trans (h.fixed r safe))
    · intro row hi
      have within : row < m.nr 61 := by rwa [h.fixed 61 (by decide)]
      have keepRows : MatchingCandidateRowValid cutAt advanced row = MatchingCandidateRowValid cutAt t row := by
        simp only [MatchingCandidateRowValid, decodeMatchingDictionaryEvent, advanced, Function.update_of_ne (by decide : 58 ≠ 25),
          Function.update_of_ne (by decide : 54 ≠ 25)]
      have keepRead : readMatchingCandidate cutAt advanced row = readMatchingCandidate cutAt t row := by
        simp only [readMatchingCandidate, decodeMatchingDictionaryEvent, advanced, Function.update_of_ne (by decide : 58 ≠ 25),
          Function.update_of_ne (by decide : 54 ≠ 25), Function.update_of_ne (by decide : 59 ≠ 25), Function.update_of_ne (by decide : 60 ≠ 25)]
      change MatchingCandidateRowValid cutAt advanced row ∧ readMatchingCandidate cutAt advanced row = _
      rw [keepRows, keepRead]
      refine ⟨(changedRows row within).1, ?_⟩
      rw [(changedRows row within).2, (h.rows row hi).2, insertSlackCandidates_finRange_succ _ _ i inside]
    · intro slot hi
      have keepBuckets : MatchingPairBucketValid k advanced slot = MatchingPairBucketValid k t slot := by
        simp only [MatchingPairBucketValid, advanced, Function.update_of_ne (by decide : 65 ≠ 25)]
      have keepRead : readMatchingPairBucket (k := k) advanced slot = readMatchingPairBucket (k := k) t slot := by
        simp only [readMatchingPairBucket, advanced, Function.update_of_ne (by decide : 65 ≠ 25),
          Function.update_of_ne (by decide : 66 ≠ 25)]
      change MatchingPairBucketValid k advanced slot ∧ readMatchingPairBucket (k := k) advanced slot = _
      rw [keepBuckets, keepRead]
      refine ⟨(changedBuckets slot hi).1, ?_⟩
      rw [(changedBuckets slot hi).2, (h.buckets slot hi).2, h.time, insertSlackCandidates_finRange_succ _ _ i inside]
  obtain ⟨finished, steps, done, budget, complete⟩ := countedLoopFromZero_bounded 9 25 55 k 95
    refreshGrowthNeighborBlock inv (s := s) entry running initial
    (fun _ _ h => ⟨h.entry, h.live, h.cursor, h.input.layout.dimension⟩) next
  have all : (List.finRange k).take k = List.finRange k := List.take_of_length_le (by simp)
  refine ⟨_, steps, by omega, complete, done.live, done.fixed, done.time, ?_, ?_, ?_⟩
  · apply done.input.keeps
    · exact ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    · intro r _
      rfl
  · intro i hi
    change MatchingCandidateRowValid cutAt finished i ∧ readMatchingCandidate cutAt finished i = _
    simpa only [all] using done.rows i hi
  · intro i hi
    change MatchingPairBucketValid k finished i ∧ readMatchingPairBucket (k := k) finished i = _
    simpa only [all] using done.buckets i hi

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

/-- The forest's parent-edge witness array lies between the header tables
and the allocated cycle records. Thus writing parent witnesses cannot change
any live tree's stored encoding. -/
theorem MatchingRegistryView.witnessFootprint {k stage : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {original s : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} (registry : MatchingRegistryView dual)
    (storage : MatchingStageStorage k original s) (order : MatchingCycleRecordOrder s)
    (stageBudget : MatchingRegistryBudget k stage s (matchingStageCountsFromRAM k s (s.nr 39)))
    (searching : stage < k/2) (v : Fin k) :
    (registry.trees.tree v).readable s.nm (s.nr 77) (s.nr 78)
      (fun a => (a < s.nr 90 ∨ s.nr 90+2*k ≤ a) ∧ s.nr 65+2*(k*k) ≤ a) := by
  let tree := registry.trees.tree v
  have visit (sub : MatchingMemberTree)
      (subset : ∀ n ∈ sub.registryIds, n ∈ registry.trees.registryIds)
      (high : sub.readable s.nm (s.nr 77) (s.nr 78) (fun a => s.nr 65+2*(k*k) ≤ a)) :
      sub.readable s.nm (s.nr 77) (s.nr 78)
        (fun a => (a < s.nr 90 ∨ s.nr 90+2*k ≤ a) ∧ s.nr 65+2*(k*k) ≤ a) := by
    induction sub with
    | nil => trivial
    | leaf _ rest ih => exact ih subset high
    | blossom r n child rest cih rih =>
      have present := subset n (by simp [MatchingMemberTree.registryIds])
      obtain ⟨B, live, id⟩ := (registry.keys n).mp present
      have positive : 0 < n := Nat.pos_of_ne_zero (id ▸ dual.nodeNonzero B live)
      have small : n < s.nr 76 := id ▸ registry.allocated B live
      have capacity := stageBudget.allocated_fits searching small
      obtain ⟨ha, hb, hc, hd, he⟩ := high
      have headers := storage.lengths
      have traces := storage.traceLeft
      have right := storage.traceRight
      have marks := storage.traceMarks
      have witness := storage.witnesses
      refine ⟨⟨.inl (by omega), ha⟩, ⟨.inl (by omega), hb⟩, ?_,
        cih (fun i hi => subset i (by simp [MatchingMemberTree.registryIds,hi])) hd,
        rih (fun i hi => subset i (by simp [MatchingMemberTree.registryIds,hi])) he⟩
      intro i hi w hw
      have low := (order.bounded n positive small).1
      unfold matchingRebaseScratchEnd matchingCycleRecordStart at low
      have records := storage.records
      have promoted := storage.promotion
      have mask := storage.mask
      have map := storage.memberMap
      have stack := storage.memberStack
      exact ⟨.inr (by omega), hc i hi w hw⟩
  apply visit tree _ (registry.readable v)
  intro n inside
  exact List.mem_flatMap.mpr ⟨v, List.mem_finRange v, inside⟩

/-- Reconstruct a registry after witness stores, using the previous cycle
trees and their actual allocated rows. -/
def MatchingRegistryView.afterWitnesses {k stage : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {before after : AlternatingForestState (Fin k)} {original s t : ArithmeticState}
    {old : MatchingSearchDualMemory part before s} {new : MatchingSearchDualMemory part after t}
    (registry : MatchingRegistryView old) (storage : MatchingStageStorage k original s)
    (order : MatchingCycleRecordOrder s) (budget : MatchingRegistryBudget k stage s (matchingStageCountsFromRAM k s (s.nr 39)))
    (searching : stage < k/2) (ids : new.node = old.node)
    (headers : t.nr 77 = s.nr 77) (lengths : t.nr 78 = s.nr 78) (cursor : t.nr 76 = s.nr 76)
    (pointers : t.nr 65 = s.nr 65) (top : ∀ v : Fin k, blossomNodeAt t v = blossomNodeAt s v)
    (natural : ∀ a, s.nr 65+2*(k*k) ≤ a → a < s.nr 90 ∨ s.nr 90+2*k ≤ a → t.nm a = s.nm a) :
    MatchingRegistryView new := by
  have preserved (a : ℕ) (h : (a < s.nr 90 ∨ s.nr 90+2*k ≤ a) ∧ s.nr 65+2*(k*k) ≤ a) := natural a h.2 h.1
  let trees : MatchingTopMemberTrees k t := {
    tree := registry.trees.tree
    roots v := by
      change (registry.trees.tree v).rootKeys = (if blossomNodeAt t v = 0 then [] else [MatchingMemberTree.rootKey v.val (blossomNodeAt t v)])
      rw [top]
      exact registry.trees.roots v
    proper := registry.trees.proper
    encoded v := by
      rw [headers, lengths]
      exact MatchingMemberTree.encoded_congr (registry.trees.encoded v)
        (registry.witnessFootprint storage order budget searching v) preserved }
  refine ⟨trees, ?_, registry.unique, ?_, ?_, registry.nontrivial, registry.laminar, registry.nested⟩
  · intro v
    rw [headers, lengths, pointers]
    have move (tree : MatchingMemberTree)
        (h : tree.readable s.nm (s.nr 77) (s.nr 78)
          (fun a => (a < s.nr 90 ∨ s.nr 90+2*k ≤ a) ∧ s.nr 65+2*(k*k) ≤ a)) :
        tree.readable t.nm (s.nr 77) (s.nr 78) (fun a => s.nr 65+2*(k*k) ≤ a) := by
      induction tree with
      | nil => trivial
      | leaf _ rest ih => exact ih h
      | blossom _ n child rest ci ri =>
        obtain ⟨first, last, rows, c, r⟩ := h
        refine ⟨first.2, last.2, ?_, ci c, ri r⟩
        intro i hi w hw
        rw [preserved _ first]
        exact (rows i hi w hw).2
    exact move _ (registry.witnessFootprint storage order budget searching v)
  · intro n; rw [ids]; exact registry.keys n
  · intro B h; rw [ids, cursor]; exact registry.allocated B h


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRegistryWitnessFrame

/-! matching/MatchingGrowWitnessProof.lean -/
section RppSource_MatchingGrowWitnessProof
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

def orientedMatchingOriginalGrowthEvent (s : ArithmeticState) (target : ℕ) : ℕ × ℕ :=
  let e := matchingOriginalGrowthEvent s
  if s.nm (s.nr 57 + e.1) = target then e.swap else e

/-- The executable grow handler preserves the selected original edge until the
new inner and outer parent entries can be written in their proper orientations. -/
theorem matchingGrowHandlerWithWitnesses_runs {n : ℕ} {forest : AlternatingForestState (Fin n)}
    {mate : Fin n → Option (Fin n)} {tight : Fin n → Fin n → Prop} (valid : forest.valid mate tight)
    (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (size : s.nr 55 = n) (table : AlternatingForestMemory forest (s.nr 51) s.nm)
    (parentBase : s.nr 52 = s.nr 51 + n) (depthBase : s.nr 53 = s.nr 51 + n + n)
    (repAfter : s.nr 53 + n ≤ s.nr 57) (repBefore : s.nr 57 + n ≤ s.nr 58)
    (dictionary : s.nr 58 ≤ s.nr 54) (buckets : s.nr 58 ≤ s.nr 65) (witnessAfter : s.nr 58 ≤ s.nr 90)
    {source target peer : Fin n} {parent : Option (Fin n)}
    (sourceIndex : matchingChosenGrowSource s = source.val)
    (targetIndex : matchingChosenGrowTarget s = target.val) (peerIndex : s.nm (s.nr 50 + target.val) = peer.val)
    (sourceOuter : forest.role source = .outer parent) (targetDormant : forest.role target = .unlabelled)
    (peerDormant : forest.role peer = .unlabelled) (distinct : target ≠ peer)
    (mateTarget : mate target = some peer) (matePeer : mate peer = some target)
    (incoming : tight source target) (matched : tight target peer)
    (leftValid : (matchingOriginalGrowthEvent s).1 < n) :
    ∃ t ticks, ticks ≤ 56 * n + (n * 98 + 2) * matchingNewOuterCard s peer.val + 105 ∧
      BlockRuns matchingGrowHandlerWithWitnesses ticks s t ∧ t.halted = false ∧ t.nr 1 = 0 ∧
      AlternatingForestMemory (forest.grow source target peer) (s.nr 51) t.nm ∧
      (forest.grow source target peer).valid mate tight ∧
      matchingForestWitnessAt t.nm (s.nr 90) target.val = orientedMatchingOriginalGrowthEvent s target.val ∧
      matchingForestWitnessAt t.nm (s.nr 90) peer.val = (target.val, peer.val) ∧
      (∀ a, a < s.nr 58 → (a < s.nr 51 ∨ s.nr 53 + n ≤ a) → t.nm a = s.nm a) ∧
      (∀ r ≥ 29, t.nr r = s.nr r) ∧
      t.nr 3 = s.nr 58 ∧ t.nr 4 = s.nr 59 ∧ t.nr 5 = s.nr 60 ∧ t.nr 8 = s.nr 61 := by
  obtain ⟨stored, save, saveLive, edge, saveNat, _, _, saved⟩ := saveMatchingGrowthOriginalEdge_spec s entry running one
  let a := {stored with pc := 0}
  have frame (r : ℕ) (safe : r ∉ [0, 6, 22, 23] := by decide) : a.nr r = s.nr r := saved r safe
  have aNat : a.nm = s.nm := saveNat
  have aOne : a.nr 9 = 1 := (frame 9).trans one
  have aTable : AlternatingForestMemory forest (a.nr 51) a.nm := by simpa only [frame 51, aNat] using table
  have sameEnds : matchingChosenLeftBlock a = matchingChosenLeftBlock s ∧ matchingChosenRightBlock a = matchingChosenRightBlock s := by
    simp [matchingChosenLeftBlock, matchingChosenRightBlock, matchingChosenEdgeAddress, frame 1, frame 54, frame 57, aNat]
  have aSource : matchingChosenGrowSource a = source.val := by
    simpa only [matchingChosenGrowSource, sameEnds.1, sameEnds.2, frame 51, aNat] using sourceIndex
  have aTarget : matchingChosenGrowTarget a = target.val := by
    simpa only [matchingChosenGrowTarget, sameEnds.1, sameEnds.2, frame 51, aNat] using targetIndex
  obtain ⟨grown, growTicks, growBudget, grow, live, id, forestEncoding, forestValid, growNatural, fixed, peerAt, targetAt,
    keepsOne, idAt, slackAt, rateAt, countAt⟩ := matchingGrowHandlerBlock_runs valid a rfl saveLive aOne
      ((frame 55).trans size) aTable (by simpa only [frame 52, frame 51] using parentBase)
      (by simpa only [frame 53, frame 51] using depthBase) (by simpa only [frame 53, frame 57] using repAfter)
      (by simpa only [frame 57, frame 58] using repBefore) (by simpa only [frame 58, frame 54] using dictionary)
      (by simpa only [frame 58, frame 65] using buckets) aSource aTarget
      (by simpa only [frame 50, aNat] using peerIndex) sourceOuter targetDormant peerDormant distinct mateTarget matePeer incoming matched
  let b := {grown with pc := 0}
  have high (r : ℕ) (large : 29 ≤ r) : b.nr r = s.nr r :=
    (fixed r (.inl large)).trans (frame r (by simp; omega))
  have storedEdge : (b.nr 22, b.nr 23) = matchingOriginalGrowthEvent s := by
    change (grown.nr 22, grown.nr 23) = _
    rw [fixed 22 (by decide), fixed 23 (by decide)]
    exact edge
  have left : b.nr 22 = (matchingOriginalGrowthEvent s).1 := congrArg Prod.fst storedEdge
  have right : b.nr 23 = (matchingOriginalGrowthEvent s).2 := congrArg Prod.snd storedEdge
  have preservedRead : b.nm (s.nr 57 + (matchingOriginalGrowthEvent s).1) =
      s.nm (s.nr 57 + (matchingOriginalGrowthEvent s).1) := by
    exact (growNatural _ (by rw [frame 58]; omega) (.inr (by rw [frame 53]; omega))).trans (congrFun aNat _)
  have orient : orientedMatchingGrowthEdge b = orientedMatchingOriginalGrowthEvent s target.val := by
    have bTarget : b.nr 28 = target.val := targetAt
    simp only [orientedMatchingGrowthEdge, orientedMatchingOriginalGrowthEvent, left, right, high 57 (by decide),
      bTarget, preservedRead, Prod.swap]
  obtain ⟨t, storeTicks, storeBudget, store, ready, wrote, _, _⟩ := storeOrientedMatchingGrowthWitnesses_spec b rfl live keepsOne
  have final : BlockRuns matchingGrowHandlerWithWitnesses (6 + (growTicks + storeTicks)) s _ := save.append (grow.append store)
  have storedMemory : t.nm = writeMatchingForestWitness
      (writeMatchingForestWitness b.nm (s.nr 90) target.val (orientedMatchingOriginalGrowthEvent s target.val))
      (s.nr 90) peer.val (target.val, peer.val) := by
    have bTarget : b.nr 28 = target.val := targetAt
    have bPeer : b.nr 26 = peer.val := peerAt
    simpa only [high 90 (by decide), bTarget, bPeer, orient] using wrote
  have unchangedNatural (addr : ℕ) (earlier : addr < s.nr 90) : t.nm addr = b.nm addr := by
    simp (disch := omega) [storedMemory, writeMatchingForestWitness, forestWitnessAddress, Function.update_of_ne]
  have storedRegister (r : ℕ) (safe : r ∉ [0, 6, 10, 14, 22, 23]) : t.nr r = b.nr r := by
    rw [← store.run]
    exact arithmeticRun_keeps_from_destination_list [0, 6, 10, 14, 22, 23] (by decide) safe b storeTicks
  refine ⟨_, _, ?_, final, ready, (storedRegister 1 (by decide)).trans id, ?_, forestValid, ?_, ?_, ?_, ?_,
    (storedRegister 3 (by decide)).trans (idAt.trans (frame 58)),
    (storedRegister 4 (by decide)).trans (slackAt.trans (frame 59)),
    (storedRegister 5 (by decide)).trans (rateAt.trans (frame 60)),
    (storedRegister 8 (by decide)).trans (countAt.trans (frame 61))⟩
  · have cardEq : matchingNewOuterCard a peer.val = matchingNewOuterCard s peer.val := by
      simp [matchingNewOuterCard, frame 55, frame 57, aNat]
    rw [cardEq] at growBudget
    omega
  · rw [frame 51] at forestEncoding
    intro v
    have bounded := v.isLt
    obtain ⟨role, parentCode, level⟩ := forestEncoding v
    exact ⟨(unchangedNatural _ (by omega)).trans role, (unchangedNatural _ (by omega)).trans parentCode,
      (unchangedNatural _ (by omega)).trans level⟩
  · change matchingForestWitnessAt t.nm _ _ = _
    rw [storedMemory, matchingForestWitnessAt_write_other _ _ _ _ _ (fun equal => distinct (Fin.ext equal)),
      matchingForestWitnessAt_write_same]
  · change matchingForestWitnessAt t.nm _ _ = _
    rw [storedMemory, matchingForestWitnessAt_write_same]
  · intro addr before safe
    exact (unchangedNatural addr (before.trans_le witnessAfter)).trans
      ((growNatural addr (by rwa [frame 58]) (by simpa only [frame 51, frame 53] using safe)).trans (congrFun aNat addr))
  · intro r large
    exact (storedRegister r (by simp; omega)).trans (high r large)



end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowWitnessProof

/-! matching/MatchingGrowthSelection.lean -/
section RppSource_MatchingGrowthSelection
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- A growth event reads an outer representative and the two ends of a dormant
matched pair. The new forest still represents the same primal matching. -/
structure MatchingGrowthSelection {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (s : ArithmeticState) (edge : Sym2 (Fin k)) where
  source : Fin k
  target : Fin k
  peer : Fin k
  parent : Option (Fin k)
  sourceOuter : forest.role source = .outer parent
  targetDormant : forest.role target = .unlabelled
  targetActive : target ∈ part.activeRepresentatives
  peerDormant : forest.role peer = .unlabelled
  sourceWord : matchingChosenGrowSource s = source.val
  targetWord : matchingChosenGrowTarget s = target.val
  peerWord : s.nm (s.nr 50 + target.val) = peer.val
  distinct : target ≠ peer
  paired : state.partialMate target = some peer
  reversePaired : state.partialMate peer = some target
  incoming : part.tightBetween source target
  matched : part.tightBetween target peer
  leftValid : (matchingOriginalGrowthEvent s).1 < k
  direction : ∃ a b : Fin k, edge = s(a, b) ∧
    orientedMatchingOriginalGrowthEvent s target.val = (a.val, b.val) ∧
    part.representative a = source ∧ part.representative b = target
  next : CompactMatchingSearchForest part (forest.grow source target peer) state.partialMate part.tightBetween

/-- A typed, tight growth selection provides all operands consumed by the
actual handler, including the orientation of the original crossing edge. -/
theorem matchingGrowthSelection_of_class {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {original s : ArithmeticState} {edge : Sym2 (Fin k)}
    (positive : 0 < k) (cutAt : Fin k → Finset (Fin k)) (top : CompactTopMatching part)
    (primal : CompactMatchingPrimalDualMemory state original s)
    (search : CompactMatchingSearchForest part forest state.partialMate part.tightBetween)
    (roles : AlternatingForestMemory forest (s.nr 51) s.nm)
    (reps : ∀ v : Fin k, s.nm (s.nr 57 + v.val) = (part.representative v).val)
    (classified : MatchingEventClassView part.blocks forest (part.representativeOf positive) cutAt s (.edge edge))
    (growth : matchingEventClass s = 0)
    (tight : oddCutDualEdgeValue state.cuts state.potential state.cutDual edge = edgeCost cost edge) :
    Nonempty (MatchingGrowthSelection part forest s edge) := by
  have roots : AlternatingStageRoots forest part.activeRepresentatives state.partialMate part.tightBetween := by
    refine ⟨search.valid, ?_, top.resetForest.1.partners⟩
    intro v active free
    have excluded : v ∉ state.covered := by
      intro inMatching
      simp [CompactMatchingPrimalDual.partialMate, inMatching] at free
    simpa only [(part.mem_activeRepresentatives v).mp active] using search.exposed v excluded
  obtain ⟨u, v, ports, shape, _, leftCode, rightCode, choice⟩ := classified
  simp only [part.representativeOf_block] at leftCode rightCode choice
  have left : matchingChosenLeftBlock s = (part.representative u).val := leftCode
  have right : matchingChosenRightBlock s = (part.representative v).val := rightCode
  have leftValid : (matchingOriginalGrowthEvent s).1 < k := by rw [ports]; exact u.isLt
  rcases choice with ⟨wrong, _⟩ | ⟨_, oriented⟩
  · omega
  have prepare {a b : Fin k} {p : Option (Fin k)} (aOuter : forest.role (part.representative a) = .outer p)
      (bDormant : forest.role (part.representative b) = .unlabelled) (orientation : edge = s(a, b))
      (source : matchingChosenGrowSource s = (part.representative a).val)
      (target : matchingChosenGrowTarget s = (part.representative b).val)
      (event : orientedMatchingOriginalGrowthEvent s (part.representative b).val = (a.val, b.val)) :
      Nonempty (MatchingGrowthSelection part forest s edge) := by
    let src := part.representative a
    let dest := part.representative b
    have active : dest ∈ part.activeRepresentatives :=
      (part.mem_activeRepresentatives dest).mpr (part.representative_idem b)
    obtain ⟨peer, endPair⟩ : ∃ peer, state.partialMate dest = some peer := by
      cases found : state.partialMate dest with
      | some peer => exact ⟨peer, rfl⟩
      | none => cases (bDormant.symm.trans (roots.exposedRoots dest active found))
    obtain ⟨_, distinct, reverse, matched⟩ := roots.partners dest active peer endPair
    have dormant : forest.role peer = .unlabelled := by
      have rate := AlternatingForestState.mate_dualDirection_add_eq_zero search.valid endPair reverse
      change (forest.role dest).dualDirection + (forest.role peer).dualDirection = 0 at rate
      rw [show forest.role dest = .unlabelled from bDormant] at rate
      cases label : forest.role peer with
      | unlabelled => rfl
      | outer p => norm_num [label, AlternatingForestRole.dualDirection] at rate
      | inner p => norm_num [label, AlternatingForestRole.dualDirection] at rate
    have edgeTight : part.tightBetween src dest := ⟨a, b, rfl, rfl, orientation ▸ tight⟩
    have installed := AlternatingForestState.grow_valid search.valid aOuter bDormant dormant distinct endPair reverse edgeTight matched
    have next : CompactMatchingSearchForest part (forest.grow src dest peer) state.partialMate part.tightBetween := by
      refine ⟨installed, search.crossing, ?_⟩
      intro x exposed
      have stays := search.exposed x exposed
      have notDest : part.representative x ≠ dest := fun eq => by
        change forest.role dest = .unlabelled at bDormant
        cases stays.symm.trans (eq.symm ▸ bDormant)
      have notPeer : part.representative x ≠ peer := fun eq => by cases stays.symm.trans (eq.symm ▸ dormant)
      simp [AlternatingForestState.grow, notDest, notPeer, stays]
    have peerWord : s.nm (s.nr 50 + dest.val) = peer.val := by simp only [primal.partialMate_word dest, endPair, Option.elim_some]
    exact ⟨⟨src, dest, peer, p, aOuter, bDormant, active, dormant, source, target, peerWord, distinct, endPair,
      reverse, edgeTight, matched, leftValid, ⟨a, b, orientation, event, rfl, rfl⟩, next⟩⟩
  rcases oriented with ⟨p, outer, idle⟩ | ⟨p, idle, outer⟩
  · have readOuter := (roles (part.representative u)).1
    rw [outer] at readOuter
    have noSwap : s.nm (s.nr 57 + u.val) ≠ (part.representative v).val := by
      rw [reps]
      intro same
      have equal : part.representative u = part.representative v := Fin.ext same
      cases (outer.symm.trans (equal.symm ▸ idle))
    apply prepare outer idle shape
    · simp [matchingChosenGrowSource, left, right, readOuter, alternatingRoleCode]
    · simp [matchingChosenGrowTarget, left, right, readOuter, alternatingRoleCode]
    · simp [orientedMatchingOriginalGrowthEvent, ports, noSwap]
  · have readIdle := (roles (part.representative u)).1
    rw [idle] at readIdle
    apply prepare outer idle (shape.trans Sym2.eq_swap)
    · simp [matchingChosenGrowSource, left, right, readIdle, alternatingRoleCode]
    · simp [matchingChosenGrowTarget, left, right, readIdle, alternatingRoleCode]
    · simp [orientedMatchingOriginalGrowthEvent, ports, reps, Prod.swap]

theorem matchingNewOuterCard_eq_block {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {s : ArithmeticState} (part : CompactMatchingPartition state)
    (size : s.nr 55 = k) (reps : ∀ v : Fin k, s.nm (s.nr 57 + v.val) = (part.representative v).val)
    {peer : Fin k} (fixed : part.representative peer = peer) :
    matchingNewOuterCard s peer.val = (part.blocks.block peer).card := by
  let promoted := (List.range k).filter fun v => decide (s.nm (s.nr 57 + v) = peer.val)
  let index : Fin k ↪ ℕ := ⟨Fin.val, fun _ _ same => Fin.ext same⟩
  have key (v : Fin k) : s.nm (s.nr 57 + v.val) = peer.val ↔ v ∈ part.blocks.block peer := by
    rw [reps]
    constructor
    · intro same
      have equation : part.representative v = part.representative peer := (Fin.ext same).trans fixed.symm
      exact (part.same_block.mp equation) ▸ part.blocks.self_mem v (Finset.mem_univ v)
    · intro inside
      have same := part.blocks.same_of_mem (Finset.mem_univ peer) inside
      exact congrArg Fin.val ((part.same_block.mpr same).trans fixed)
  have exactSet : promoted.toFinset = (part.blocks.block peer).map index := by
    ext i
    simp only [promoted, List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq, Finset.mem_map]
    constructor
    · rintro ⟨hi, label⟩
      exact ⟨⟨i, hi⟩, (key ⟨i, hi⟩).mp label, rfl⟩
    · rintro ⟨v, member, hv⟩
      change v.val = i at hv
      subst i
      exact ⟨v.isLt, (key v).mpr member⟩
  unfold matchingNewOuterCard
  rw [size]
  change promoted.length = _
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _), exactSet, Finset.card_map]

/-- Run the selected grow arm within one linear scan per charged vertex. Its
two parent witnesses agree with the newly marked pair and the chosen edge.
The bound reserves 28 instructions for classification and four for dispatch. -/
theorem MatchingGrowthSelection.run {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState} {edge : Sym2 (Fin k)}
    (choice : MatchingGrowthSelection part forest s edge) (top : CompactTopMatching part)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (before : CompactMatchingSearchForest part forest state.partialMate part.tightBetween)
    (layout : MatchingWarmLayout s k) (encoding : AlternatingForestMemory forest (s.nr 51) s.nm)
    (reps : ∀ v : Fin k, s.nm (s.nr 57 + v.val) = (part.representative v).val) (witnessAfter : s.nr 58 ≤ s.nr 90) :
    ∃ t ticks, ticks + 32 ≤ 1024 * (k + 1) * (1 + (part.blocks.block choice.peer).card) ∧
      BlockRuns matchingGrowHandlerWithWitnesses ticks s t ∧ t.halted = false ∧ t.nr 1 = 0 ∧
      AlternatingForestMemory (forest.grow choice.source choice.target choice.peer) (s.nr 51) t.nm ∧
      matchingForestWitnessAt t.nm (s.nr 90) choice.target.val = orientedMatchingOriginalGrowthEvent s choice.target.val ∧
      matchingForestWitnessAt t.nm (s.nr 90) choice.peer.val = (choice.target.val, choice.peer.val) ∧
      (∀ a, a < s.nr 58 → (a < s.nr 51 ∨ s.nr 53 + k ≤ a) → t.nm a = s.nm a) ∧
      (∀ r ≥ 29, t.nr r = s.nr r) ∧
      t.nr 3 = s.nr 58 ∧ t.nr 4 = s.nr 59 ∧ t.nr 5 = s.nr 60 ∧ t.nr 8 = s.nr 61 := by
  have peerFixed : part.representative choice.peer = choice.peer :=
    (part.mem_activeRepresentatives choice.peer).mp (top.resetForest.1.partners _ choice.targetActive _ choice.paired).1
  have rose : s.nr 53 + k ≤ s.nr 57 := by
    rw [layout.depths]
    have room := layout.representativesAfter
    omega
  obtain ⟨t, ticks, bound, ran, live, id, next, _, inner, outer, natural, fixed, ids, slacks, rates, count⟩ :=
    matchingGrowHandlerWithWitnesses_runs before.valid s entry running one layout.size encoding layout.parents layout.depths
      rose layout.candidatesAfter layout.dictionaryAfter layout.pairsAfter witnessAfter choice.sourceWord choice.targetWord
      choice.peerWord choice.sourceOuter choice.targetDormant choice.peerDormant choice.distinct choice.paired
      choice.reversePaired choice.incoming choice.matched choice.leftValid
  rw [matchingNewOuterCard_eq_block part layout.size reps peerFixed] at bound
  let fresh := (part.blocks.block choice.peer).card
  have budget : ticks + 32 ≤ 1024 * (k + 1) * (1 + fresh) := by
    have row : k * 98 + 2 ≤ 1024 * (k + 1) := by omega
    have scans := Nat.mul_le_mul_right fresh row
    rw [Nat.mul_add, Nat.mul_one]
    change ticks + 32 ≤ 1024 * (k + 1) + (1024 * (k + 1)) * fresh
    have step : ticks ≤ 56 * k + (k * 98 + 2) * fresh + 105 := bound
    omega
  exact ⟨t, ticks, budget, ran, live, id, next, inner, outer, natural, fixed, ids, slacks, rates, count⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowthSelection

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

/-- The two new parent links and every surviving parent link have the
prescribed original witness after growth. -/
theorem MatchingGrowthSelection.forestLinks {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s t : ArithmeticState} {edge : Sym2 (Fin k)}
    (chosen : MatchingGrowthSelection part forest s edge) (top : CompactTopMatching part)
    (links : MatchingForestLinkMemory part forest s) (witnesses : MatchingForestOriginalWitnesses part forest s)
    (tight : oddCutDualEdgeValue state.cuts state.potential state.cutDual edge = edgeCost cost edge)
    (inner : matchingForestWitnessAt t.nm (t.nr 90) chosen.target.val = orientedMatchingOriginalGrowthEvent s chosen.target.val)
    (outer : matchingForestWitnessAt t.nm (t.nr 90) chosen.peer.val = (chosen.target.val, chosen.peer.val))
    (keep : ∀ v : Fin k, v ≠ chosen.target → v ≠ chosen.peer →
      matchingForestWitnessAt t.nm (t.nr 90) v.val = matchingForestWitnessAt s.nm (s.nr 90) v.val) :
    let next := forest.grow chosen.source chosen.target chosen.peer
    MatchingForestLinkMemory part next t ∧ MatchingForestOriginalWitnesses part next t := by
  intro next
  have targetFixed := (part.mem_activeRepresentatives _).mp chosen.targetActive
  have paired := state.partialMate_some_iff.mp chosen.paired
  have peerFixed := (top.crossing_endpoints paired (top.matchedBase targetFixed chosen.paired)).2
  have targetRole : next.role chosen.target = .inner chosen.source := by
    simp [next, AlternatingForestState.grow]
  have peerRole : next.role chosen.peer = .outer (some chosen.target) := by
    simp [next, AlternatingForestState.grow, Ne.symm chosen.distinct]
  have otherRole (v : Fin k) (a : v ≠ chosen.target) (b : v ≠ chosen.peer) : next.role v = forest.role v := by
    simp [next, AlternatingForestState.grow, a, b]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro v away
    have a : v ≠ chosen.target := fun e => away (e ▸ targetFixed)
    have b : v ≠ chosen.peer := fun e => away (e ▸ peerFixed)
    exact (otherRole v a b).trans (links.inactive v away)
  · intro v p kind
    by_cases a : v = chosen.target
    · subst v
      rw [targetRole] at kind
      cases kind
    by_cases b : v = chosen.peer
    · subst v
      rw [peerRole] at kind
      cases kind
      exact outer
    exact (keep v a b).trans (links.matched ((otherRole v a b).symm.trans kind))
  · intro v p link
    by_cases a : v = chosen.target
    · subst v
      have eq : chosen.source = p := Option.some.inj (by simpa only [targetRole, AlternatingForestRole.parent] using link)
      subst p
      obtain ⟨x, y, edgeEq, words, first, second⟩ := chosen.direction
      exact ⟨x, y, inner.trans words, first, second, edgeEq ▸ tight⟩
    by_cases b : v = chosen.peer
    · subst v
      have eq : chosen.target = p := Option.some.inj (by simpa only [peerRole, AlternatingForestRole.parent] using link)
      subst p
      exact ⟨chosen.target, chosen.peer, outer, targetFixed, peerFixed, state.tight _ paired⟩
    obtain ⟨x, y, words, first, second, oldTight⟩ := witnesses (by rwa [← otherRole v a b])
    exact ⟨x, y, (keep v a b).trans words, first, second, oldTight⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingForestLinkMemory

/-! matching/MatchingPairMeaning.lean -/
section RppSource_MatchingPairMeaning
namespace VehicleRoutingSurvey.Routing



theorem normalizedOuterEdge_swap {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (symmetric : ∀ u v, cost u v = cost v u) (effective : Fin k → ℝ) (time : ℝ) (u v : Fin k) :
    normalizedOuterEdge cost effective time u v = normalizedOuterEdge cost effective time v u := by
  have key : time + time + (cost u v - effective u - effective v) =
      time + time + (cost v u - effective v - effective u) := by rw [symmetric u v]; ring
  have endpoints : s(u,v) = s(v,u) := Sym2.eq_swap
  simp only [normalizedOuterEdge, key, endpoints]

theorem matchingPairSlot_lt {k : ℕ} (a b : Fin k) : k*a.val+b.val < k*k := by
  have bound := Nat.mul_le_mul_left k (Nat.succ_le_of_lt a.isLt)
  rw [Nat.mul_succ] at bound
  have hb := b.isLt
  omega

theorem outerRefreshPairInput_some_iff {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (time : ℝ) (u v a b : Fin k)
    (d : DualSlack (MatchingDualEvent k)) :
    outerRefreshPairInput rep role cost effective time u v (k*a.val+b.val) = some d ↔
      rep u ≠ rep v ∧ (role (rep v) = 1 ∧
        ((a = rep u ∧ b = rep v) ∨ (a = rep v ∧ b = rep u))) ∧
        normalizedOuterEdge cost effective time u v = d := by
  have slots (x y : Fin k) : k*a.val+b.val = k*x.val+y.val ↔ a = x ∧ b = y := by
    simpa only [Fin.ext_iff] using (denseMatrixOffset_eq_iff (i := a.val) (i' := x.val) b.isLt y.isLt)
  by_cases same : rep u = rep v
  · simp [outerRefreshPairInput, same]
  · simp only [outerRefreshPairInput, if_neg same, outerNeighborPairCandidate, slots, same, not_false_eq_true, true_and]
    split <;> simp_all [normalizedOuterEdge]



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

/-- Mathematical and physical input shared by the event arms after applying
the selected dual adjustment. The old selector minima are now minima at the
new numerical point. -/
structure MatchingAdvancedStage {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (positive : 0 < k) (cutAt : Fin k → Finset (Fin k))
    (original s : ArithmeticState) where
  primal : CompactMatchingPrimalDualMemory state original s
  search : CompactMatchingSearchForest part forest state.partialMate part.tightBetween
  witnesses : MatchingForestOriginalWitnesses part forest s
  links : MatchingForestLinkMemory part forest s
  dual : MatchingSearchDualMemory part forest s
  registry : MatchingRegistryView dual
  reads : MatchingRefreshInput s part.representative (fun u => alternatingRoleCode (forest.role u)) cost
    (effectiveVertexPotential state.cuts state.potential state.cutDual)
  pairs : MatchingSearchOuterBuckets s part.representative (fun u => alternatingRoleCode (forest.role u)) cost
    (effectiveVertexPotential state.cuts state.potential state.cutDual)
  valid : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i
  least : ∀ g : MatchingCandidateGroup k, LeastSlackEntry ((matchingSearchSlacks part forest positive).filter fun d =>
    @decide _ (Classical.propDecidable (g.admits part.blocks forest (part.representativeOf positive) d)))
    (readMatchingCandidate cutAt s g.slot)

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
namespace VehicleRoutingSurvey.Routing





















private def matchingDispatchTagged (s : ArithmeticState) : ArithmeticState :=
  {s with pc := 3, nr := Function.update (Function.update (Function.update s.nr 36 0) 37 1) 38 2}

private theorem initMatchingDispatchTags_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) : BlockRuns initMatchingDispatchTags 3 s (matchingDispatchTagged s) := by
  apply BlockRuns.of_running_exit
  · simp [initMatchingDispatchTags, matchingDispatchTagged, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · exact running
  · rfl



private theorem noTraceBlock (s : ArithmeticState) (entry : s.pc = 0) : BlockRuns [] 0 s s :=
  ⟨fun i hi => (Nat.not_lt_zero i hi).elim, by simp, entry⟩

/-- Growing and expanding read only the selected dictionary entry and do not need traces. -/
theorem classifyAndTraceMatchingEvent_simple (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (direct : matchingEventClass s = 0 ∨ matchingEventClass s = 2) :
    ∃ t steps, steps ≤ 28 ∧ BlockRuns classifyAndTraceMatchingEvent steps s t ∧ t.halted = false ∧
      t.nr 35 = matchingEventClass s ∧ t.nr 36 = 0 ∧ t.nr 37 = 1 ∧ t.nr 38 = 2 ∧ t.nr 1 = s.nr 1 ∧
      t.nr 91 = s.nr 1 ∧ (t.nr 92, t.nr 93) = matchingOriginalGrowthEvent s ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r ∈ [30, 31, 32, 33, 34, 40, 41, 42], t.nr r = s.nr r := by
  obtain ⟨detected, firstSteps, firstCost, cls⟩ := classifyMatchingSelectedEvent_spec s entry running one
  let leading := {detected with pc := 0}
  let t := matchingDispatchTagged leading
  let p := {t with pc := 0}
  have set := initMatchingDispatchTags_spec leading rfl cls.running
  have tag : p.nr 35 = matchingEventClass s := by simpa [p, t, matchingDispatchTagged, leading] using cls.tag
  have zero : p.nr 36 = 0 := by simp [p, t, matchingDispatchTagged]
  have unit : p.nr 37 = 1 := by simp [p, t, matchingDispatchTagged]
  have two : p.nr 38 = 2 := by simp [p, t, matchingDispatchTagged]
  have live : p.halted = false := cls.running
  let body := branchOnAtMost 35 37 (branchOnAtMost 35 36 [] resolveMatchingOuterEvent) []
  have directly : ∃ ticks ≤ 4, BlockRuns body ticks p {p with pc := body.length} := by
    rcases direct with grow | expand
    · have low : p.nr 35 ≤ p.nr 36 := by omega
      have middle : p.nr 35 ≤ p.nr 37 := by omega
      have inside := branchOnAtMost_left 35 36 [] resolveMatchingOuterEvent (s := p) rfl live low (noTraceBlock p rfl) live
      have outside := branchOnAtMost_left 35 37 _ [] (s := p) rfl live middle inside live
      exact ⟨4, le_rfl, outside⟩
    · have higher : p.nr 37 < p.nr 35 := by omega
      exact ⟨1, by decide, branchOnAtMost_right 35 37 (branchOnAtMost 35 36 [] resolveMatchingOuterEvent) []
        (s := p) rfl live higher (noTraceBlock p rfl) live⟩
  obtain ⟨lastSteps, short, last⟩ := directly
  refine ⟨_, firstSteps + (3 + lastSteps), by omega, cls.run.append (set.append last), live,
    tag, zero, unit, two, ?_, ?_, ?_, cls.natural, cls.real, cls.realRegisters, ?_⟩
  · change p.nr 1 = s.nr 1
    simpa [p, t, matchingDispatchTagged, leading] using cls.registers 1 (by decide)
  · change p.nr 91 = s.nr 1
    simpa [p, t, matchingDispatchTagged, leading] using cls.identifier
  · change (p.nr 92, p.nr 93) = matchingOriginalGrowthEvent s
    simpa [p, t, matchingDispatchTagged, leading] using cls.endpoints
  · intro r hr
    change p.nr r = s.nr r
    have a : r ≠ 36 := by simp at hr; omega
    have b : r ≠ 37 := by simp at hr; omega
    have c : r ≠ 38 := by simp at hr; omega
    have d : r ∉ [0, 2, 6, 10, 11, 14, 35, 91, 92, 93] := by simp at hr ⊢; omega
    simpa [p, t, matchingDispatchTagged, leading, Function.update_of_ne a, Function.update_of_ne b, Function.update_of_ne c]
      using cls.registers r d





end VehicleRoutingSurvey.Routing
end RppSource_MatchingTraceDispatch

/-! matching/MatchingChosenFrame.lean -/
section RppSource_MatchingChosenFrame
namespace VehicleRoutingSurvey.Routing

/-- Register-only bookkeeping between selection and the dual update preserves
the chosen mathematical event and every decoded row. -/
def MatchingChosenStage.reframe {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {cutAt : Fin k → Finset (Fin k)}
    {original s t : ArithmeticState} (chosen : MatchingChosenStage part forest positive cutAt original s)
    (natural : t.nm = s.nm) (real : t.rm = s.rm) (delta : t.rr 1 = s.rr 1) (clock : t.rr 15 = s.rr 15)
    (id : t.nr 1 = s.nr 1)
    (regs : ∀ r, r = 20 ∨ r = 21 ∨ (50 ≤ r ∧ r ≤ 90) ∨ 100 ≤ r → t.nr r = s.nr r) :
    MatchingChosenStage part forest positive cutAt original t := by
  have port (r : ℕ) (safe : r = 20 ∨ r = 21 ∨ (50 ≤ r ∧ r ≤ 90) ∨ 100 ≤ r := by decide) := regs r safe
  have tables (r : ℕ) (table : r ∈ matchingRefreshTableRegisters) : t.nr r = s.nr r :=
    port r (by simp [matchingRefreshTableRegisters] at table; omega)
  have read := chosen.reads.keeps (t := t) ⟨fun a _ => congrFun natural a, fun a _ _ _ => congrFun real a⟩ tables
  have primal := chosen.primal
  have stored : CompactMatchingPrimalDualMemory state original t := by
    refine ⟨read.layout.dimension, (port 56).trans primal.oddMap, ?_, ?_, ?_, ?_, ?_⟩
    · rw [port 50]; exact primal.mateAbove
    · intro v; rw [natural, port 50]; exact primal.mate v
    · intro r h; exact (port r (.inr (.inr (.inr h)))).trans (primal.saved r h)
    · intro a h; exact (congrFun natural a).trans (primal.natural a h)
    · intro a h; exact (congrFun real a).trans (primal.real a h)
  have top (v : Fin k) : blossomNodeAt t v = blossomNodeAt s v := by simp only [blossomNodeAt, port 74, natural]
  let dual : MatchingSearchDualMemory part forest t := {
    dimension := read.layout.dimension
    separated := by rw [port 62, port 75]; exact chosen.dual.separated
    reps := read.representatives
    roles := by rw [natural, port 51]; exact chosen.dual.roles
    effective := read.potentials
    node := chosen.dual.node
    nodeNonzero := chosen.dual.nodeNonzero
    nodeInjective := chosen.dual.nodeInjective
    cutValues B h := by rw [real, port 75]; exact chosen.dual.cutValues B h
    top v := (top v).trans (chosen.dual.top v) }
  let registry : MatchingRegistryView dual := chosen.registry.transport rfl (port 77) (port 78) (port 76) (port 65)
    top (fun a _ => congrFun natural a)
  have words (v : Fin k) : matchingForestWitnessAt t.nm (t.nr 90) v.val = matchingForestWitnessAt s.nm (s.nr 90) v.val := by
    rw [natural, port 90]
  have event : MatchingEventRecord cutAt (matchingOriginalGrowthEvent t) chosen.event := by
    simpa only [matchingOriginalGrowthEvent, natural, port 54, id] using chosen.chosen
  have shift := delta.symm ▸ chosen.adjustment
  have kind := matchingEventClass_of_adjustment state part.blocks forest (part.representativeOf positive) cutAt
    read.layout.dimension dual.roles (fun v => by rw [part.representativeOf_block]; exact dual.reps v) event shift
  have rows := (matchingCacheReads_unchanged cutAt natural real tables).1
  have keys := (matchingCacheReads_unchanged cutAt natural real tables).2
  refine ⟨chosen.event, event, kind, shift, stored, dual, registry, read, ?_, chosen.links.advance rfl words,
    ⟨fun i hi => (keys i).1.symm ▸ chosen.pairs.valid i hi, ?_, ?_⟩, ?_, ?_⟩
  · intro child parent link
    simpa only [natural, port 90] using chosen.witnesses link
  · intro a b different first last
    rw [clock, (keys _).2]
    exact chosen.pairs.least a b different first last
  · intro a b off; exact (keys _).2.trans (chosen.pairs.inactive a b off)
  · intro i hi; exact (rows i).1.symm ▸ chosen.valid i (port 61 ▸ hi)
  · intro _ _ group; rw [delta, (rows group.slot).2]; exact chosen.least group

set_option maxRecDepth 8192 in
theorem MatchingChosenStage.dispatchDirect {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {cutAt : Fin k → Finset (Fin k)}
    {original s : ArithmeticState} (chosen : MatchingChosenStage part forest positive cutAt original s)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (direct : matchingEventClass s = 0 ∨ matchingEventClass s = 2) :
    ∃ t ticks, BlockRuns classifyAndTraceMatchingEvent ticks s t ∧ ticks ≤ 28 ∧ t.halted = false ∧
      t.nr 35 = matchingEventClass s ∧ t.nr 36 = 0 ∧ t.nr 37 = 1 ∧ t.nr 38 = 2 ∧
      (t.nr 92,t.nr 93) = matchingOriginalGrowthEvent s ∧ t.nr 1 = s.nr 1 ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ r, r = 9 ∨ r = 20 ∨ r = 21 ∨ (30 ≤ r ∧ r ≤ 34) ∨ (39 ≤ r ∧ r ≤ 90) ∨ 100 ≤ r →
        t.nr r = s.nr r) ∧
      Nonempty (MatchingChosenStage part forest positive cutAt original {t with pc := 0}) := by
  obtain ⟨t, ticks, limit, run, live, tag, zero, unit, two, id, _, ends, nm, rm, rr, _⟩ :=
    classifyAndTraceMatchingEvent_simple s entry running one direct
  have kept (r : ℕ) (eligible : r = 9 ∨ r = 20 ∨ r = 21 ∨ (30 ≤ r ∧ r ≤ 34) ∨
      (39 ≤ r ∧ r ≤ 90) ∨ 100 ≤ r) : t.nr r = s.nr r := by
    have safe : classifyAndTraceMatchingEvent.all (fun ins =>
      let n := naturalDestination ins
      decide (n ≠ 9 ∧ n ≠ 20 ∧ n ≠ 21 ∧ (n < 30 ∨ 34 < n) ∧ (n < 39 ∨ 90 < n) ∧ n < 100)) = true := by decide
    rw [← run.run]
    apply arithmeticRun_keeps_register _ s ticks
    intro ins member eq
    have h := of_decide_eq_true (List.all_eq_true.mp safe ins member)
    change naturalDestination ins ≠ 9 ∧ naturalDestination ins ≠ 20 ∧ naturalDestination ins ≠ 21 ∧
      (naturalDestination ins < 30 ∨ 34 < naturalDestination ins) ∧
      (naturalDestination ins < 39 ∨ 90 < naturalDestination ins) ∧ naturalDestination ins < 100 at h
    omega
  exact ⟨t, ticks, run, limit, live, tag, zero, unit, two, ends, id, nm, rm, rr, kept,
    ⟨chosen.reframe (t := {t with pc := 0}) nm rm (congrFun rr 1) (congrFun rr 15) id
      (fun r needed => kept r (by omega))⟩⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingChosenFrame

/-! matching/MatchingDispatchState.lean -/
section RppSource_MatchingDispatchState
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory





/-- Bookkeeping that leaves memory and the stage's registers unchanged
preserves the selected event, cycle registry, and remaining work allowance. -/
def MatchingDispatchState.reframe {k i : ℕ} {cost : Fin k → Fin k → ℝ} {original s t : ArithmeticState}
    (before : MatchingDispatchState cost original i s)
    (natural : t.nm = s.nm) (real : t.rm = s.rm) (rr : t.rr = s.rr) (winner : t.nr 1 = s.nr 1)
    (ports : ∀ r, r = 9 ∨ r = 20 ∨ r = 21 ∨ r = 39 ∨ (50 ≤ r ∧ r ≤ 90) ∨ 100 ≤ r →
      t.nr r = s.nr r) : MatchingDispatchState cost original i t := by
  have fixed (r : ℕ) (used : r = 9 ∨ r = 20 ∨ r = 21 ∨ r = 39 ∨ (50 ≤ r ∧ r ≤ 90) ∨ 100 ≤ r := by decide) :=
    ports r used
  let selected := before.selected.reframe (t := t) natural real (congrFun rr 1) (congrFun rr 15) winner
    (fun r used => ports r (by omega))
  have ids : selected.dual.node = before.selected.dual.node := rfl
  have trees : selected.registry.trees.tree = before.selected.registry.trees.tree := rfl
  have cycles := before.cycles.sameNodes selected.registry ids trees
    (fun B h => (before.cycles.memory B h).sameMemory natural (fun r used => fixed r (by simp at used; omega)))
  have storage := before.storage.keeps (t := t)
    (fun r used => fixed r (by simp [matchingFixedStorageRegisters] at used; omega))
  have order := before.order.transport (t := t) (by simp only [matchingRebaseScratchEnd, fixed 80, fixed 55])
    (fixed 76) (fixed 68) (fun _ _ _ => by simp only [matchingCycleRecordStart, fixed 77, natural])
    (fun _ _ _ => by simp only [matchingCycleRecordEnd, matchingCycleRecordStart, fixed 77, fixed 78, natural])
  have countEq : matchingStageCountsFromRAM k t (t.nr 39) = matchingStageCountsFromRAM k s (s.nr 39) := by
    rw [matchingStageCountsFromRAM_eq selected.dual before.positive _ selected.registry.trees selected.registry.unique selected.registry.keys,
      matchingStageCountsFromRAM_eq before.selected.dual before.positive _ before.selected.registry.trees before.selected.registry.unique
        before.selected.registry.keys, ids, fixed 39]
  exact ⟨before.state, before.part, before.forest, before.positive, before.count, before.top, before.internal,
    before.search, selected, cycles, storage, order, by simpa only [ids, fixed 39] using before.fresh,
    before.budget.keeps (fixed 39) (fixed 76) countEq,
    (fixed 9).trans before.one⟩




end VehicleRoutingSurvey.Routing
end RppSource_MatchingDispatchState

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

/-! matching/MatchingCycleArchiveFrame.lean -/
section RppSource_MatchingCycleArchiveFrame
namespace VehicleRoutingSurvey.Routing

def matchingExpansionArchiveCell (k : ℕ) (s : ArithmeticState) (a : ℕ) : Prop :=
  (s.nr 77 ≤ a ∧ a < s.nr 90) ∨ s.nr 80+3*k ≤ a

/-- Every live registry tree reads either its small allocated header ID,
or a row above both of the reserved traversal stacks. -/
theorem MatchingMemberTree.expansionFootprint {k stage : ℕ} {original s : ArithmeticState}
    (tree : MatchingMemberTree) (storage : MatchingStageStorage k original s)
    (order : MatchingCycleRecordOrder s) {counts : MatchingStageCounts}
    (budget : MatchingRegistryBudget k stage s counts) (searching : stage < k/2)
    (bounds : ∀ n ∈ tree.registryIds, 0 < n ∧ n < s.nr 76) :
    tree.readable s.nm (s.nr 77) (s.nr 78) (matchingExpansionArchiveCell k s) := by
  induction tree with
  | nil => trivial
  | leaf _ rest ih => exact ih bounds
  | blossom r n c rest ih tail =>
    have allocation := bounds n (by simp [MatchingMemberTree.registryIds])
    have capacity := budget.allocated_fits searching allocation.2
    have low := (order.bounded n allocation.1 allocation.2).1
    have lengths := storage.lengths
    have traces := storage.traceLeft
    have right := storage.traceRight
    have marks := storage.traceMarks
    have witnesses := storage.witnesses
    have dim := storage.warm.size
    unfold matchingRebaseScratchEnd matchingCycleRecordStart at low
    refine ⟨.inl ⟨by omega,by omega⟩,.inl ⟨by omega,by omega⟩,?_,
      ih (fun id h => bounds id (by simp [MatchingMemberTree.registryIds,h])),
      tail (fun id h => bounds id (by simp [MatchingMemberTree.registryIds,h]))⟩
    intro i hi w hw
    exact .inr (by omega)

def MatchingLiveCycles.memoryOnExpansionArchive {k stage : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {original s t : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (live : MatchingLiveCycles registry) (storage : MatchingStageStorage k original s)
    (order : MatchingCycleRecordOrder s) {counts : MatchingStageCounts}
    (budget : MatchingRegistryBudget k stage s counts) (searching : stage < k/2)
    (ports : ∀ r ∈ ([55,77,78,79,80] : List ℕ), t.nr r = s.nr r)
    (bytes : ∀ a, matchingExpansionArchiveCell k s a → t.nm a = s.nm a) (B : Finset (Fin k)) (h : B ∈ state.cuts) :
    MatchingLiveCycleMemory (live.entry B h) t := by
  let tree := MatchingMemberTree.blossom 0 (dual.node B) (live.entry B h).tree .nil
  apply (live.memory B h).onRegion (region := matchingExpansionArchiveCell k s) _ ports bytes
  · apply tree.expansionFootprint storage order budget searching
    intro n hn
    have classified : n = dual.node B ∨ n ∈ (live.entry B h).tree.registryIds := by
      simpa [tree,MatchingMemberTree.registryIds] using hn
    have member : n ∈ registry.trees.registryIds := by
      rcases classified with eq | below
      · exact (registry.keys n).mpr ⟨B,h,eq.symm⟩
      · exact live.ids B h n below
    obtain ⟨C,present,rfl⟩ := (registry.keys n).mp member
    exact ⟨Nat.pos_of_ne_zero (dual.nodeNonzero C present),registry.allocated C present⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingCycleArchiveFrame

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

/-! matching/MatchingSearchEdgeMeaning.lean -/
section RppSource_MatchingSearchEdgeMeaning
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Exterior edge candidates use the original endpoints' effective potentials. -/
def matchingSearchRawEdge {k : ℕ} (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ)
    (u v : Fin k) (rate : ℝ) : DualSlack (MatchingDualEvent k) :=
  ⟨.edge s(u,v), cost u v-effective u-effective v, rate⟩

private noncomputable def searchEdge {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    (part : CompactMatchingPartition state) (forest : AlternatingForestState (Fin k)) (positive : 0 < k) :=
  let label := part.dualLabel forest positive
  matchingEdgeSlack cost state.cuts state.potential (forestVertexDirection part.blocks label) state.cutDual
    (forestCutDirection part.blocks label)

private theorem searchEdge_mem_iff {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    (part : CompactMatchingPartition state) (forest : AlternatingForestState (Fin k)) (positive : 0 < k)
    {u v : Fin k} {d : DualSlack (MatchingDualEvent k)} (event : d.event = .edge s(u,v)) :
    d ∈ matchingSearchSlacks part forest positive ↔ u ≠ v ∧ searchEdge part forest positive s(u,v) = d := by
  let label := part.dualLabel forest positive
  change d ∈ (compactMatchingEdges k).map (searchEdge part forest positive) ++ state.cuts.toList.map
    (matchingCutSlack state.cutDual (forestCutDirection part.blocks label)) ↔ _
  constructor
  · intro found
    rcases List.mem_append.mp found with edge | cut
    · obtain ⟨e,legal,rfl⟩ := List.mem_map.mp edge
      change MatchingDualEvent.edge e = .edge s(u,v) at event
      obtain rfl := MatchingDualEvent.edge.inj event
      exact ⟨fun eq => (mem_compactMatchingEdges_iff.mp legal) (Sym2.mk_isDiag_iff.mpr eq), rfl⟩
    · obtain ⟨_,_,rfl⟩ := List.mem_map.mp cut
      cases event
  · rintro ⟨separate,rfl⟩
    exact List.mem_append_left _ (List.mem_map_of_mem (mem_compactMatchingEdges_mk separate))

private theorem searchEdge_external {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    (part : CompactMatchingPartition state) (forest : AlternatingForestState (Fin k)) (positive : 0 < k)
    (symmetric : ∀ u v, cost u v = cost v u)
    (nested : ∀ S ∈ state.cuts, ∀ u ∈ S, ∀ v ∈ S, part.blocks.block u = part.blocks.block v)
    {u v : Fin k} (external : part.blocks.block u ≠ part.blocks.block v) :
    searchEdge part forest positive s(u,v) =
      matchingSearchRawEdge cost (effectiveVertexPotential state.cuts state.potential state.cutDual) u v
        ((forest.role (part.representative u)).dualDirection + (forest.role (part.representative v)).dualDirection) := by
  let label := part.dualLabel forest positive
  have diff : u ≠ v := fun h => external (congrArg part.blocks.block h)
  change matchingEdgeSlack cost state.cuts state.potential (forestVertexDirection part.blocks label) state.cutDual
    (forestCutDirection part.blocks label) s(u,v) = _
  dsimp only [matchingEdgeSlack, matchingSearchRawEdge]
  rw [edgeCost_eq_of_symmetric cost symmetric, external_edge_dual_eq_effectivePotential part.blocks nested _ _ external,
    forest_edge_slope part.blocks label (Finset.mem_univ u) (Finset.mem_univ v) diff, if_neg external,
    show label (part.blocks.block u) = _ from part.dualLabel_block forest positive u,
    show label (part.blocks.block v) = _ from part.dualLabel_block forest positive v]
  congr 1
  ring

/-- The entire outer selector row consists of all exterior original edges
incident to the given representative whose two endpoint blocks are outer. -/
theorem matchingSearchOuterGroup_mem_iff {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    (part : CompactMatchingPartition state) (forest : AlternatingForestState (Fin k)) (positive : 0 < k)
    (symmetric : ∀ u v, cost u v = cost v u)
    (nested : ∀ S ∈ state.cuts, ∀ u ∈ S, ∀ v ∈ S, part.blocks.block u = part.blocks.block v)
    (i : Fin k) (d : DualSlack (MatchingDualEvent k)) :
    let eff := effectiveVertexPotential state.cuts state.potential state.cutDual
    let rep := part.representative
    let role := fun u => alternatingRoleCode (forest.role u)
    d ∈ ((matchingSearchSlacks part forest positive).filter fun e => @decide _
      (Classical.propDecidable ((MatchingCandidateGroup.outer i).admits part.blocks forest (part.representativeOf positive) e))) ↔
      ∃ u v, rep u = i ∧ rep u ≠ rep v ∧ role (rep u) = 1 ∧ role (rep v) = 1 ∧ matchingSearchRawEdge cost eff u v 2 = d := by
  classical
  intro eff rep role
  rw [List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨member,speed,u,v,event,source⟩
    obtain ⟨diff,record⟩ := (searchEdge_mem_iff part forest positive event).mp member
    have external : part.blocks.block u ≠ part.blocks.block v := by
      intro same
      rw [← record] at speed
      let label := part.dualLabel forest positive
      change oddCutDualEdgeValue state.cuts (forestVertexDirection part.blocks label)
        (forestCutDirection part.blocks label) s(u,v) = 2 at speed
      rw [forest_edge_slope part.blocks label (Finset.mem_univ u) (Finset.mem_univ v) diff, if_pos same] at speed
      norm_num at speed
    rw [searchEdge_external part forest positive symmetric nested external] at record
    have sourceAt := (part.representativeOf_block positive u).symm.trans source
    refine ⟨u,v,sourceAt,fun h => external (part.same_block.mp h),?_⟩
    rw [← record] at speed ⊢
    cases h : forest.role (part.representative u) <;> cases j : forest.role (part.representative v) <;>
      first
      | solve | norm_num [h,j,matchingSearchRawEdge,AlternatingForestRole.dualDirection] at speed
      | norm_num [rep,role,eff,h,j,matchingSearchRawEdge,alternatingRoleCode,AlternatingForestRole.dualDirection]
  · rintro ⟨u,v,source,distinct,outerU,outerV,rfl⟩
    have external : part.blocks.block u ≠ part.blocks.block v := fun h => distinct (part.same_block.mpr h)
    have record := searchEdge_external part forest positive symmetric nested external
    have converts : searchEdge part forest positive s(u,v) = matchingSearchRawEdge cost eff u v 2 := by
      rw [record]
      cases h : forest.role (part.representative u) <;> cases j : forest.role (part.representative v) <;>
        first
        | solve | norm_num [role,rep,h,alternatingRoleCode] at outerU
        | solve | norm_num [role,rep,j,alternatingRoleCode] at outerV
        | norm_num [eff,h,j,AlternatingForestRole.dualDirection]
    exact ⟨(searchEdge_mem_iff part forest positive (show (matchingSearchRawEdge cost eff u v 2).event = .edge s(u,v) from rfl)).mpr
      ⟨fun h => distinct (congrArg rep h),converts⟩,rfl,u,v,rfl,(part.representativeOf_block positive u).trans source⟩

/-- A nonouter target's incoming row stores exterior original edges from an
outer source. Its rate is one for a dormant target and zero for an inner one. -/
theorem matchingSearchIncomingGroup_mem_iff {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    (part : CompactMatchingPartition state) (forest : AlternatingForestState (Fin k)) (positive : 0 < k)
    (symmetric : ∀ u v, cost u v = cost v u)
    (nested : ∀ S ∈ state.cuts, ∀ u ∈ S, ∀ v ∈ S, part.blocks.block u = part.blocks.block v)
    (v : Fin k) (d : DualSlack (MatchingDualEvent k)) :
    let eff := effectiveVertexPotential state.cuts state.potential state.cutDual
    let rep := part.representative
    let role := fun u => alternatingRoleCode (forest.role u)
    d ∈ ((matchingSearchSlacks part forest positive).filter fun e => @decide _
      (Classical.propDecidable ((MatchingCandidateGroup.incoming v).admits part.blocks forest (part.representativeOf positive) e))) ↔
      ∃ u, rep u ≠ rep v ∧ role (rep u) = 1 ∧ role (rep v) ≠ 1 ∧
        matchingSearchRawEdge cost eff u v (if role (rep v) = 0 then 1 else 0) = d := by
  classical
  intro eff rep role
  rw [List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨member,_,u,event,external,⟨p,outer⟩,target⟩
    obtain ⟨_,record⟩ := (searchEdge_mem_iff part forest positive event).mp member
    rw [searchEdge_external part forest positive symmetric nested external] at record
    rw [part.representativeOf_block positive u] at outer
    rw [part.representativeOf_block positive v] at target
    refine ⟨u,fun h => external (part.same_block.mp h),by simp [role,rep,outer,alternatingRoleCode],?_⟩
    rcases target with idle | ⟨q,inner⟩
    · simp [role,rep,idle,alternatingRoleCode]
      simpa [eff,outer,idle,AlternatingForestRole.dualDirection] using record
    · simp [role,rep,inner,alternatingRoleCode]
      simpa [eff,outer,inner,AlternatingForestRole.dualDirection] using record
  · rintro ⟨u,distinct,on,off,rfl⟩
    let rate : ℝ := if role (rep v) = 0 then 1 else 0
    let datum := matchingSearchRawEdge cost eff u v rate
    have external : part.blocks.block u ≠ part.blocks.block v := fun h => distinct (part.same_block.mpr h)
    have record := searchEdge_external part forest positive symmetric nested external
    have roles : (∃ p,forest.role (rep u) = .outer p) ∧
        (forest.role (rep v) = .unlabelled ∨ ∃ q,forest.role (rep v) = .inner q) := by
      constructor
      · cases h : forest.role (rep u) <;> simp_all [role,alternatingRoleCode]
      · cases h : forest.role (rep v) <;> simp_all [role,alternatingRoleCode]
    obtain ⟨⟨p,outer⟩,target⟩ := roles
    have actual : searchEdge part forest positive s(u,v) = datum := by
      rw [record]
      change matchingSearchRawEdge cost eff u v ((forest.role (rep u)).dualDirection + (forest.role (rep v)).dualDirection) =
        matchingSearchRawEdge cost eff u v rate
      rcases target with idle | ⟨q,inner⟩
      · simp [rate,role,outer,idle,alternatingRoleCode,AlternatingForestRole.dualDirection]
      · simp [rate,role,outer,inner,alternatingRoleCode,AlternatingForestRole.dualDirection]
    have speed : datum.rate = incomingCandidateRate (forest.role (rep v)) := by
      rcases target with idle | ⟨q,inner⟩
      · simp [datum,rate,role,matchingSearchRawEdge,idle,alternatingRoleCode,incomingCandidateRate]
      · simp [datum,rate,role,matchingSearchRawEdge,inner,alternatingRoleCode,incomingCandidateRate]
    refine ⟨(searchEdge_mem_iff part forest positive (show datum.event = .edge s(u,v) from rfl)).mpr
      ⟨fun h => distinct (congrArg rep h),actual⟩, ?_⟩
    change datum.rate = incomingCandidateRate (forest.role (part.representativeOf positive (part.blocks.block v))) ∧ _
    rw [part.representativeOf_block positive v]
    refine ⟨speed,u,rfl,external,?_,?_⟩
    · rw [part.representativeOf_block positive u]
      exact ⟨p,outer⟩
    · simpa only [part.representativeOf_block] using target

end VehicleRoutingSurvey.Routing
end RppSource_MatchingSearchEdgeMeaning

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

theorem matchingCutGroupEntry_least {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (positive : 0 < k) (i : Fin k) :
    LeastSlackEntry ((matchingSearchSlacks part forest positive).filter fun d =>
      @decide _ (Classical.propDecidable ((MatchingCandidateGroup.cut i).admits part.blocks forest
        (part.representativeOf positive) d))) (matchingCutGroupEntry part forest i) := by
  classical
  have hit := matchingCutGroupEntry_mem part forest positive i
  constructor
  · intro d found
    exact List.mem_filter.mpr ⟨((hit d).mpr found).1, decide_eq_true ((hit d).mpr found).2⟩
  · intro d present
    obtain ⟨all, admit⟩ := List.mem_filter.mp present
    exact ⟨d, (hit d).mp ⟨all, of_decide_eq_true admit⟩, le_rfl⟩


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

/-! matching/MatchingGrowthAfterDual.lean -/
section RppSource_MatchingGrowthAfterDual
namespace VehicleRoutingSurvey.Routing

/-- Changing the local program counter between two concatenated blocks
preserves the complete search view. -/
def MatchingAdvancedStage.atEntry {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {cutAt : Fin k → Finset (Fin k)}
    {original s : ArithmeticState} (view : MatchingAdvancedStage part forest positive cutAt original s) :
    MatchingAdvancedStage part forest positive cutAt original {s with pc := 0} := by
  let dual : MatchingSearchDualMemory part forest {s with pc := 0} :=
    ⟨view.dual.dimension, view.dual.separated, view.dual.reps, view.dual.roles, view.dual.effective,
      view.dual.node, view.dual.nodeNonzero, view.dual.nodeInjective, view.dual.cutValues, view.dual.top⟩
  have mate := view.primal
  exact ⟨⟨mate.dimension, mate.oddMap, mate.mateAbove, mate.mate, mate.saved, mate.natural, mate.real⟩,
    view.search, fun h => view.witnesses h, view.links.advance rfl (fun _ => rfl), dual,
    view.registry.transport rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ _ => rfl),
    view.reads.keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun _ _ => rfl),
    ⟨view.pairs.valid,view.pairs.least,view.pairs.inactive⟩, view.valid, view.least⟩

/-- A growth event's selected edge becomes tight at the new dual point.
The role and endpoint words consumed by the executable grow prefix still
name the same original edge after the dual arrays have been written. -/
theorem MatchingChosenStage.advanceGrowth {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {cutAt : Fin k → Finset (Fin k)}
    {original s : ArithmeticState} (chosen : MatchingChosenStage part forest positive cutAt original s)
    (search : CompactMatchingSearchForest part forest state.partialMate part.tightBetween)
    (internal : state.InternalCuts) (top : CompactTopMatching part)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (storage : MatchingStageStorage k original s)
    (grow : matchingEventClass s = 0) :
    let bound : DualBound (MatchingDualEvent k) := ⟨chosen.event, s.rr 1⟩
    let next := state.advanceSearch part search positive internal bound chosen.adjustment
    let nextPart := part.advanceSearch search positive internal bound chosen.adjustment
    ∃ t ticks, BlockRuns advanceMatchingEventDuals ticks s t ∧ ticks ≤ 31*k+6 ∧ t.halted = false ∧
      ∃ (edge : Sym2 (Fin k)) (stage : MatchingAdvancedStage nextPart forest positive cutAt original {t with pc := 0})
        (selection : MatchingGrowthSelection nextPart forest {t with pc := 0} edge),
        chosen.event = .edge edge ∧
        oddCutDualEdgeValue next.cuts next.potential next.cutDual edge = SupplyChainTheory.edgeCost cost edge := by
  intro bound next nextPart
  obtain ⟨t, ticks, run, limit, live, _, nm, ports, ⟨stage, _⟩⟩ :=
    chosen.advance search internal entry running one storage
  let b := {t with pc := 0}
  let ready : MatchingAdvancedStage nextPart forest positive cutAt original b := stage.atEntry
  have reg (r : ℕ) (safe : r ∉ [0,6,7,10,11,12,14] := by decide) : b.nr r = s.nr r := ports r safe
  have bytes : b.nm = s.nm := nm
  have words : matchingOriginalGrowthEvent b = matchingOriginalGrowthEvent s := by
    simp only [matchingOriginalGrowthEvent, reg 1, reg 54, bytes]
  have left : matchingEventLeftRep b = matchingEventLeftRep s := by simp only [matchingEventLeftRep, words, reg 57, bytes]
  have right : matchingEventRightRep b = matchingEventRightRep s := by simp only [matchingEventRightRep, words, reg 57, bytes]
  have tag : matchingEventClass b = matchingEventClass s := by
    simp only [matchingEventClass, matchingEventIsCut, words, reg 55, reg 51, bytes, left, right]
  cases kind : chosen.event with
  | cut B =>
    have typed := chosen.kind
    rw [kind] at typed
    obtain ⟨_,_,_,bad,_⟩ := typed
    omega
  | edge edge =>
    have old := chosen.kind
    rw [kind] at old
    have typed : MatchingEventClassView nextPart.blocks forest (nextPart.representativeOf positive) cutAt b (.edge edge) := by
      simpa only [MatchingEventClassView, words, left, right, tag] using! old
    have tight : oddCutDualEdgeValue next.cuts next.potential next.cutDual edge = SupplyChainTheory.edgeCost cost edge := by
      have hit := chosen.adjustment.2.2.2
      rw [kind] at hit
      exact hit.2.2
    have topAfter : CompactTopMatching nextPart := ⟨top.interior,top.matchedBase⟩
    obtain ⟨g⟩ := matchingGrowthSelection_of_class positive cutAt topAfter ready.primal ready.search
      ready.dual.roles ready.dual.reps typed (tag.trans grow) tight
    exact ⟨t, ticks, run, limit, live, edge, ready, g, rfl, tight⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowthAfterDual

/-! matching/MatchingCacheRegionReads.lean -/
section RppSource_MatchingCacheRegionReads
namespace VehicleRoutingSurvey.Routing

/-- A cache with valid row identifiers only consults its allocated dictionary
records and score cells. Writes outside these intervals preserve both tables. -/
theorem matchingCacheRegionReads {k : ℕ} {s t : ArithmeticState}
    (layout : MatchingCacheLayout k s)
    (ports : ∀ r ∈ ([54,58,59,60,65,66] : List ℕ), t.nr r = s.nr r)
    (natural : ∀ a, s.nr 58 ≤ a → a < s.nr 65+2*(k*k) → t.nm a = s.nm a)
    (real : ∀ a, s.nr 59 ≤ a → a < s.nr 66+k*k → t.rm a = s.rm a)
    (cutAt : Fin k → Finset (Fin k)) (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i) :
    (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i = readMatchingCandidate cutAt s i) ∧
    (∀ i < k*k, MatchingPairBucketValid k t i = MatchingPairBucketValid k s i ∧
       readMatchingPairBucket (k := k) t i = readMatchingPairBucket (k := k) s i) := by
  have ids := layout.idsBefore
  have records := layout.recordsBefore
  have slacks := layout.slacksBefore
  have rates := layout.ratesBefore
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

end VehicleRoutingSurvey.Routing
end RppSource_MatchingCacheRegionReads

/-! matching/ExpansionIncomingRows.lean -/
section RppSource_ExpansionIncomingRows
namespace VehicleRoutingSurvey.Routing



/-- Changing the common rate preserves the minimum under comparison by raw slack. -/
theorem LeastSlackEntry.rerate {Event : Type*} {choices : List (DualSlack Event)}
    {retained : Option (DualSlack Event)} (old : LeastSlackEntry choices retained) (rate : ℝ) :
    let rerate := fun d : DualSlack Event => {d with rate := rate}
    LeastSlackEntry (choices.map rerate) (retained.map rerate) := by
  intro rerate
  constructor
  · intro d present
    cases kept : retained with
    | none => simp [kept] at present
    | some previous =>
      have same : rerate previous = d := Option.some.inj (by simpa only [kept, Option.map_some] using present)
      exact same ▸ List.mem_map_of_mem (f := rerate) (old.sound kept)
  · intro d present
    obtain ⟨previous, member, rfl⟩ := List.mem_map.mp present
    obtain ⟨choice, witness, least⟩ := old.covers previous member
    exact ⟨rerate choice, congrArg (Option.map rerate) witness, least⟩











end VehicleRoutingSurvey.Routing
end RppSource_ExpansionIncomingRows

/-! matching/MatchingExpansionRowOffers.lean -/
section RppSource_MatchingExpansionRowOffers
namespace VehicleRoutingSurvey.Routing

theorem matchingRawOuterOffer_iff {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (u v p : Fin k) (d : DualSlack (MatchingDualEvent k)) :
    outerRefreshRowInput rep role cost effective u v p.val = some d ↔
      rep u ≠ rep v ∧ role (rep v) = 1 ∧ (p = rep u ∨ p = rep v) ∧
      matchingSearchRawEdge cost effective u v 2 = d := by
  have smaller := p.isLt
  have apart : p.val ≠ k+v.val := by omega
  by_cases internal : rep u = rep v
  · simp [outerRefreshRowInput, internal]
  by_cases on : role (rep v) = 1
  · by_cases chosen : p = rep u ∨ p = rep v
    · have addr : p.val = (rep u).val ∨ p.val = (rep v).val := chosen.imp (congrArg Fin.val) (congrArg Fin.val)
      simp [outerRefreshRowInput, outerNeighborRowCandidate, internal, on, chosen, addr, matchingSearchRawEdge]
    · have miss : ¬ (p.val = (rep u).val ∨ p.val = (rep v).val) := fun h => chosen (h.imp Fin.ext Fin.ext)
      simp [outerRefreshRowInput, outerNeighborRowCandidate, internal, on, chosen, miss]
  · simp [outerRefreshRowInput, outerNeighborRowCandidate, internal, on, apart]

theorem matchingRawIncomingOffer_iff {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (u w v : Fin k) (d : DualSlack (MatchingDualEvent k)) :
    outerRefreshRowInput rep role cost effective u w (k+v.val) = some d ↔
      w = v ∧ rep u ≠ rep v ∧ role (rep v) ≠ 1 ∧
      matchingSearchRawEdge cost effective u v (if role (rep v) = 0 then 1 else 0) = d := by
  have au := (rep u).isLt
  have aw := (rep w).isLt
  have away : ¬ (k+v.val = (rep u).val ∨ k+v.val = (rep w).val) := by omega
  by_cases target : w = v
  · subst w
    by_cases same : rep u = rep v <;> by_cases on : role (rep v) = 1 <;>
      simp [outerRefreshRowInput, outerNeighborRowCandidate, same, on, away, matchingSearchRawEdge]
  · have miss : v.val ≠ w.val := fun eq => target (Fin.ext eq.symm)
    by_cases same : rep u = rep w <;> by_cases on : role (rep w) = 1 <;>
      simp [outerRefreshRowInput, outerNeighborRowCandidate, same, on, away, miss, target]

noncomputable def expansionRowOffers {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (fresh : List (Fin k)) (i : ℕ) :=
  fresh.flatMap (fun u => (List.finRange k).filterMap (fun v => outerRefreshRowInput rep role cost effective u v i))

theorem expansionOuterOffers_mem {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (fresh : List (Fin k)) (p : Fin k) (d : DualSlack (MatchingDualEvent k)) :
    d ∈ expansionRowOffers rep role cost effective fresh p.val ↔
      ∃ u ∈ fresh, ∃ v : Fin k, rep u ≠ rep v ∧ role (rep v) = 1 ∧ (p = rep u ∨ p = rep v) ∧
      matchingSearchRawEdge cost effective u v 2 = d := by
  simp only [expansionRowOffers, List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and, matchingRawOuterOffer_iff]

theorem expansionIncomingOffers_mem {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (fresh : List (Fin k)) (v : Fin k) (d : DualSlack (MatchingDualEvent k)) :
    d ∈ expansionRowOffers rep role cost effective fresh (k+v.val) ↔
      ∃ u ∈ fresh, rep u ≠ rep v ∧ role (rep v) ≠ 1 ∧
      matchingSearchRawEdge cost effective u v (if role (rep v) = 0 then 1 else 0) = d := by
  simp only [expansionRowOffers, List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and,
    matchingRawIncomingOffer_iff, exists_eq_left]

theorem expansionCutOffers_empty {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (fresh : List (Fin k)) (v : Fin k) :
    expansionRowOffers rep role cost effective fresh (2*k+v.val) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro d found
  obtain ⟨u,_,listed⟩ := List.mem_flatMap.mp found
  obtain ⟨w,_,offered⟩ := List.mem_filterMap.mp listed
  have uPort := (rep u).isLt
  have wPort := (rep w).isLt
  have wLimit := w.isLt
  have lo : ¬ (2*k+v.val = (rep u).val ∨ 2*k+v.val = (rep w).val) := by omega
  have mid : 2*k+v.val ≠ k+w.val := by omega
  by_cases same : rep u = rep w <;> by_cases on : role (rep w) = 1 <;>
    simp [outerRefreshRowInput, outerNeighborRowCandidate, same, on, lo, mid] at offered

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionRowOffers

/-! matching/MatchingExpansionEdgeMinimum.lean -/
section RppSource_MatchingExpansionEdgeMinimum
namespace VehicleRoutingSurvey.Routing

/-- Old outer-edge rows keep both original endpoints and their representatives.
The fresh scan covers newly eligible edges from either end. -/
theorem expansionOuterRow_least {k : ℕ} {oldRep rep : Fin k → Fin k} {old role : Fin k → ℕ}
    {cost : Fin k → Fin k → ℝ} {eff : Fin k → ℝ} (symmetric : ∀ u v, cost u v = cost v u)
    (stays : ∀ v, old (oldRep v) = 1 → rep v = oldRep v ∧ role (rep v) = 1)
    (fresh : List (Fin k)) (freshIff : ∀ v, v ∈ fresh ↔ old (oldRep v) ≠ 1 ∧ role (rep v) = 1)
    (p : Fin k) {prior full : List (DualSlack (MatchingDualEvent k))} {cached : Option (DualSlack (MatchingDualEvent k))}
    (before : LeastSlackEntry prior cached)
    (oldGroup : ∀ d, d ∈ prior ↔ ∃ u v, oldRep u = p ∧ oldRep u ≠ oldRep v ∧ old (oldRep u) = 1 ∧
      old (oldRep v) = 1 ∧ matchingSearchRawEdge cost eff u v 2 = d)
    (newGroup : ∀ d, d ∈ full ↔ ∃ u v, rep u = p ∧ rep u ≠ rep v ∧ role (rep u) = 1 ∧
      role (rep v) = 1 ∧ matchingSearchRawEdge cost eff u v 2 = d) :
    LeastSlackEntry full (insertSlackCandidates (expansionRowOffers rep role cost eff fresh p.val) cached) := by
  let offers := expansionRowOffers rep role cost eff fresh p.val
  have mem := expansionOuterOffers_mem rep role cost eff fresh p
  have reversed (u v : Fin k) : matchingSearchRawEdge cost eff v u 2 = matchingSearchRawEdge cost eff u v 2 := by
    have same : cost v u - eff v - eff u = cost u v - eff u - eff v := by rw [symmetric v u]; ring
    simp only [matchingSearchRawEdge, same, show s(v,u) = s(u,v) from Sym2.eq_swap]
  have exactList (d) : d ∈ offers.reverse ++ prior ↔ d ∈ full := by
    rw [List.mem_append, List.mem_reverse, newGroup]
    constructor
    · rintro (offered | earlier)
      · obtain ⟨u,inList,v,distinct,on,side,value⟩ := (mem d).mp offered
        have source := ((freshIff u).mp inList).2
        rcases side with first | second
        · exact ⟨u,v,first.symm,distinct,source,on,value⟩
        · exact ⟨v,u,second.symm,distinct.symm,on,source,(reversed u v).trans value⟩
      · obtain ⟨u,v,index,diff,left,right,value⟩ := (oldGroup d).mp earlier
        obtain ⟨a, active⟩ := stays u left
        obtain ⟨b, other⟩ := stays v right
        exact ⟨u,v,a.trans index,fun eq => diff (a.symm.trans (eq.trans b)),active,other,value⟩
    · rintro ⟨u,v,index,diff,left,right,value⟩
      by_cases uOld : old (oldRep u) = 1
      · by_cases vOld : old (oldRep v) = 1
        · have a := (stays u uOld).1
          have b := (stays v vOld).1
          exact .inr ((oldGroup d).mpr ⟨u,v,a.symm.trans index,fun eq => diff (a.trans (eq.trans b.symm)),uOld,vOld,value⟩)
        · exact .inl ((mem d).mpr ⟨v,(freshIff v).mpr ⟨vOld,right⟩,u,diff.symm,left,.inr index.symm,(reversed u v).trans value⟩)
      · exact .inl ((mem d).mpr ⟨u,(freshIff u).mpr ⟨uOld,left⟩,v,diff,right,.inl index.symm,value⟩)
  have result := before.insert_many offers
  exact ⟨fun chosen => (exactList _).mp (result.sound chosen), fun d h => result.covers d ((exactList d).mpr h)⟩

/-- The old incoming candidates are retained with the target's updated rate
until their target becomes outer, when they are cleared. Newly outer sources
insert all other witnesses for the row. -/
theorem expansionIncomingRow_least {k : ℕ} {oldRep rep : Fin k → Fin k} {old role : Fin k → ℕ}
    {cost : Fin k → Fin k → ℝ} {eff : Fin k → ℝ}
    (stays : ∀ v, old (oldRep v) = 1 → role (rep v) = 1)
    (fresh : List (Fin k)) (freshIff : ∀ v, v ∈ fresh ↔ old (oldRep v) ≠ 1 ∧ role (rep v) = 1)
    (v : Fin k) {prior full : List (DualSlack (MatchingDualEvent k))} {cached : Option (DualSlack (MatchingDualEvent k))}
    (before : LeastSlackEntry prior cached)
    (oldGroup : ∀ d, d ∈ prior ↔ ∃ u, oldRep u ≠ oldRep v ∧ old (oldRep u) = 1 ∧ old (oldRep v) ≠ 1 ∧
      matchingSearchRawEdge cost eff u v (if old (oldRep v) = 0 then 1 else 0) = d)
    (newGroup : ∀ d, d ∈ full ↔ ∃ u, rep u ≠ rep v ∧ role (rep u) = 1 ∧ role (rep v) ≠ 1 ∧
      matchingSearchRawEdge cost eff u v (if role (rep v) = 0 then 1 else 0) = d) :
    let rate : ℝ := if role (rep v) = 0 then 1 else 0
    let seed := if role (rep v) = 1 then none else cached.map (fun d => {d with rate := rate})
    LeastSlackEntry full (insertSlackCandidates (expansionRowOffers rep role cost eff fresh (k+v.val)) seed) := by
  intro rate seed
  let offers := expansionRowOffers rep role cost eff fresh (k+v.val)
  have mem := expansionIncomingOffers_mem rep role cost eff fresh v
  by_cases outer : role (rep v) = 1
  · have empty : offers = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro d h
      obtain ⟨_,_,_,off,_⟩ := (mem d).mp h
      exact off outer
    have noFull (d) (h : d ∈ full) : False := by
      obtain ⟨_,_,_,off,_⟩ := (newGroup d).mp h
      exact off outer
    change LeastSlackEntry full (insertSlackCandidates offers seed)
    rw [empty]
    simp only [seed, if_pos outer, insertSlackCandidates, List.foldl_nil]
    constructor
    · intro _ h
      cases h
    · exact fun d h => (noFull d h).elim
  · have priorOff : old (oldRep v) ≠ 1 := fun was => outer (stays v was)
    let rerate := fun d : DualSlack (MatchingDualEvent k) => {d with rate := rate}
    have changed : LeastSlackEntry (prior.map rerate) (cached.map rerate) := before.rerate rate
    have result := changed.insert_many offers
    have exactList (d) : d ∈ offers.reverse ++ prior.map rerate ↔ d ∈ full := by
      rw [List.mem_append, List.mem_reverse, List.mem_map, newGroup]
      constructor
      · rintro (offered | ⟨e,oldEntry,rfl⟩)
        · obtain ⟨u,member,apart,off,value⟩ := (mem d).mp offered
          exact ⟨u,apart,((freshIff u).mp member).2,off,value⟩
        · obtain ⟨u,_,on,_,raw⟩ := (oldGroup e).mp oldEntry
          have now := stays u on
          have apart : rep u ≠ rep v := fun eq => outer (eq ▸ now)
          exact ⟨u,apart,now,outer,congrArg rerate raw⟩
      · rintro ⟨u,apart,on,_,value⟩
        by_cases was : old (oldRep u) = 1
        · let prev := matchingSearchRawEdge cost eff u v (if old (oldRep v) = 0 then 1 else 0)
          have split : oldRep u ≠ oldRep v := fun eq => priorOff (eq ▸ was)
          exact .inr ⟨prev,(oldGroup prev).mpr ⟨u,split,was,priorOff,rfl⟩,value⟩
        · exact .inl ((mem d).mpr ⟨u,(freshIff u).mpr ⟨was,on⟩,apart,outer,value⟩)
    change LeastSlackEntry full (insertSlackCandidates offers seed)
    simp only [seed, if_neg outer]
    exact ⟨fun chosen => (exactList _).mp (result.sound chosen), fun d h => result.covers d ((exactList d).mpr h)⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionEdgeMinimum

/-! matching/MatchingGrowthRefresh.lean -/
section RppSource_MatchingGrowthRefresh
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 8192

noncomputable def growthSourceRowInputs {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (peer : Fin k) (i : ℕ) (u : Fin k) :
    List (DualSlack (MatchingDualEvent k)) :=
  if rep u = peer then (List.finRange k).filterMap (fun v => outerRefreshRowInput rep role cost effective u v i) else []

noncomputable def growthSourcePairInputs {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (time : ℝ) (peer : Fin k) (i : ℕ) (u : Fin k) :
    List (DualSlack (MatchingDualEvent k)) :=
  if rep u = peer then (List.finRange k).filterMap (fun v => outerRefreshPairInput rep role cost effective time u v i) else []

/-- The source test visits exactly the originals in the newly outer block.
Each selected row performs one checked neighbor sweep. -/
theorem refreshGrowthCacheSourceBlock_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} {rep : Fin k → Fin k} {role : Fin k → ℕ}
    {cost : Fin k → Fin k → ℝ} {effective : Fin k → ℝ} {u peer : Fin k}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (input : MatchingRefreshInput s rep role cost effective) (source : s.nr 24 = u.val) (outer : s.nr 26 = peer.val)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k*k, MatchingPairBucketValid k s i) :
    ∃ t steps, BlockRuns refreshGrowthCacheSourceBlock steps s t ∧ t.halted = false ∧ steps ≤ 98 * k + 10 ∧
      MatchingRefreshInput t rep role cost effective ∧ MatchingCacheFootprint k s t ∧ t.rr 15 = s.rr 15 ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i =
        insertSlackCandidates (growthSourceRowInputs rep role cost effective peer i u) (readMatchingCandidate cutAt s i)) ∧
      ∀ i < k*k, MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i =
        insertSlackCandidates (growthSourcePairInputs rep role cost effective (s.rr 15) peer i u)
          (readMatchingPairBucket (k := k) s i) := by
  let loaded := {s with
    pc := 3
    nr := Function.update (Function.update (Function.update s.nr 15 u.val) 6 (s.nr 57 + u.val)) 17 (rep u).val}
  have load : BlockRuns readGrowthCacheSource 3 s loaded := by
    simpa [loaded, source, zero, input.representatives u] using readGrowthCacheSource_spec s entry running
  let a := {loaded with pc := 0}
  have aReg (r : ℕ) (safe : r ∉ [6, 15, 17] := by decide) : a.nr r = s.nr r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at safe
    simp [a, loaded, safe.1, safe.2.1, safe.2.2]
  have code : a.nr 17 = (rep u).val := by simp [a, loaded]
  have peerCode : a.nr 26 = peer.val := (aReg 26).trans outer
  have aTables (r : ℕ) (table : r ∈ matchingRefreshTableRegisters) : a.nr r = s.nr r :=
    aReg r (by simp [matchingRefreshTableRegisters] at table; simp; omega)
  have aInput : MatchingRefreshInput a rep role cost effective := input.keeps
    ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ aTables
  obtain ⟨rowStable, pairStable⟩ := matchingCacheReads_unchanged cutAt (m := s) (t := a) rfl rfl aTables
  have aRows (i : ℕ) (within : i < a.nr 61) : MatchingCandidateRowValid cutAt a i := by
    rw [(rowStable i).1]
    exact rows i (aReg 61 ▸ within)
  have aPairs (i : ℕ) (within : i < k*k) : MatchingPairBucketValid k a i := by
    rw [(pairStable i).1]
    exact buckets i within
  have finishSkip (rejected : rep u ≠ peer) {ticks : ℕ}
      (skip : BlockRuns refreshGrowthCacheSourceBlock ticks s
        (relocateState readGrowthCacheSource.length {a with pc := (branchOnAtMost 17 26
          (branchOnAtMost 26 17 selectedGrowthCacheSource []) []).length})) (bound : ticks ≤ 98 * k + 10) :
      ∃ t steps, BlockRuns refreshGrowthCacheSourceBlock steps s t ∧ t.halted = false ∧ steps ≤ 98 * k + 10 ∧
        MatchingRefreshInput t rep role cost effective ∧ MatchingCacheFootprint k s t ∧ t.rr 15 = s.rr 15 ∧
        (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i =
          insertSlackCandidates (growthSourceRowInputs rep role cost effective peer i u) (readMatchingCandidate cutAt s i)) ∧
        ∀ i < k*k, MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i =
          insertSlackCandidates (growthSourcePairInputs rep role cost effective (s.rr 15) peer i u)
            (readMatchingPairBucket (k := k) s i) := by
    refine ⟨_, ticks, skip, running, bound, ?_, MatchingCacheFootprint.unchanged rfl rfl, rfl, ?_, ?_⟩
    · exact aInput.keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
    · intro i hi
      change MatchingCandidateRowValid cutAt a i ∧ readMatchingCandidate cutAt a i = _
      exact ⟨aRows i ((aReg 61).symm ▸ hi), by simpa [growthSourceRowInputs, rejected, insertSlackCandidates] using (rowStable i).2⟩
    · intro i hi
      change MatchingPairBucketValid k a i ∧ readMatchingPairBucket (k := k) a i = _
      exact ⟨aPairs i hi, by simpa [growthSourcePairInputs, rejected, insertSlackCandidates] using (pairStable i).2⟩
  by_cases upper : a.nr 17 ≤ a.nr 26
  · by_cases lower : a.nr 26 ≤ a.nr 17
    · have selected : rep u = peer := Fin.ext (code.symm.trans ((Nat.le_antisymm upper lower).trans peerCode))
      let seeded := {a with pc := 1, nr := Function.update a.nr 27 (a.nr 27 + 1)}
      have bump : BlockRuns [.natAdd 27 27 9] 1 a seeded := by
        apply BlockRuns.of_running_exit
        · simp [seeded, a, loaded, arithmeticStep, running, one]
        · exact running
        · rfl
      let start := {seeded with pc := 0}
      have startReg (r : ℕ) (safe : r ≠ 27 := by decide) : start.nr r = a.nr r := by
        simp only [start, seeded, Function.update_of_ne safe]
      have startPorts (r : ℕ) (table : r ∈ matchingRefreshTableRegisters) : start.nr r = s.nr r :=
        (startReg r (by simp [matchingRefreshTableRegisters] at table; omega)).trans (aTables r table)
      have startInput : MatchingRefreshInput start rep role cost effective := input.keeps
        ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ startPorts
      obtain ⟨keepRows, keepPairs⟩ := matchingCacheReads_unchanged cutAt (m := s) (t := start) rfl rfl startPorts
      have startOne := (startReg 9).trans ((aReg 9).trans one)
      have startZero := (startReg 14).trans ((aReg 14).trans zero)
      have startSource : start.nr 26 = (rep u).val := (startReg 26).trans (peerCode.trans (congrArg Fin.val selected.symm))
      have startOrigin : start.nr 15 = u.val := by simp [start, seeded, a, loaded]
      have readyRows (i : ℕ) (within : i < start.nr 61) : MatchingCandidateRowValid cutAt start i := by
        rw [(keepRows i).1]
        exact rows i (startPorts 61 (by decide) ▸ within)
      have readyPairs (i : ℕ) (within : i < k*k) : MatchingPairBucketValid k start i := by
        rw [(keepPairs i).1]
        exact buckets i within
      obtain ⟨b, ticks, cost, scan, live, _, time, finalInput, newRows, newPairs⟩ :=
        refreshSelectedOuterVertex_rows cutAt (s := start) (u := u) rfl running startOne startZero startInput
          startOrigin startSource readyRows readyPairs
      have offsets : MatchingCacheOffsets k start := ⟨fun i hi => by have h := startInput.offsetsBefore; omega,
        fun i hi => startInput.offsets ⟨i, hi⟩⟩
      have reps : MatchingCacheRepresentatives k start := ⟨fun i hi => by have h := startInput.representativesBefore; omega,
        fun i hi => by rw [startInput.representatives ⟨i, hi⟩]; exact (rep ⟨i, hi⟩).isLt⟩
      obtain ⟨c, steps, checked, _, _, footprint⟩ := refreshSelectedOuterVertex_footprint (s := start)
        rfl running startOne startZero startInput.layout offsets reps (by rw [startSource]; exact (rep u).isLt)
      have same := (checked.same_exit scan).2
      subst c
      have space := (MatchingCacheFootprint.unchanged (k := k) (s := s) (t := start) rfl rfl).chain footprint
        (fun r h => startPorts r (by simp [matchingRefreshTableRegisters] at h ⊢; omega))
      have inside := branchOnAtMost_left 26 17 selectedGrowthCacheSource [] (s := a) rfl running lower (bump.append scan) live
      have outside := branchOnAtMost_left 17 26 _ [] (s := a) rfl running upper inside live
      refine ⟨_, _, load.append outside, live, by omega, ?_, ⟨space.natural, space.real⟩, time, ?_, ?_⟩
      · exact finalInput.keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
      · intro i hi
        change MatchingCandidateRowValid cutAt b i ∧ readMatchingCandidate cutAt b i = _
        have within : i < start.nr 61 := (startPorts 61 (by decide)).symm ▸ hi
        simpa only [growthSourceRowInputs, if_pos selected, (keepRows i).2] using newRows i within
      · intro i hi
        change MatchingPairBucketValid k b i ∧ readMatchingPairBucket (k := k) b i = _
        simpa only [growthSourcePairInputs, if_pos selected, (keepPairs i).2,
          show start.rr 15 = s.rr 15 from rfl] using newPairs i hi
    · have skip : BlockRuns [] 0 a a := BlockRuns.of_running_exit rfl running rfl
      have inside := branchOnAtMost_right 26 17 selectedGrowthCacheSource [] (s := a) rfl running
        (Nat.lt_of_not_ge lower) skip running
      have outside := branchOnAtMost_left 17 26 _ [] (s := a) rfl running upper inside running
      exact finishSkip (fun h => lower (by rw [code, peerCode, h])) (load.append outside) (by omega)
  · have skip : BlockRuns [] 0 a a := BlockRuns.of_running_exit rfl running rfl
    have outside := branchOnAtMost_right 17 26 (branchOnAtMost 26 17 selectedGrowthCacheSource []) []
      (s := a) rfl running (Nat.lt_of_not_ge upper) skip running
    exact finishSkip (fun h => upper (by rw [code, peerCode, h])) (load.append outside) (by omega)

private theorem growthRefresh_fold_succ {k : ℕ} {Event : Type*}
    (inputs : Fin k → List (DualSlack Event)) (old : Option (DualSlack Event)) (i : ℕ) (hi : i < k) :
    insertSlackCandidates (((List.finRange k).take (i+1)).flatMap inputs) old =
      insertSlackCandidates (inputs ⟨i, hi⟩) (insertSlackCandidates (((List.finRange k).take i).flatMap inputs) old) := by
  have within : i < (List.finRange k).length := by simpa using hi
  rw [List.take_succ_eq_append_getElem within, List.getElem_finRange, List.flatMap_append]
  simp [insertSlackCandidates, List.foldl_append]

private structure GrowthRefreshProgress {k : ℕ} (cutAt : Fin k → Finset (Fin k)) (s : ArithmeticState)
    (rep : Fin k → Fin k) (role : Fin k → ℕ) (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ)
    (peer : Fin k) (seen : ℕ) (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  live : m.halted = false
  index : m.nr 24 = seen
  one : m.nr 9 = 1
  zero : m.nr 14 = 0
  outer : m.nr 26 = peer.val
  time : m.rr 15 = s.rr 15
  bases : ∀ r ∈ [58, 59, 65, 66], m.nr r = s.nr r
  input : MatchingRefreshInput m rep role cost effective
  footprint : MatchingCacheFootprint k s m
  rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt m i ∧ readMatchingCandidate cutAt m i =
    insertSlackCandidates (((List.finRange k).take seen).flatMap (growthSourceRowInputs rep role cost effective peer i))
      (readMatchingCandidate cutAt s i)
  buckets : ∀ i < k*k, MatchingPairBucketValid k m i ∧ readMatchingPairBucket (k := k) m i =
    insertSlackCandidates (((List.finRange k).take seen).flatMap (growthSourcePairInputs rep role cost effective (s.rr 15) peer i))
      (readMatchingPairBucket (k := k) s i)

set_option maxRecDepth 8192 in
/-- The complete promotion sweep inserts precisely the candidates from the
new outer block and keeps the exact existing instruction bound. -/
theorem refreshMatchingNewOuterBlock_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} {rep : Fin k → Fin k} {role : Fin k → ℕ}
    {cost : Fin k → Fin k → ℝ} {effective : Fin k → ℝ} {peer : Fin k}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (input : MatchingRefreshInput s rep role cost effective) (outer : s.nr 26 = peer.val)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k*k, MatchingPairBucketValid k s i) :
    ∃ t ticks, BlockRuns refreshMatchingNewOuterBlock ticks s t ∧ t.halted = false ∧
      t.nr 27 = matchingGrowthMembers s k ∧ ticks ≤ 11*k + (k*98+2)*t.nr 27 + 3 ∧
      MatchingRefreshInput t rep role cost effective ∧ MatchingCacheFootprint k s t ∧ t.rr 15 = s.rr 15 ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i =
        insertSlackCandidates ((List.finRange k).flatMap (growthSourceRowInputs rep role cost effective peer i))
          (readMatchingCandidate cutAt s i)) ∧
      ∀ i < k*k, MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i =
        insertSlackCandidates ((List.finRange k).flatMap (growthSourcePairInputs rep role cost effective (s.rr 15) peer i))
          (readMatchingPairBucket (k := k) s i) := by
  let inv := GrowthRefreshProgress cutAt s rep role cost effective peer
  let seeded := {s with pc := 2, nr := Function.update (Function.update s.nr 24 0) 27 0}
  let start := {seeded with pc := 0}
  have seed : BlockRuns initGrowthCacheScan 2 s seeded := by
    apply BlockRuns.of_running_exit
    · simp [initGrowthCacheScan, seeded, arithmeticStep, entry, running, Function.iterate_succ_apply']
    · exact running
    · rfl
  have seedRegisters (r : ℕ) (safe : r ≠ 24) (away : r ≠ 27) : start.nr r = s.nr r :=
    (Function.update_of_ne away _ _).trans (Function.update_of_ne safe _ _)
  have seedTables (r : ℕ) (used : r ∈ matchingRefreshTableRegisters) : start.nr r = s.nr r :=
    seedRegisters r (by simp [matchingRefreshTableRegisters] at used; omega)
      (by simp [matchingRefreshTableRegisters] at used; omega)
  obtain ⟨stableRows, stablePairs⟩ := matchingCacheReads_unchanged cutAt (m := s) (t := start) rfl rfl seedTables
  have initial : inv 0 start := by
    refine ⟨rfl, running, by simp [start, seeded], one, zero, outer, rfl, ?_,
      input.keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ seedTables, .unchanged rfl rfl, ?_, ?_⟩
    · intro r h
      exact seedTables r (by simp [matchingRefreshTableRegisters] at h ⊢; omega)
    · intro i hi
      exact ⟨(stableRows i).1.symm ▸ rows i hi, by simpa [insertSlackCandidates] using (stableRows i).2⟩
    · intro i hi
      exact ⟨(stablePairs i).1.symm ▸ buckets i hi, by simpa [insertSlackCandidates] using (stablePairs i).2⟩
  have control (i : ℕ) (m : ArithmeticState) (h : inv i m) : m.pc = 0 ∧ m.halted = false ∧
      m.nr 24 = i ∧ m.nr 55 = k := ⟨h.entry, h.live, h.index, h.input.layout.dimension⟩
  have step (i : ℕ) (hi : i < k) (m : ArithmeticState) (h : inv i m) :
      ∃ t ticks, ticks ≤ 98*k+10 ∧ BlockRuns refreshGrowthCacheSourceBlock ticks m t ∧ t.halted = false ∧
        inv (i+1) {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)} := by
    let u : Fin k := ⟨i, hi⟩
    have rowsSame : m.nr 61 = s.nr 61 := h.input.layout.rows.trans input.layout.rows.symm
    obtain ⟨t, ticks, ran, live, cost, reads, frame, time, rowEffect, pairEffect⟩ :=
      refreshGrowthCacheSourceBlock_rows cutAt (s := m) (u := u) h.entry h.live h.one h.zero h.input h.index h.outer
        (fun j hj => (h.rows j (rowsSame ▸ hj)).1) (fun j hj => (h.buckets j hj).1)
    let next := {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)}
    have preserves (r : ℕ) (safe : r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 25, 27] := by decide) : t.nr r = m.nr r := by
      rw [← ran.run]
      exact arithmeticRun_keeps_register (growthCacheSourceBlock_no_write safe) m ticks
    have nextTables (r : ℕ) (used : r ∈ matchingRefreshTableRegisters) : next.nr r = t.nr r :=
      Function.update_of_ne (by simp [matchingRefreshTableRegisters] at used; omega) _ _
    have sameTables (r : ℕ) (used : r ∈ matchingRefreshTableRegisters) : m.nr r = t.nr r :=
      (preserves r (by simp [matchingRefreshTableRegisters] at used; simp; omega)).symm
    obtain ⟨sameRows, sameBuckets⟩ := matchingCacheReads_unchanged cutAt (m := t) (t := next) rfl rfl nextTables
    refine ⟨t, ticks, cost, ran, live, ⟨rfl, live, ?_, ?_, ?_, ?_, time.trans h.time, ?_,
      reads.keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ nextTables,
      h.footprint.chain ⟨frame.natural, frame.real⟩ h.bases, ?_, ?_⟩⟩
    · simp [next, preserves 24, preserves 9, h.index, h.one]
    · simpa [next, preserves 9] using h.one
    · simpa [next, preserves 14] using h.zero
    · simpa [next, preserves 26] using h.outer
    · intro r hr
      have member : r ∈ matchingRefreshTableRegisters := by simp [matchingRefreshTableRegisters] at hr ⊢; omega
      exact (nextTables r member).trans ((sameTables r member).symm.trans (h.bases r hr))
    · intro j hj
      obtain ⟨valid, result⟩ := rowEffect j (rowsSame.symm ▸ hj)
      refine ⟨(sameRows j).1.symm ▸ valid, ?_⟩
      rw [(sameRows j).2, result, (h.rows j hj).2, growthRefresh_fold_succ _ _ i hi]
    · intro j hj
      obtain ⟨valid, result⟩ := pairEffect j hj
      refine ⟨(sameBuckets j).1.symm ▸ valid, ?_⟩
      rw [(sameBuckets j).2, result, h.time, (h.buckets j hj).2, growthRefresh_fold_succ _ _ i hi]
  obtain ⟨last, actual, finished, _, sweep⟩ := countedLoop_bounded 9 24 55 k (98*k+10) refreshGrowthCacheSourceBlock
    inv initial control step
  let t := relocateState initGrowthCacheScan.length {last with pc := (countedLoop 9 24 55 refreshGrowthCacheSourceBlock).length}
  have ran : BlockRuns refreshMatchingNewOuterBlock (2 + actual) s t := seed.append sweep
  have ids := input.layout.idsBefore
  have endpoints := input.layout.recordsBefore
  have exactDim := input.layout.dimension
  obtain ⟨q, qTicks, qRun, _, counts, cost, _, _⟩ := refreshMatchingNewOuterBlock_bound s entry running one zero
    (by omega) (by omega) (by rw [exactDim]; exact input.representativesBefore)
  obtain ⟨equalTime, equalExit⟩ := qRun.same_exit ran
  rw [equalExit, exactDim] at counts
  rw [equalTime, equalExit, exactDim] at cost
  have all : (List.finRange k).take k = List.finRange k := by simp
  refine ⟨t, 2+actual, ran, finished.live, counts, cost, ?_, ?_, finished.time, ?_, ?_⟩
  · exact finished.input.keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
  · exact ⟨finished.footprint.natural, finished.footprint.real⟩
  · intro i hi
    change MatchingCandidateRowValid cutAt last i ∧ readMatchingCandidate cutAt last i = _
    simpa only [all] using finished.rows i hi
  · intro i hi
    change MatchingPairBucketValid k last i ∧ readMatchingPairBucket (k := k) last i = _
    simpa only [all] using finished.buckets i hi


end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowthRefresh

/-! matching/MatchingGrowthIncomingRows.lean -/
section RppSource_MatchingGrowthIncomingRows
namespace VehicleRoutingSurvey.Routing

abbrev MatchingGrowthIncomingAt (s : ArithmeticState) (rep slot : ℕ) : Prop :=
  ∃ v < s.nr 55, slot = s.nr 55 + v ∧ s.nm (s.nr 57 + v) = rep

open Classical in
/-- The actual growth pass clears incoming rows of the promoted originals. It
keeps the same witness and slack for a newly inner original and sets its rate
to zero. Cut rows, outer rows, and directed buckets remain intact. -/
theorem rerateGrowthIncomingBlock_rows {k : ℕ} {s : ArithmeticState}
    (cutAt : Fin k → Finset (Fin k)) (layout : MatchingCacheLayout k s)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (separate : s.nr 57 + s.nr 55 ≤ s.nr 58) (distinct : s.nr 26 ≠ s.nr 28)
    (valid : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i) :
    ∃ t steps, steps ≤ 14 * k + 2 ∧ BlockRuns rerateGrowthIncomingBlock steps s t ∧ t.halted = false ∧
      MatchingCacheFootprint k s t ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i =
        if MatchingGrowthIncomingAt s (s.nr 26) i then none else
          (readMatchingCandidate cutAt s i).map (fun d =>
            {d with rate := if MatchingGrowthIncomingAt s (s.nr 28) i then 0 else d.rate})) ∧
      ∀ i < k * k, (MatchingPairBucketValid k t i ↔ MatchingPairBucketValid k s i) ∧
        readMatchingPairBucket (k := k) t i = readMatchingPairBucket s i := by
  classical
  obtain ⟨t, steps, cost, ran, live, natural, real⟩ := rerateGrowthIncomingBlock_correct s entry running one zero separate
  have kept (r : ℕ) (safe : r ∉ [0, 6, 7, 10, 11] := by decide) : t.nr r = s.nr r :=
    rerateGrowthIncoming_keeps_register ran safe
  have dimension := layout.dimension
  have count := layout.rows
  have ids := layout.idsBefore
  have records := layout.recordsBefore
  have slacks := layout.slacksBefore
  have rates := layout.ratesBefore
  have words (a : ℕ) (outside : a < s.nr 58 ∨ s.nr 54 ≤ a) : t.nm a = s.nm a := by
    rw [natural, if_neg]
    rintro ⟨v, within, address, _⟩
    omega
  have scores (a : ℕ) (outside : a < s.nr 60 ∨ s.nr 66 ≤ a) : t.rm a = s.rm a := by
    rw [real, if_neg]
    rintro ⟨v, within, address, _⟩
    omega
  have dictionary (id : ℕ) : decodeMatchingDictionaryEvent k cutAt t id = decodeMatchingDictionaryEvent k cutAt s id := by
    unfold decodeMatchingDictionaryEvent
    rw [kept 54]
    simp only [words _ (Or.inr (by omega : s.nr 54 ≤ s.nr 54 + ((id - 1) + (id - 1)))),
      words _ (Or.inr (by omega : s.nr 54 ≤ s.nr 54 + ((id - 1) + (id - 1)) + 1))]
  have identifier (i : ℕ) : t.nm (t.nr 58 + i) =
      if MatchingGrowthIncomingAt s (s.nr 26) i then 0 else s.nm (s.nr 58 + i) := by
    rw [kept 58, natural]
    simp only [MatchingGrowthIncomingAt, Nat.add_left_cancel_iff]
  have newRate (i : ℕ) : t.rm (t.nr 60 + i) =
      if MatchingGrowthIncomingAt s (s.nr 28) i then 0 else s.rm (s.nr 60 + i) := by
    rw [kept 60, real]
    simp only [MatchingGrowthIncomingAt, Nat.add_left_cancel_iff]
    have same : (∃ j < s.nr 55, i = s.nr 55 + j ∧ s.nm (s.nr 57 + j) ≠ s.nr 26 ∧
        s.nm (s.nr 57 + j) = s.nr 28) ↔ ∃ j < s.nr 55, i = s.nr 55 + j ∧ s.nm (s.nr 57 + j) = s.nr 28 := by
      constructor
      · rintro ⟨j, hj, eq, _, role⟩
        exact ⟨j, hj, eq, role⟩
      · rintro ⟨j, hj, eq, role⟩
        exact ⟨j, hj, eq, role.trans_ne (Ne.symm distinct), role⟩
    by_cases selected : ∃ j < s.nr 55, i = s.nr 55 + j ∧ s.nm (s.nr 57 + j) = s.nr 28
    · simp only [if_pos selected, if_pos (same.mpr selected)]
    · simp only [if_neg selected, if_neg (fun h => selected (same.mp h))]
  refine ⟨t, steps, ?_, ran, live, ?_, ?_, ?_⟩
  · simpa only [dimension, Nat.mul_comm k 14] using cost
  · exact ⟨fun a outside => words a (by omega), fun a outside => scores a (by omega)⟩
  · intro i within
    have keptSlack : t.rm (t.nr 59 + i) = s.rm (s.nr 59 + i) := by rw [kept 59, scores _ (Or.inl (by omega))]
    by_cases erase : MatchingGrowthIncomingAt s (s.nr 26) i
    · have empty := (identifier i).trans (if_pos erase)
      exact ⟨Or.inl empty, by simp [readMatchingCandidate, empty, erase, decodeMatchingDictionaryEvent]⟩
    · have same := (identifier i).trans (if_neg erase)
      refine ⟨by simpa only [MatchingCandidateRowValid, same, dictionary] using valid i within, ?_⟩
      simp [readMatchingCandidate, erase, same, dictionary, keptSlack, newRate, Option.map_map, Function.comp_def]
  · intro i _
    have first := words (s.nr 65 + (i + i)) (Or.inr (by omega))
    have last := words (s.nr 65 + (i + i) + 1) (Or.inr (by omega))
    have key := scores (s.nr 66 + i) (Or.inr (by omega))
    simp only [MatchingPairBucketValid, readMatchingPairBucket, kept 65, kept 66, first, last, key, and_self]


end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowthIncomingRows

/-! matching/MatchingGrowthCutRows.lean -/
section RppSource_MatchingGrowthCutRows
namespace VehicleRoutingSurvey.Routing

/-- Growth makes the newly inner base eligible for a cut event precisely when
its block has a registered blossom. All other decoded rows and pair buckets
retain their values. -/
theorem activateMatchingInnerCut_rows {k : ℕ} {s : ArithmeticState} {v : Fin k}
    (cutAt : Fin k → Finset (Fin k)) (layout : MatchingCacheLayout k s)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (index : s.nr 28 = v.val) (valid : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i) :
    let slot := 2*k + v.val
    let candidate : Option (DualSlack (MatchingDualEvent k)) := if matchingInnerNode s = 0 then none
      else some ⟨.cut (cutAt v), s.rm (s.nr 75 + matchingInnerNode s), 1⟩
    ∃ t steps, steps ≤ 22 ∧ BlockRuns activateMatchingInnerCut steps s t ∧ t.halted = false ∧
      MatchingCacheFootprint k s t ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i =
        if i = slot then candidate else readMatchingCandidate cutAt s i) ∧
      ∀ i < k*k, (MatchingPairBucketValid k t i ↔ MatchingPairBucketValid k s i) ∧
        readMatchingPairBucket (k := k) t i = readMatchingPairBucket s i := by
  intro slot candidate
  let addr (i : ℕ) := s.nr 54 + (i+i)
  let value := s.rm (s.nr 75 + matchingInnerNode s)
  obtain ⟨t, steps, cost, run, live, natural, real⟩ := activateMatchingInnerCut_spec s entry running one zero
  have fixed (r : ℕ) (safe : r ∉ [0, 6, 10, 15, 16, 18] := by decide) : t.nr r = s.nr r :=
    activateMatchingInnerCut_keeps_register run safe
  have vp := v.isLt
  have inside : slot < s.nr 61 := by rw [layout.rows]; dsimp [slot]; omega
  have pos : innerCutCandidateSlot s = slot := by rw [innerCutCandidateSlot, layout.dimension, index]; dsimp [slot]; omega
  have ids := layout.idsBefore
  have records := layout.recordsBefore
  have slacks := layout.slacksBefore
  have rates := layout.ratesBefore
  have natWords : t.nm = if matchingInnerNode s = 0 then Function.update s.nm (s.nr 58 + slot) 0 else
      Function.update (Function.update (Function.update s.nm (s.nr 58 + slot) (slot+1)) (addr slot) v.val)
        (addr slot+1) k := by
    rw [natural, installedMatchingInnerCutNat]
    split
    · rw [pos]
    · change Function.update (Function.update (Function.update s.nm (s.nr 58 + innerCutCandidateSlot s)
        (innerCutCandidateSlot s+1)) (addr (innerCutCandidateSlot s)) (s.nr 28))
        (addr (innerCutCandidateSlot s)+1) (s.nr 55) = _
      rw [pos, index, layout.dimension]
  have realWords : t.rm = if matchingInnerNode s = 0 then s.rm else
      Function.update (Function.update s.rm (s.nr 59 + slot) value) (s.nr 60 + slot) 1 := by
    rw [real, installedMatchingInnerCutReal]
    split
    · rfl
    · change Function.update (Function.update s.rm (s.nr 59 + innerCutCandidateSlot s) value)
        (s.nr 60 + innerCutCandidateSlot s) 1 = _
      rw [pos]
  have words (a : ℕ) (id : a ≠ s.nr 58 + slot) (first : a ≠ addr slot) (last : a ≠ addr slot+1) :
      t.nm a = s.nm a := by
    rw [natWords]
    split <;> simp only [Function.update_of_ne id, Function.update_of_ne first, Function.update_of_ne last]
  have scores (a : ℕ) (score : a ≠ s.nr 59 + slot) (rate : a ≠ s.nr 60 + slot) : t.rm a = s.rm a := by
    rw [realWords]
    split <;> simp only [Function.update_of_ne score, Function.update_of_ne rate]
  have before (a : ℕ) (outside : a < s.nr 58 ∨ s.nr 65 ≤ a) : t.nm a = s.nm a :=
    words a (by omega) (by dsimp [addr]; omega) (by dsimp [addr]; omega)
  have prior (a : ℕ) (outside : a < s.nr 59 ∨ s.nr 66 ≤ a) : t.rm a = s.rm a :=
    scores a (by omega) (by omega)
  refine ⟨t, steps, cost, run, live, ⟨fun a h => before a (by omega), fun a h => prior a (by omega)⟩, ?_, ?_⟩
  · intro i hi
    by_cases same : i = slot
    · subst i
      rw [if_pos rfl]
      by_cases empty : matchingInnerNode s = 0
      · have id : t.nm (t.nr 58 + slot) = 0 := by rw [fixed 58, natWords, if_pos empty]; simp
        exact ⟨Or.inl id, by simp [readMatchingCandidate, id, decodeMatchingDictionaryEvent, candidate, empty]⟩
      have id : t.nm (t.nr 58 + slot) = slot+1 := by
        rw [fixed 58, natWords, if_neg empty]
        simp (disch := omega) [addr, Function.update_of_ne]
      have first : t.nm (t.nr 54 + (slot+slot)) = v.val := by
        rw [fixed 54, natWords, if_neg empty]
        simp (disch := omega) [addr, Function.update_of_ne]
      have last : t.nm (t.nr 54 + (slot+slot) + 1) = k := by rw [fixed 54, natWords, if_neg empty]; simp [addr]
      have item : decodeMatchingDictionaryEvent k cutAt t (slot+1) = some (.cut (cutAt v)) := by
        simp [decodeMatchingDictionaryEvent, first, last, vp]
      have score : t.rm (t.nr 59+slot) = value := by
        rw [fixed 59, realWords, if_neg empty]; simp (disch := omega) [Function.update_of_ne]
      have rate : t.rm (t.nr 60+slot) = 1 := by rw [fixed 60, realWords, if_neg empty]; simp
      exact ⟨Or.inr ⟨id, _, id ▸ item⟩, by simp [candidate, empty, readMatchingCandidate, id, item, score, rate, value]⟩
    · have id : t.nm (t.nr 58+i) = s.nm (s.nr 58+i) := by
        rw [fixed 58]; exact words _ (by omega) (by dsimp [addr]; omega) (by dsimp [addr]; omega)
      have first := words (addr i) (by dsimp [addr]; omega) (by dsimp [addr]; omega) (by dsimp [addr]; omega)
      have last := words (addr i+1) (by dsimp [addr]; omega) (by dsimp [addr]; omega) (by dsimp [addr]; omega)
      have event : decodeMatchingDictionaryEvent k cutAt t (s.nm (s.nr 58+i)) =
          decodeMatchingDictionaryEvent k cutAt s (s.nm (s.nr 58+i)) := by
        rcases valid i hi with absent | ⟨own, _, _⟩
        · simp [absent, decodeMatchingDictionaryEvent]
        · dsimp [addr] at first last
          simp [own, decodeMatchingDictionaryEvent, fixed 54, first, last]
      have score := scores (s.nr 59+i) (by omega) (by omega)
      have rate := scores (s.nr 60+i) (by omega) (by omega)
      exact ⟨by simpa only [MatchingCandidateRowValid, id, event] using valid i hi,
        by simp only [if_neg same, readMatchingCandidate, id, event, fixed 59, fixed 60, score, rate]⟩
  · intro i _
    have first := before (s.nr 65+(i+i)) (Or.inr (by omega))
    have last := before (s.nr 65+(i+i)+1) (Or.inr (by omega))
    have key := prior (s.nr 66+i) (Or.inr (by omega))
    simp only [MatchingPairBucketValid, readMatchingPairBucket, fixed 65, fixed 66, first, last, key, and_self]


end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowthCutRows

/-! matching/MatchingGrowthCacheRepair.lean -/
section RppSource_MatchingGrowthCacheRepair
namespace VehicleRoutingSurvey.Routing

/-- The suffix of the growth handler after it saves its two new base indices. -/
def matchingGrowthCacheRepairBlock : List ArithmeticInstruction :=
  appendBlock rerateGrowthIncomingBlock (appendBlock activateMatchingInnerCut
    (appendBlock refreshMatchingNewOuterBlock resetMatchingSelector))

open Classical in
noncomputable def growthRepairSeed {k : ℕ} (cutAt : Fin k → Finset (Fin k)) (s : ArithmeticState)
    (target : Fin k) (i : ℕ) : Option (DualSlack (MatchingDualEvent k)) :=
  if i = 2*k+target.val then
    if matchingInnerNode s = 0 then none else some ⟨.cut (cutAt target), s.rm (s.nr 75 + matchingInnerNode s), 1⟩
  else if MatchingGrowthIncomingAt s (s.nr 26) i then none else
    (readMatchingCandidate cutAt s i).map (fun d => {d with rate := if MatchingGrowthIncomingAt s (s.nr 28) i then 0 else d.rate})

set_option maxRecDepth 8192 in
/-- The executable rerating, cut installation, promotion sweep and selector
reset compute one exact set of rows and pair buckets in the charged time. -/
theorem matchingGrowthCacheRepairBlock_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} {rep : Fin k → Fin k} {role : Fin k → ℕ}
    {cost : Fin k → Fin k → ℝ} {eff : Fin k → ℝ} {target peer : Fin k}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (input : MatchingRefreshInput s rep role cost eff) (targetId : s.nr 28 = target.val)
    (peerId : s.nr 26 = peer.val) (distinct : target ≠ peer)
    (nodes : s.nr 65 + 2*(k*k) ≤ s.nr 74) (duals : s.nr 66+k*k ≤ s.nr 75)
    (valid : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (pairs : ∀ i < k*k, MatchingPairBucketValid k s i) :
    ∃ t ticks, BlockRuns matchingGrowthCacheRepairBlock ticks s t ∧ t.halted = false ∧
      ticks ≤ 25*k + (k*98+2)*matchingGrowthMembers s k + 32 ∧
      t.nr 1 = 0 ∧ t.nr 3 = t.nr 58 ∧ t.nr 4 = t.nr 59 ∧ t.nr 5 = t.nr 60 ∧ t.nr 8 = t.nr 61 ∧
      MatchingRefreshInput t rep role cost eff ∧ MatchingCacheFootprint k s t ∧ t.rr 15 = s.rr 15 ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i =
        insertSlackCandidates ((List.finRange k).flatMap (growthSourceRowInputs rep role cost eff peer i))
          (growthRepairSeed cutAt s target i)) ∧
      ∀ i < k*k, MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i =
        insertSlackCandidates ((List.finRange k).flatMap (growthSourcePairInputs rep role cost eff (s.rr 15) peer i))
          (readMatchingPairBucket (k := k) s i) := by
  classical
  have diff : s.nr 26 ≠ s.nr 28 := fun eq => distinct (Fin.ext (targetId.symm.trans (eq.symm.trans peerId)))
  obtain ⟨rated, rt, rtBound, rates, rLive, rFrame, rRows, rPairs⟩ :=
    rerateGrowthIncomingBlock_rows cutAt input.layout entry running one zero
      (by rw [input.layout.dimension]; exact input.representativesBefore) diff valid
  let b := {rated with pc := 0}
  have rPort (r : ℕ) (safe : r ∉ [0,6,7,10,11] := by decide) : b.nr r = s.nr r := by
    change rated.nr r = s.nr r
    exact rerateGrowthIncoming_keeps_register rates safe
  have rTables (r : ℕ) (table : r ∈ matchingRefreshTableRegisters) : b.nr r = s.nr r :=
    rPort r (by simp [matchingRefreshTableRegisters] at table; simp; omega)
  have bInput := input.keeps (t := b) ⟨fun a h => rFrame.natural a (.inl h), fun a h _ _ => rFrame.real a (.inl h)⟩ rTables
  have bTarget := (rPort 28).trans targetId
  have bNode : matchingInnerNode b = matchingInnerNode s := by
    unfold matchingInnerNode
    rw [rPort 74, rPort 28]
    exact rFrame.natural _ (.inr (by omega))
  have bValue : b.rm (b.nr 75 + matchingInnerNode b) = s.rm (s.nr 75 + matchingInnerNode s) := by
    rw [rPort 75, bNode]
    exact rFrame.real _ (.inr (by omega))
  obtain ⟨cut, ct, ctBound, cuts, cLive, cFrame, cRows, cPairs⟩ :=
    activateMatchingInnerCut_rows cutAt bInput.layout rfl rLive ((rPort 9).trans one) ((rPort 14).trans zero)
      bTarget (fun i hi => (rRows i (rPort 61 ▸ hi)).1)
  let c := {cut with pc := 0}
  have cPort (r : ℕ) (safe : r ∉ [0,6,10,15,16,18] := by decide) : c.nr r = b.nr r := by
    change cut.nr r = b.nr r
    exact activateMatchingInnerCut_keeps_register cuts safe
  have cTables (r : ℕ) (table : r ∈ matchingRefreshTableRegisters) : c.nr r = b.nr r :=
    cPort r (by simp [matchingRefreshTableRegisters] at table; simp; omega)
  have cInput := bInput.keeps (t := c) ⟨fun a h => cFrame.natural a (.inl h), fun a h _ _ => cFrame.real a (.inl h)⟩ cTables
  have cCount : c.nr 61 = s.nr 61 := (cPort 61).trans (rPort 61)
  have cPeer := (cPort 26).trans ((rPort 26).trans peerId)
  have cSeed (i : ℕ) (hi : i < s.nr 61) : readMatchingCandidate cutAt c i = growthRepairSeed cutAt s target i := by
    have read := (cRows i ((rPort 61).symm ▸ hi)).2
    change readMatchingCandidate cutAt cut i = _
    rw [read, bValue, bNode, growthRepairSeed]
    by_cases changed : i = 2*k+target.val
    · simp only [if_pos changed]
    · simp only [if_neg changed]
      exact (rRows i hi).2
  have bucket (i : ℕ) (hi : i < k*k) : readMatchingPairBucket (k := k) c i = readMatchingPairBucket s i :=
    (cPairs i hi).2.trans (rPairs i hi).2
  obtain ⟨scan, st, scanRun, scanLive, srcCount, stBound, sInput, sFrame, _, rows, buckets⟩ :=
    refreshMatchingNewOuterBlock_rows cutAt (s := c) rfl cLive ((cPort 9).trans ((rPort 9).trans one))
      ((cPort 14).trans ((rPort 14).trans zero)) cInput cPeer
      (fun i hi => (cRows i (cPort 61 ▸ hi)).1)
      (fun i hi => (cPairs i hi).1.mpr ((rPairs i hi).1.mpr (pairs i hi)))
  let e := {scan with pc := 0}
  have sPort (r : ℕ) (safe : r ∉ [0,6,10,11,15,16,17,18,19,24,25,27] := by decide) : e.nr r = c.nr r :=
    (show scan.nr r = c.nr r from refreshMatchingNewOuterBlock_keeps scanRun safe)
  have members : matchingGrowthMembers c k = matchingGrowthMembers s k := by
    unfold matchingGrowthMembers
    apply congrArg List.length
    apply List.filter_congr
    intro j hj
    let v : Fin k := ⟨j, List.mem_range.mp hj⟩
    change decide (c.nm (c.nr 57+v.val) = c.nr 26) = decide (s.nm (s.nr 57+v.val) = s.nr 26)
    rw [cInput.representatives v, input.representatives v, cPeer, peerId]
  obtain ⟨t, reset, live, natural, real, empty, idBase, slackBase, rateBase, rowCount⟩ :=
    resetMatchingSelector_spec e rfl scanLive ((sPort 14).trans ((cPort 14).trans ((rPort 14).trans zero)))
  have endPort (r : ℕ) (safe : r ∉ [0,1,3,4,5,8] := by decide) : t.nr r = e.nr r := by
    rw [← reset.run]
    exact arithmeticRun_keeps_from_destination_list [0,1,3,4,5,8] (by decide) safe e 5
  have endTables (r : ℕ) (mem : r ∈ matchingRefreshTableRegisters) : t.nr r = scan.nr r :=
    endPort r (by simp [matchingRefreshTableRegisters] at mem; simp; omega)
  obtain ⟨finalRows, finalPairs⟩ := matchingCacheReads_unchanged cutAt (m := scan) (t := t) natural real endTables
  have frameBC : MatchingCacheFootprint k s c := rFrame.chain ⟨cFrame.natural, cFrame.real⟩ (fun r hr => rPort r (by simp at hr ⊢; omega))
  have frameE : MatchingCacheFootprint k s scan := frameBC.chain sFrame (fun r hr =>
    (cPort r (by simp at hr ⊢; omega)).trans (rPort r (by simp at hr ⊢; omega)))
  let out := relocateState rerateGrowthIncomingBlock.length (relocateState activateMatchingInnerCut.length
    (relocateState refreshMatchingNewOuterBlock.length t))
  have ran : BlockRuns matchingGrowthCacheRepairBlock (rt+(ct+(st+5))) s out := rates.append (cuts.append (scanRun.append reset))
  have clock : c.rr 15 = s.rr 15 := by
    change cut.rr 15 = _
    rw [← cuts.run, arithmeticRun_keeps_real_from_destination_list (p := activateMatchingInnerCut) (r := 15)
      [0,4] (by decide) (by decide) b ct]
    change rated.rr 15 = _
    rw [← rates.run, arithmeticRun_keeps_real_from_destination_list (p := rerateGrowthIncomingBlock) (r := 15)
      [0,2] (by decide) (by decide) s rt]
  have finalClock : out.rr 15 = s.rr 15 := by
    rw [← ran.run]
    exact arithmeticRun_keeps_real_from_destination_list [0,2,3,4,5] (by decide) (by decide) s _
  refine ⟨out, _, ran, live, ?_, empty, idBase.trans (endPort 58).symm, slackBase.trans (endPort 59).symm,
    rateBase.trans (endPort 60).symm, rowCount.trans (endPort 61).symm, ?_, ?_, finalClock, ?_, ?_⟩
  · rw [srcCount, members] at stBound
    omega
  · exact sInput.keeps (t := out) ⟨fun a _ => congrFun natural a, fun a _ _ _ => congrFun real a⟩ endTables
  · exact ⟨fun a h => (congrFun natural a).trans (frameE.natural a h), fun a h => (congrFun real a).trans (frameE.real a h)⟩
  · intro i hi
    change MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i = _
    rw [(finalRows i).1, (finalRows i).2]
    simpa only [cSeed i hi] using rows i (cCount.symm ▸ hi)
  · intro i hi
    change MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i = _
    rw [(finalPairs i).1, (finalPairs i).2]
    simpa only [bucket i hi, clock] using buckets i hi


end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowthCacheRepair

/-! matching/MatchingGrowthCutMeaning.lean -/
section RppSource_MatchingGrowthCutMeaning
namespace VehicleRoutingSurvey.Routing

/-- The program's cut-row replacement exactly implements the role change of
the new inner base. All other cut rows have the same semantic entry. -/
theorem MatchingGrowthSelection.cutEntries {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest recordForest : AlternatingForestState (Fin k)} {s t : ArithmeticState} {edge : Sym2 (Fin k)}
    (chosen : MatchingGrowthSelection part forest s edge)
    (dual : MatchingSearchDualMemory part recordForest t) (index : t.nr 28 = chosen.target.val)
    (cut : Fin k → Finset (Fin k)) (decode : cut chosen.target = part.blocks.block chosen.target)
    (i : Fin k) :
    let newer := forest.grow chosen.source chosen.target chosen.peer
    matchingCutGroupEntry part newer i =
      if i = chosen.target then
        (if matchingInnerNode t = 0 then none else
          some ⟨.cut (cut chosen.target), t.rm (t.nr 75 + matchingInnerNode t), 1⟩)
      else matchingCutGroupEntry part forest i := by
  classical
  intro newer
  by_cases same : i = chosen.target
  · subst i
    rw [if_pos rfl]
    have fixed := (part.mem_activeRepresentatives _).mp chosen.targetActive
    have inner : newer.role chosen.target = .inner chosen.source := by simp [newer, AlternatingForestState.grow]
    have raw : matchingInnerNode t = blossomNodeAt t chosen.target := by simp [matchingInnerNode, blossomNodeAt, index]
    by_cases singleton : (part.blocks.block chosen.target).card = 1
    · have noNode : matchingInnerNode t = 0 := by rw [raw, dual.top, if_neg (by simp [singleton])]
      simp [matchingCutGroupEntry, singleton, noNode]
    · have present := part.blocks.cut_mem (Finset.mem_univ chosen.target) singleton
      have node : matchingInnerNode t = dual.node (part.blocks.block chosen.target) := by
        rw [raw, dual.top, if_pos ⟨fixed, singleton⟩]
      simp [matchingCutGroupEntry, fixed, singleton, inner, node, decode, dual.nodeNonzero _ present, dual.cutValues _ present]
  · rw [if_neg same]
    by_cases peer : i = chosen.peer
    · subst i
      have outer : newer.role chosen.peer = .outer (some chosen.target) := by
        simp [newer, AlternatingForestState.grow, Ne.symm chosen.distinct]
      simp [matchingCutGroupEntry, chosen.peerDormant, outer]
    · have kept : newer.role i = forest.role i := by simp [newer, AlternatingForestState.grow, same, peer]
      simp only [matchingCutGroupEntry, kept]


end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowthCutMeaning

/-! matching/MatchingGrowthRowMeaning.lean -/
section RppSource_MatchingGrowthRowMeaning
namespace VehicleRoutingSurvey.Routing

theorem growthSourceRowInputs_filter {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (eff : Fin k → ℝ) (peer : Fin k) (i : ℕ) (xs : List (Fin k)) :
    xs.flatMap (growthSourceRowInputs rep role cost eff peer i) =
      expansionRowOffers rep role cost eff (xs.filter (fun u => decide (rep u = peer))) i := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases belongs : rep x = peer <;> simp [growthSourceRowInputs, expansionRowOffers, belongs, ih,
      expansionRowOffers] at *

theorem MatchingGrowthSelection.promotes {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState} {edge : Sym2 (Fin k)}
    (g : MatchingGrowthSelection part forest s edge) (v : Fin k) :
    alternatingRoleCode ((forest.grow g.source g.target g.peer).role v) = 1 ↔
      alternatingRoleCode (forest.role v) = 1 ∨ v = g.peer := by
  by_cases hit : v = g.target
  · subst v
    simp [AlternatingForestState.grow, g.targetDormant, g.distinct, alternatingRoleCode]
  · by_cases peer : v = g.peer
    · subst v
      simp [AlternatingForestState.grow, Ne.symm g.distinct, alternatingRoleCode]
    · simp only [AlternatingForestState.grow, if_neg hit, peer, if_false, or_false]

def matchingGrowthIncomingSeed {k : ℕ} (rep : Fin k → Fin k) (target peer v : Fin k)
    (cached : Option (DualSlack (MatchingDualEvent k))) : Option (DualSlack (MatchingDualEvent k)) :=
  if rep v = peer then none else
    cached.map (fun d => {d with rate := if rep v = target then 0 else d.rate})

/-- The RAM rerates only the newly inner block. The entries of all continuing
incoming rows already have their prescribed rates, including dormant rows. -/
theorem MatchingGrowthSelection.incomingSeed {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState} {edge : Sym2 (Fin k)}
    (g : MatchingGrowthSelection part forest s edge) (v : Fin k) (cached : Option (DualSlack (MatchingDualEvent k)))
    (sound : ∀ d, cached = some d → alternatingRoleCode (forest.role (part.representative v)) ≠ 1 ∧
      d.rate = (if alternatingRoleCode (forest.role (part.representative v)) = 0 then 1 else 0)) :
    let next := fun r => alternatingRoleCode ((forest.grow g.source g.target g.peer).role r)
    matchingGrowthIncomingSeed part.representative g.target g.peer v cached =
      if next (part.representative v) = 1 then none else
        cached.map (fun d => {d with rate := if next (part.representative v) = 0 then 1 else 0}) := by
  intro next
  let r := part.representative v
  change (if r = g.peer then none else cached.map (fun d =>
      {d with rate := if r = g.target then 0 else d.rate})) =
    (if next r = 1 then none else cached.map (fun d => {d with rate := if next r = 0 then 1 else 0}))
  by_cases peer : r = g.peer
  · have on : next r = 1 := (g.promotes r).mpr (Or.inr peer)
    rw [if_pos peer, if_pos on]
  · rw [if_neg peer]
    by_cases target : r = g.target
    · have inner : next r = 2 := by simp [next, AlternatingForestState.grow, target, alternatingRoleCode]
      simp only [if_pos target, inner, show (2 : ℕ) ≠ 1 by decide, show (2 : ℕ) ≠ 0 by decide, if_false]
    · have kept : next r = alternatingRoleCode (forest.role r) := by simp [next, AlternatingForestState.grow, target, peer]
      cases found : cached with
      | none => simp
      | some d =>
        obtain ⟨off, rate⟩ := sound d found
        change alternatingRoleCode (forest.role r) ≠ 1 at off
        change d.rate = (if alternatingRoleCode (forest.role r) = 0 then 1 else 0) at rate
        simp only [kept, if_neg target, if_neg off, Option.map_some, ← rate]

/-- Combine the actual per-source scan with the exact old group minimum.
This covers all three selector ranges for a growth event. -/
theorem MatchingGrowthSelection.rowMinimum {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState} {edge : Sym2 (Fin k)}
    (g : MatchingGrowthSelection part forest s edge) (positive : 0 < k)
    (symmetric : ∀ u v, cost u v = cost v u)
    (nested : ∀ S ∈ state.cuts, ∀ u ∈ S, ∀ v ∈ S, part.blocks.block u = part.blocks.block v)
    (group : MatchingCandidateGroup k) (cached : Option (DualSlack (MatchingDualEvent k)))
    (before : LeastSlackEntry ((matchingSearchSlacks part forest positive).filter fun d =>
      @decide _ (Classical.propDecidable (group.admits part.blocks forest (part.representativeOf positive) d))) cached) :
    let after := forest.grow g.source g.target g.peer
    let eff := effectiveVertexPotential state.cuts state.potential state.cutDual
    let role := fun u => alternatingRoleCode (after.role u)
    let seed := match group with
      | .outer _ => cached
      | .incoming v => matchingGrowthIncomingSeed part.representative g.target g.peer v cached
      | .cut v => matchingCutGroupEntry part after v
    LeastSlackEntry ((matchingSearchSlacks part after positive).filter fun d =>
      @decide _ (Classical.propDecidable (group.admits part.blocks after (part.representativeOf positive) d)))
      (insertSlackCandidates ((List.finRange k).flatMap (growthSourceRowInputs part.representative role cost eff g.peer group.slot)) seed) := by
  intro after eff role seed
  let old := fun r => alternatingRoleCode (forest.role r)
  let fresh := (List.finRange k).filter (fun u => decide (part.representative u = g.peer))
  have stay (v : Fin k) (on : old (part.representative v) = 1) : role (part.representative v) = 1 :=
    (g.promotes _).mpr (Or.inl on)
  have freshIff (v : Fin k) : v ∈ fresh ↔ old (part.representative v) ≠ 1 ∧ role (part.representative v) = 1 := by
    simp only [fresh, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    constructor
    · intro hit
      exact ⟨by simp [old, hit, g.peerDormant, alternatingRoleCode], (g.promotes _).mpr (Or.inr hit)⟩
    · rintro ⟨off, on⟩
      exact ((g.promotes _).mp on).resolve_left off
  rw [growthSourceRowInputs_filter]
  cases group with
  | outer i =>
    exact expansionOuterRow_least symmetric (fun v on => ⟨rfl, stay v on⟩) fresh freshIff i before
      (matchingSearchOuterGroup_mem_iff part forest positive symmetric nested i)
      (matchingSearchOuterGroup_mem_iff part after positive symmetric nested i)
  | incoming v =>
    have oldGroup := matchingSearchIncomingGroup_mem_iff part forest positive symmetric nested v
    have seedEq := g.incomingSeed v cached (fun d present => by
      obtain ⟨u, _, _, off, value⟩ := (oldGroup d).mp (before.sound present)
      exact ⟨off, congrArg DualSlack.rate value.symm⟩)
    change LeastSlackEntry _ (insertSlackCandidates (expansionRowOffers _ _ _ _ fresh (k+v.val))
      (matchingGrowthIncomingSeed part.representative g.target g.peer v cached))
    rw [seedEq]
    exact expansionIncomingRow_least stay fresh freshIff v before oldGroup
      (matchingSearchIncomingGroup_mem_iff part after positive symmetric nested v)
  | cut i =>
    change LeastSlackEntry _ (insertSlackCandidates (expansionRowOffers _ _ _ _ fresh (2*k+i.val)) (matchingCutGroupEntry part after i))
    rw [expansionCutOffers_empty]
    exact matchingCutGroupEntry_least part after positive i


end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowthRowMeaning

/-! matching/MatchingGrowthPairMeaning.lean -/
section RppSource_MatchingGrowthPairMeaning
namespace VehicleRoutingSurvey.Routing

/-- A newly outer block offers each of its original edges to the two directed
slots for the endpoint representatives. -/
theorem growthSourcePairOffers_mem {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (time : ℝ) (peer a b : Fin k)
    (d : DualSlack (MatchingDualEvent k)) :
    d ∈ (List.finRange k).flatMap (growthSourcePairInputs rep role cost effective time peer (k*a.val+b.val)) ↔
      ∃ u v : Fin k, rep u = peer ∧ peer ≠ rep v ∧ role (rep v) = 1 ∧
        ((a = peer ∧ b = rep v) ∨ (a = rep v ∧ b = peer)) ∧ normalizedOuterEdge cost effective time u v = d := by
  simp only [List.mem_flatMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨u, offered⟩
    by_cases selected : rep u = peer
    · simp only [growthSourcePairInputs, if_pos selected, List.mem_filterMap, List.mem_finRange, true_and] at offered
      obtain ⟨v, found⟩ := offered
      obtain ⟨diff, ⟨on, coords⟩, value⟩ := (outerRefreshPairInput_some_iff rep role cost effective time u v a b d).mp found
      rw [selected] at diff coords
      exact ⟨u, v, selected, diff, on, coords, value⟩
    · simp [growthSourcePairInputs, selected] at offered
  · rintro ⟨u, v, selected, diff, on, coords, value⟩
    refine ⟨u, ?_⟩
    simp only [growthSourcePairInputs, if_pos selected, List.mem_filterMap, List.mem_finRange, true_and]
    refine ⟨v, (outerRefreshPairInput_some_iff rep role cost effective time u v a b d).mpr ?_⟩
    exact ⟨by rwa [selected], ⟨on, by rwa [selected]⟩, value⟩

/-- Rebuilding the promoted block extends the old directed-pair invariant
to the grown forest, including vacancy at every still nonouter original. -/
theorem MatchingSearchOuterBuckets.grow {k : ℕ} {s t : ArithmeticState} {rep : Fin k → Fin k}
    {old next : Fin k → ℕ} {cost : Fin k → Fin k → ℝ} {effective : Fin k → ℝ} {peer : Fin k}
    (cached : MatchingSearchOuterBuckets s rep old cost effective)
    (symmetric : ∀ u v, cost u v = cost v u) (idem : ∀ v, rep (rep v) = rep v)
    (fixed : rep peer = peer) (fresh : old peer ≠ 1)
    (promoted : ∀ r, next r = 1 ↔ old r = 1 ∨ r = peer)
    (time : t.rr 15 = s.rr 15)
    (stored : ∀ i < k*k, MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i =
      insertSlackCandidates ((List.finRange k).flatMap (growthSourcePairInputs rep next cost effective (s.rr 15) peer i))
        (readMatchingPairBucket (k := k) s i)) : MatchingSearchOuterBuckets t rep next cost effective := by
  have peerOn := (promoted peer).mpr (Or.inr rfl)
  let offers (a b : Fin k) := (List.finRange k).flatMap
    (growthSourcePairInputs rep next cost effective (s.rr 15) peer (k*a.val+b.val))
  have mem := growthSourcePairOffers_mem rep next cost effective (s.rr 15) peer
  have untouched (a b : Fin k) (aa : a ≠ peer) (bb : b ≠ peer) : offers a b = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d found
    obtain ⟨_, _, _, _, _, coords, _⟩ := (mem a b d).mp found
    exact coords.elim (fun c => aa c.1) (fun c => bb c.2)
  refine ⟨fun i hi => (stored i hi).1, ?_, ?_⟩
  · intro a b diff left right
    rw [time, (stored _ (matchingPairSlot_lt a b)).2]
    change LeastSlackEntry _ (insertSlackCandidates (offers a b) _)
    by_cases affected : a = peer ∨ b = peer
    · have oldEmpty : readMatchingPairBucket (k := k) s (k*a.val+b.val) = none := by
        apply cached.inactive
        rcases affected with h | h
        · exact Or.inl (by rwa [h, fixed])
        · exact Or.inr (by rwa [h, fixed])
      rw [oldEmpty]
      have empty : LeastSlackEntry ([] : List (DualSlack (MatchingDualEvent k))) none := by constructor <;> simp
      have least := empty.insert_many (offers a b)
      have exactOffers (d : DualSlack (MatchingDualEvent k)) : d ∈ (offers a b).reverse ++ [] ↔
          d ∈ normalizedOuterPairEntries rep cost effective (s.rr 15) a b := by
        rw [List.append_nil, List.mem_reverse, normalizedOuterPairEntries_mem]
        constructor
        · intro found
          obtain ⟨u, v, source, _, _, coords, val⟩ := (mem a b d).mp found
          rcases coords with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact ⟨u, v, source.trans ha.symm, hb.symm, val⟩
          · exact ⟨v, u, ha.symm, source.trans hb.symm, (normalizedOuterEdge_swap symmetric effective _ v u).trans val⟩
        · rintro ⟨u, v, hu, hv, val⟩
          apply (mem a b d).mpr
          rcases affected with ha | hb
          · exact ⟨u, v, hu.trans ha, by rwa [← ha, hv], by rwa [hv], Or.inl ⟨ha, hv.symm⟩, val⟩
          · exact ⟨v, u, hv.trans hb, by rw [← hb, hu]; exact Ne.symm diff, by rwa [hu], Or.inr ⟨hu.symm, hb⟩,
              (normalizedOuterEdge_swap symmetric effective _ v u).trans val⟩
      exact ⟨fun hit => (exactOffers _).mp (least.sound hit), fun d hit => least.covers d ((exactOffers _).mpr hit)⟩
    · have aa : a ≠ peer := fun h => affected (Or.inl h)
      have bb : b ≠ peer := fun h => affected (Or.inr h)
      rw [untouched a b aa bb]
      exact cached.least a b diff (((promoted a).mp left).resolve_right aa) (((promoted b).mp right).resolve_right bb)
  · intro a b off
    have before : old (rep a) ≠ 1 ∨ old (rep b) ≠ 1 :=
      off.imp (fun h oldOn => h ((promoted _).mpr (Or.inl oldOn))) (fun h oldOn => h ((promoted _).mpr (Or.inl oldOn)))
    have noOffers : offers a b = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro d hit
      obtain ⟨_, v, _, _, on, coords, _⟩ := (mem a b d).mp hit
      rcases coords with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [fixed, idem, peerOn, on] at off
    rw [(stored _ (matchingPairSlot_lt a b)).2, cached.inactive a b before]
    change insertSlackCandidates (offers a b) none = none
    rw [noOffers]; rfl


end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowthPairMeaning

/-! matching/MatchingGrowthSearchRows.lean -/
section RppSource_MatchingGrowthSearchRows
namespace VehicleRoutingSurvey.Routing

open Classical in
theorem matchingGrowthIncomingAt_slot {k : ℕ} {s : ArithmeticState} {rep : Fin k → Fin k}
    (size : s.nr 55 = k) (reps : ∀ v : Fin k, s.nm (s.nr 57+v.val) = (rep v).val)
    (r : Fin k) (g : MatchingCandidateGroup k) :
    MatchingGrowthIncomingAt s r.val g.slot ↔ match g with | .incoming v => rep v = r | _ => False := by
  cases g with
  | outer v =>
    simp only [MatchingCandidateGroup.slot, MatchingGrowthIncomingAt, size, iff_false]
    rintro ⟨j, _, address, _⟩
    have := v.isLt
    omega
  | cut v =>
    simp only [MatchingCandidateGroup.slot, MatchingGrowthIncomingAt, size, iff_false]
    rintro ⟨j, hj, address, _⟩
    omega
  | incoming v =>
    simp only [MatchingCandidateGroup.slot, MatchingGrowthIncomingAt, size, Nat.add_left_cancel_iff]
    constructor
    · rintro ⟨j, _, address, word⟩
      subst j
      exact Fin.ext ((reps v).symm.trans word)
    · intro h
      exact ⟨v.val, v.isLt, rfl, (reps v).trans (congrArg Fin.val h)⟩

/-- Starting after the grow prefix has set both forest roles, run the entire
cache suffix and recover the stage selector with its full minimum semantics. -/
theorem MatchingGrowthSelection.refreshSearch {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {eventInput s : ArithmeticState} {edge : Sym2 (Fin k)}
    (g : MatchingGrowthSelection part forest eventInput edge) (positive : 0 < k)
    (symmetric : ∀ u v, cost u v = cost v u)
    (nested : ∀ S ∈ state.cuts, ∀ u ∈ S, ∀ v ∈ S, part.blocks.block u = part.blocks.block v)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (target : s.nr 28 = g.target.val) (peer : s.nr 26 = g.peer.val)
    (nodes : s.nr 65+2*(k*k) ≤ s.nr 74) (values : s.nr 66+k*k ≤ s.nr 75)
    (read : MatchingRefreshInput s part.representative
      (fun r => alternatingRoleCode ((forest.grow g.source g.target g.peer).role r)) cost
      (effectiveVertexPotential state.cuts state.potential state.cutDual))
    (dual : MatchingSearchDualMemory part (forest.grow g.source g.target g.peer) s)
    (valid : ∀ i < s.nr 61, MatchingCandidateRowValid (matchingTopCutAt part) s i)
    (least : ∀ group : MatchingCandidateGroup k, LeastSlackEntry ((matchingSearchSlacks part forest positive).filter fun d =>
      @decide _ (Classical.propDecidable (group.admits part.blocks forest (part.representativeOf positive) d)))
      (readMatchingCandidate (matchingTopCutAt part) s group.slot))
    (oldPairs : MatchingSearchOuterBuckets s part.representative (fun u => alternatingRoleCode (forest.role u))
      cost (effectiveVertexPotential state.cuts state.potential state.cutDual)) :
    let after := forest.grow g.source g.target g.peer
    let eff := effectiveVertexPotential state.cuts state.potential state.cutDual
    ∃ t ticks, BlockRuns matchingGrowthCacheRepairBlock ticks s t ∧ t.halted = false ∧
      ticks ≤ 25*k+(k*98+2)*matchingGrowthMembers s k+32 ∧ t.nr 1 = 0 ∧
      MatchingSearchRows part after positive (matchingTopCutAt part) t ∧
      MatchingSearchOuterBuckets t part.representative (fun u => alternatingRoleCode (after.role u)) cost eff ∧
      MatchingRefreshInput t part.representative (fun u => alternatingRoleCode (after.role u)) cost eff ∧
      MatchingCacheFootprint k s t ∧ t.rr 15 = s.rr 15 := by
  classical
  intro after eff
  let cut := matchingTopCutAt part
  obtain ⟨t, ticks, run, live, bound, clear, ids, slacks, rates, count, reads, frame, clock, rows, pairs⟩ :=
    matchingGrowthCacheRepairBlock_rows cut entry running one zero read target peer g.distinct nodes values valid oldPairs.valid
  have targetFixed := (part.mem_activeRepresentatives _).mp g.targetActive
  have peerFixed : part.representative g.peer = g.peer := by
    obtain ⟨_, b, _, tail, _⟩ := g.matched
    rw [← tail]
    exact part.representative_idem b
  have cutCode : cut g.target = part.blocks.block g.target := if_pos targetFixed
  have decoded (r : Fin k) (group : MatchingCandidateGroup k) := matchingGrowthIncomingAt_slot read.layout.dimension read.representatives r group
  refine ⟨t, ticks, run, live, bound, clear, ⟨reads.layout, count, ids, slacks, rates, ?_, ?_⟩,
    oldPairs.grow symmetric part.representative_idem peerFixed (by simp [g.peerDormant, alternatingRoleCode])
      g.promotes clock pairs, reads, frame, clock⟩
  · intro i hi
    exact (rows i ((reads.layout.rows.trans read.layout.rows.symm) ▸ hi)).1
  · intro group
    rw [(rows group.slot (read.layout.rows.symm ▸ group.slot_lt)).2]
    have base := g.rowMinimum positive symmetric nested group _ (least group)
    suffices same : growthRepairSeed cut s g.target group.slot =
        (match group with
        | .outer _ => readMatchingCandidate cut s group.slot
        | .incoming v => matchingGrowthIncomingSeed part.representative g.target g.peer v (readMatchingCandidate cut s group.slot)
        | .cut v => matchingCutGroupEntry part after v) by
      rw [same]
      cases group <;> exact base
    cases group with
    | outer v =>
      have small := v.isLt
      have notCut : (MatchingCandidateGroup.outer v).slot ≠ 2*k+g.target.val := by change v.val ≠ _; omega
      have noPeer := (decoded g.peer (.outer v)).not.mpr id
      have noTarget := (decoded g.target (.outer v)).not.mpr id
      simp [growthRepairSeed, notCut, peer, target, noPeer, noTarget, Function.id_def]
    | incoming v =>
      have small := v.isLt
      have notCut : (MatchingCandidateGroup.incoming v).slot ≠ 2*k+g.target.val := by change k+v.val ≠ _; omega
      simp only [growthRepairSeed, matchingGrowthIncomingSeed, if_neg notCut, peer, target,
        decoded g.peer (.incoming v), decoded g.target (.incoming v)]
    | cut v =>
      have noPeer := (decoded g.peer (.cut v)).not.mpr id
      have noTarget := (decoded g.target (.cut v)).not.mpr id
      have atCut : matchingCutGroupEntry part after v = _ := g.cutEntries dual target cut cutCode v
      have oldCut : readMatchingCandidate cut s (MatchingCandidateGroup.cut v).slot = _ :=
        matchingCutGroupEntry_of_least (least (.cut v))
      have idx : (MatchingCandidateGroup.cut v).slot = 2*k+g.target.val ↔ v = g.target := by
        simp [MatchingCandidateGroup.slot, Fin.ext_iff]
      by_cases hit : v = g.target
      · subst v
        simpa only [growthRepairSeed, MatchingCandidateGroup.slot, eq_self, if_true] using atCut.symm
      · simp [growthRepairSeed, idx, peer, target, noPeer, noTarget, atCut, oldCut, hit]


end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowthSearchRows

/-! matching/MatchingGrowForestCache.lean -/
section RppSource_MatchingGrowForestCache
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 8192 in
/-- The role and parent writes followed by the real cache repairs take the
post-dual search state to a fully decoded selector for the grown forest. -/
theorem MatchingGrowthSelection.growCaches {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s original : ArithmeticState} {edge : Sym2 (Fin k)}
    {positive : 0 < k} (g : MatchingGrowthSelection part forest s edge)
    (advanced : MatchingAdvancedStage part forest positive (matchingTopCutAt part) original s)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (layout : MatchingWarmLayout s k) (nodes : s.nr 65+2*(k*k) ≤ s.nr 74)
    (duals : s.nr 66+k*k ≤ s.nr 75) (symmetric : ∀ u v, cost u v = cost v u) :
    let newer := forest.grow g.source g.target g.peer
    let program := appendBlock applyMatchingGrowEventBlock (appendBlock saveMatchingGrowthBlocks matchingGrowthCacheRepairBlock)
    ∃ t ticks, BlockRuns program ticks s t ∧ t.halted = false ∧ t.nr 1 = 0 ∧
      MatchingSearchRows part newer positive (matchingTopCutAt part) t ∧
      MatchingSearchOuterBuckets t part.representative (fun u => alternatingRoleCode (newer.role u)) cost
        (effectiveVertexPotential state.cuts state.potential state.cutDual) ∧
      MatchingRefreshInput t part.representative (fun u => alternatingRoleCode (newer.role u)) cost
        (effectiveVertexPotential state.cuts state.potential state.cutDual) ∧
      (∀ a, a < s.nr 51 ∨ s.nr 74 ≤ a → t.nm a = s.nm a) ∧
      (∀ a, a < s.nr 59 ∨ s.nr 75 ≤ a → t.rm a = s.rm a) ∧ t.rr 15 = s.rr 15 ∧
      AlternatingForestMemory newer (s.nr 51) t.nm ∧ t.nr 26 = g.peer.val ∧ t.nr 28 = g.target.val ∧
      (∀ r, r = 9 ∨ r = 20 ∨ r = 21 ∨ 29 ≤ r → t.nr r = s.nr r) := by
  intro newer program
  obtain ⟨u, ut, _, roleRun, uLive, roles, _, target, peer, unit, real, natural, ports⟩ :=
    applyMatchingGrowEventBlock_valid advanced.search.valid s entry running one advanced.dual.roles layout.parents
      layout.depths g.sourceWord g.targetWord g.peerWord g.sourceOuter g.targetDormant g.peerDormant g.distinct
      g.paired g.reversePaired g.incoming g.matched
  let a := {u with pc := 0}
  let saved := {a with pc := 3, nr := Function.update (Function.update (Function.update a.nr 14 0) 26 (a.nr 2)) 28 (a.nr 1)}
  let b := {saved with pc := 0}
  have save : BlockRuns saveMatchingGrowthBlocks 3 a saved := saveMatchingGrowthBlocks_spec a rfl uLive
  have same (r : ℕ) (high : 15 ≤ r := by decide) (noPeer : r ≠ 26 := by decide) (noTarget : r ≠ 28 := by decide) :
      b.nr r = s.nr r := by
    simpa [b, saved, a, Function.update_of_ne noPeer, Function.update_of_ne noTarget,
      Function.update_of_ne (show r ≠ 14 by omega)] using ports r high
  have afterForest : s.nr 53+k ≤ s.nr 57 := by have h := layout.representativesAfter; rw [layout.depths]; omega
  have afterRep := layout.candidatesAfter
  have mates := layout.matesBefore
  have offsets := layout.offsetsBefore
  have headers := advanced.reads.layout.recordsBefore
  have dictionary := advanced.reads.layout.idsBefore
  have bReads : MatchingRefreshInput b part.representative (fun u => alternatingRoleCode (newer.role u)) cost
      (effectiveVertexPotential state.cuts state.potential state.cutDual) := by
    have old := advanced.reads
    refine ⟨old.layout.keeps (fun r hi => same r (by omega) (by omega) (by omega)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [same 21, same 58]; exact old.offsetsBefore
    · rw [same 57, same 58]; exact old.representativesBefore
    · rw [same 51, same 58]; exact old.rolesBefore
    · rw [same 20, same 59]; exact old.metricBefore
    · rw [same 62, same 59]; exact old.effectiveBefore
    · intro v; rw [same 21]; exact (natural _ (.inl (by have h := v.isLt; omega))).trans (old.offsets v)
    · intro v; rw [same 57]; exact (natural _ (.inr (by omega))).trans (old.representatives v)
    · intro v; rw [same 51]; exact (roles v).1
    · intro v w; rw [same 20]; exact (congrFun real _).trans (old.metric v w)
    · intro v; rw [same 62]; exact (congrFun real _).trans (old.potentials v)
  have top (v : Fin k) : blossomNodeAt b v = blossomNodeAt s v := by
    unfold blossomNodeAt
    rw [same 74]
    exact natural _ (.inr (by omega))
  let dual : MatchingSearchDualMemory part newer b := {
    dimension := bReads.layout.dimension
    separated := by rw [same 62, same 75]; exact advanced.dual.separated
    reps := bReads.representatives
    roles := by rw [same 51]; exact roles
    effective := bReads.potentials
    node := advanced.dual.node
    nodeNonzero := advanced.dual.nodeNonzero
    nodeInjective := advanced.dual.nodeInjective
    cutValues B h := by rw [same 75]; exact (congrFun real _).trans (advanced.dual.cutValues B h)
    top v := (top v).trans (advanced.dual.top v) }
  obtain ⟨row, pair⟩ := matchingCacheRegionReads (t := b) advanced.reads.layout
    (fun r mem => same r (by simp at mem; omega) (by simp at mem; omega) (by simp at mem; omega))
    (fun addr h _ => natural _ (.inr (by omega))) (fun addr _ _ => congrFun real addr) (matchingTopCutAt part) advanced.valid
  have clock : b.rr 15 = s.rr 15 := roleRun.keeps_cache_real (by decide)
  have oldPairs : MatchingSearchOuterBuckets b part.representative (fun r => alternatingRoleCode (forest.role r))
      cost (effectiveVertexPotential state.cuts state.potential state.cutDual) := by
    refine ⟨fun i hi => (pair i hi).1.symm ▸ advanced.pairs.valid i hi, ?_, ?_⟩
    · intro p q distinct left right
      rw [clock, (pair _ (matchingPairSlot_lt p q)).2]
      exact advanced.pairs.least p q distinct left right
    · intro p q idle; exact (pair _ (matchingPairSlot_lt p q)).2.trans (advanced.pairs.inactive p q idle)
  obtain ⟨t, tt, repair, live, _, empty, rows, buckets, reads, frame, endClock⟩ :=
    g.refreshSearch positive symmetric advanced.registry.nested (s := b) rfl uLive (by simpa [b, saved, a] using unit)
      (by simp [b, saved]) (by simpa [b, saved, a] using target) (by simpa [b, saved, a] using peer)
      (by rw [same 65, same 74]; exact nodes) (by rw [same 66, same 75]; exact duals)
      bReads dual (fun i hi => (row i (same 61 ▸ hi)).1) (by
        intro group
        rw [(row _ (advanced.reads.layout.rows.symm ▸ group.slot_lt)).2]
        exact advanced.least group) oldPairs
  have repairRegs (r : ℕ) (safe : r ∉ [0,1,3,4,5,6,7,8,10,11,15,16,17,18,19,24,25,27] := by decide) : t.nr r = b.nr r := by
    rw [← repair.run]
    exact arithmeticRun_keeps_from_destination_list [0,1,3,4,5,6,7,8,10,11,15,16,17,18,19,24,25,27]
      (by decide) safe b tt
  have run := roleRun.append (save.append repair)
  have outReads := reads.keeps (t := relocateState applyMatchingGrowEventBlock.length (relocateState saveMatchingGrowthBlocks.length t))
    ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
  refine ⟨_, _, run, live, empty,
    ⟨outReads.layout, rows.count, rows.ids, rows.slacks, rows.rates, rows.valid, rows.least⟩,
    ⟨buckets.valid, buckets.least, buckets.inactive⟩, outReads, ?_, ?_, endClock.trans clock,
    ?_, (repairRegs 26).trans (by simpa [b,saved,a] using peer), (repairRegs 28).trans (by simpa [b,saved,a] using target), ?_⟩
  · intro addr outside
    have pairBase := layout.pairsAfter
    have roleBase := advanced.reads.rolesBefore
    exact (frame.natural addr (by rw [same 58, same 65]; rcases outside with lo | hi <;> omega)).trans
      (natural addr (by rcases outside with lo | hi <;> omega))
  · intro addr outside
    exact (frame.real addr (by rw [same 59, same 66]; rcases outside with lo | hi <;> omega)).trans (congrFun real addr)

  · intro v
    have bound := v.isLt
    have room := layout.representativesAfter
    obtain ⟨label, parent, depth⟩ := roles v
    have stable (addr : ℕ) (small : addr < s.nr 58) : t.nm addr = b.nm addr :=
      frame.natural addr (.inl ((same 58).symm ▸ small))
    exact ⟨(stable _ (by omega)).trans label,(stable _ (by omega)).trans parent,(stable _ (by omega)).trans depth⟩
  · intro r preserved
    rw [← run.run]
    exact arithmeticRun_keeps_from_destination_list
      [0,1,2,3,4,5,6,7,8,10,11,12,14,15,16,17,18,19,24,25,26,27,28]
      (by decide) (by simp; omega) s _


end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowForestCache

/-! matching/MatchingGrowthWitnessExit.lean -/
section RppSource_MatchingGrowthWitnessExit
namespace VehicleRoutingSurvey.Routing

/-- The final two endpoint stores are above the candidate and pair tables.
They preserve the minimum of every row and the normalized outer-pair keys. -/
theorem storeOrientedMatchingGrowthWitnesses_rows {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {cutAt : Fin k → Finset (Fin k)}
    {s : ArithmeticState} (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (clear : s.nr 1 = 0) (target peer : Fin k) (targetWord : s.nr 28 = target.val) (peerWord : s.nr 26 = peer.val)
    (floor : s.nr 65+2*(k*k) ≤ s.nr 90) (oldRows : MatchingSearchRows part forest positive cutAt s)
    (oldPairs : MatchingSearchOuterBuckets s part.representative (fun r => alternatingRoleCode (forest.role r))
      cost (effectiveVertexPotential state.cuts state.potential state.cutDual))
    (oldReads : MatchingRefreshInput s part.representative (fun r => alternatingRoleCode (forest.role r))
      cost (effectiveVertexPotential state.cuts state.potential state.cutDual)) :
    ∃ t steps, steps ≤ 18 ∧ BlockRuns storeOrientedMatchingGrowthWitnesses steps s t ∧ t.halted = false ∧
      t.nr 1 = 0 ∧ MatchingSearchRows part forest positive cutAt t ∧
      MatchingSearchOuterBuckets t part.representative (fun r => alternatingRoleCode (forest.role r))
        cost (effectiveVertexPotential state.cuts state.potential state.cutDual) ∧
      MatchingRefreshInput t part.representative (fun r => alternatingRoleCode (forest.role r))
        cost (effectiveVertexPotential state.cuts state.potential state.cutDual) ∧
      t.nm = writeMatchingForestWitness
        (writeMatchingForestWitness s.nm (s.nr 90) target.val (orientedMatchingGrowthEdge s))
        (s.nr 90) peer.val (target.val,peer.val) ∧
      (∀ a, a < s.nr 90 ∨ s.nr 90+2*k ≤ a → t.nm a = s.nm a) ∧
      t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r ∉ ([0,6,10,14,22,23] : List ℕ), t.nr r = s.nr r := by
  obtain ⟨t, steps, limit, run, live, natural, real, regs⟩ := storeOrientedMatchingGrowthWitnesses_spec s entry running one
  have fixed (r : ℕ) (safe : r ∉ ([0,6,10,14,22,23] : List ℕ) := by decide) : t.nr r = s.nr r := by
    rw [← run.run]
    exact arithmeticRun_keeps_from_destination_list [0,6,10,14,22,23] (by decide) safe s steps
  rw [targetWord,peerWord] at natural
  have keep (a : ℕ) (safe : a < s.nr 90 ∨ s.nr 90+2*k ≤ a) : t.nm a = s.nm a := by
    have lo := target.isLt
    have hi := peer.isLt
    simp (disch := omega) [natural,writeMatchingForestWitness,forestWitnessAddress,Function.update_of_ne]
  have ids := oldReads.layout.idsBefore
  have cn := oldReads.layout.recordsBefore
  have cache := matchingCacheRegionReads (t := t) oldReads.layout (fun r hr => fixed r (by simp at hr ⊢; omega))
    (fun a _ below => keep a (.inl (below.trans_le floor))) (fun a _ _ => congrFun real a) cutAt oldRows.valid
  have reads := oldReads.keeps (t := t) ⟨fun a small => keep a (.inl (by omega)),fun a _ _ _ => congrFun real a⟩
    (fun r hr => fixed r (by simp [matchingRefreshTableRegisters] at hr; simp; omega))
  refine ⟨t,steps,limit,run,live,(fixed 1).trans clear,?_,?_,reads,natural,keep,real,regs,fun r safe => fixed r safe⟩
  · refine ⟨reads.layout,?_,?_,?_,?_,?_,?_⟩
    · rw [fixed 8,fixed 61]; exact oldRows.count
    · rw [fixed 3,fixed 58]; exact oldRows.ids
    · rw [fixed 4,fixed 59]; exact oldRows.slacks
    · rw [fixed 5,fixed 60]; exact oldRows.rates
    · intro i hi; exact (cache.1 i (fixed 61 ▸ hi)).1
    · intro group
      rw [(cache.1 _ (oldReads.layout.rows.symm ▸ group.slot_lt)).2]; exact oldRows.least group
  · refine ⟨fun i hi => (cache.2 i hi).1.symm ▸ oldPairs.valid i hi, ?_, ?_⟩
    · intro p q diff left right
      rw [regs,(cache.2 _ (matchingPairSlot_lt p q)).2]; exact oldPairs.least p q diff left right
    · intro p q idle; exact (cache.2 _ (matchingPairSlot_lt p q)).2.trans (oldPairs.inactive p q idle)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowthWitnessExit

/-! matching/BlossomCreditGrowth.lean -/
section RppSource_BlossomCreditGrowth
namespace VehicleRoutingSurvey.Routing

/-- Growth makes one new top-level block outer. Exactly the original
vertices in that block become outer, and the inherited cuts are unchanged. -/
theorem matchingPartitionCounts_grow {k : ℕ} {vertices : Finset (Fin k)}
    {cuts inherited : Finset (Finset (Fin k))} (blocks : TopLevelMatchingBlocks vertices cuts)
    (within : ∀ v ∈ vertices, blocks.block v ⊆ vertices)
    (before after : Finset (Fin k) → Prop) [DecidablePred before] [DecidablePred after]
    {promoted : Finset (Fin k)} (top : promoted ∈ vertices.image blocks.block)
    (unseen : ¬before promoted) (promotes : ∀ B, after B ↔ before B ∨ B = promoted) :
    MatchingStageTransition (matchingPartitionCounts blocks before inherited) (1 + promoted.card)
      (matchingPartitionCounts blocks after inherited) := by
  obtain ⟨v0, v0In, blockAt⟩ := Finset.mem_image.mp top
  have promotedInside : promoted ⊆ vertices := blockAt ▸ within v0 v0In
  have promotedPositive : 0 < promoted.card := Finset.card_pos.mpr ⟨v0, blockAt ▸ blocks.self_mem v0 v0In⟩
  have memberIff (v : Fin k) (inside : v ∈ vertices) : v ∈ promoted ↔ blocks.block v = promoted := by
    refine ⟨fun found => (blocks.same_of_mem v0In (blockAt.symm ▸ found)).trans blockAt, ?_⟩
    exact fun same => same ▸ blocks.self_mem v inside
  let oldNonouter := vertices.filter (fun v => ¬before (blocks.block v))
  let newNonouter := vertices.filter (fun v => ¬after (blocks.block v))
  let oldOuter := (vertices.image blocks.block).filter before
  let newOuter := (vertices.image blocks.block).filter after
  have oldPartition : oldNonouter = newNonouter ∪ promoted := by
    ext v
    simp only [oldNonouter, newNonouter, Finset.mem_filter, Finset.mem_union]
    by_cases inside : v ∈ vertices
    · have previouslyNonouter : blocks.block v = promoted → ¬before (blocks.block v) :=
        fun same => same.symm ▸ unseen
      simp only [inside, true_and, memberIff v inside, promotes]
      tauto
    · have notPromoted : v ∉ promoted := fun member => inside (promotedInside member)
      simp [inside, notPromoted]
  have separated : Disjoint newNonouter promoted := by
    apply Finset.disjoint_left.mpr
    intro v nonouter moved
    have found := Finset.mem_filter.mp nonouter
    exact found.2 ((promotes _).mpr (Or.inr ((memberIff v found.1).mp moved)))
  have oldNonouterSize : oldNonouter.card = newNonouter.card + promoted.card := by
    rw [oldPartition, Finset.card_union_of_disjoint separated]
  have addsOuterBlock : newOuter = insert promoted oldOuter := by
    ext B
    simp only [newOuter, oldOuter, Finset.mem_filter, Finset.mem_insert, promotes]
    by_cases same : B = promoted
    · subst B
      simp [top]
    · simp [same]
  have notOld : promoted ∉ oldOuter := fun h => unseen (Finset.mem_filter.mp h).2
  have newOuterSize : newOuter.card = oldOuter.card + 1 := by
    rw [addsOuterBlock, Finset.card_insert_of_notMem notOld]
  have outerCost : newOuter.card ≤ oldOuter.card + promoted.card := by
    rw [newOuterSize]
    exact Nat.add_le_add_left promotedPositive _
  exact MatchingStageTransition.grow promoted.card promotedPositive oldNonouterSize outerCost le_rfl

end VehicleRoutingSurvey.Routing
end RppSource_BlossomCreditGrowth

/-! matching/MatchingGrowthCredit.lean -/
section RppSource_MatchingGrowthCredit
namespace VehicleRoutingSurvey.Routing

/-- Only labels of current top-level blocks enter the work measure. -/
theorem matchingPartitionCounts_congr_top {k : ℕ} {cuts inherited : Finset (Finset (Fin k))}
    (blocks : TopLevelMatchingBlocks Finset.univ cuts)
    (p q : Finset (Fin k) → Prop) [DecidablePred p] [DecidablePred q]
    (same : ∀ B ∈ Finset.univ.image blocks.block, p B ↔ q B) :
    matchingPartitionCounts blocks p inherited = matchingPartitionCounts blocks q inherited := by
  have originals : ((Finset.univ : Finset (Fin k)).filter fun v => ¬p (blocks.block v)) =
      Finset.univ.filter fun v => ¬q (blocks.block v) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [same _ (Finset.mem_image_of_mem _ (Finset.mem_univ v))]
  have groups : (Finset.univ.image blocks.block).filter p = (Finset.univ.image blocks.block).filter q := by
    ext B
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨top, present⟩
      exact ⟨top, (same B top).mp present⟩
    · rintro ⟨top, present⟩
      exact ⟨top, (same B top).mpr present⟩
  simp only [matchingPartitionCounts, originals, groups]

/-- Growth spends the charge for exactly the block made outer by the selected
matched partner. This identifies the actual scan size with the potential drop. -/
theorem MatchingGrowthSelection.credit {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState} {edge : Sym2 (Fin k)}
    (selection : MatchingGrowthSelection part forest s edge) (top : CompactTopMatching part)
    (positive : 0 < k) (inherited : Finset (Finset (Fin k))) :
    let nextForest := forest.grow selection.source selection.target selection.peer
    MatchingStageTransition (matchingPartitionCounts part.blocks (part.outerBlock forest positive) inherited)
      (1 + (part.blocks.block selection.peer).card)
      (matchingPartitionCounts part.blocks (part.outerBlock nextForest positive) inherited) := by
  intro nextForest
  let older := part.outerBlock forest positive
  let newer := part.outerBlock nextForest positive
  let promoted := part.blocks.block selection.peer
  let ideal := fun B => older B ∨ B = promoted
  letI : DecidablePred ideal := fun B => inferInstanceAs (Decidable (older B ∨ B = promoted))
  have peerFixed : part.representative selection.peer = selection.peer :=
    (part.mem_activeRepresentatives selection.peer).mp
      (top.resetForest.1.partners _ selection.targetActive _ selection.paired).1
  have peerRep : part.representativeOf positive promoted = selection.peer :=
    (part.representativeOf_block positive _).trans peerFixed
  have notOuter : ¬older promoted := by
    unfold older CompactMatchingPartition.outerBlock
    rw [peerRep, selection.peerDormant]
    simp [alternatingRoleCode]
  have topNew : promoted ∈ Finset.univ.image part.blocks.block := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have labelAgreement (B : Finset (Fin k)) (atTop : B ∈ Finset.univ.image part.blocks.block) : ideal B ↔ newer B := by
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp atTop
    have names : part.representativeOf positive (part.blocks.block v) = selection.peer ↔ part.blocks.block v = promoted := by
      simpa only [part.representativeOf_block, peerFixed, promoted] using
        (part.same_block (u := v) (v := selection.peer))
    change (alternatingRoleCode (forest.role (part.representativeOf positive (part.blocks.block v))) = 1 ∨
        part.blocks.block v = promoted) ↔
      alternatingRoleCode (nextForest.role (part.representativeOf positive (part.blocks.block v))) = 1
    by_cases affected : part.representativeOf positive (part.blocks.block v) = selection.peer
    · have hp := names.mp affected
      simp [hp, peerRep, nextForest, AlternatingForestState.grow, (Ne.symm selection.distinct), alternatingRoleCode]
    by_cases toInner : part.representativeOf positive (part.blocks.block v) = selection.target
    · have other : part.blocks.block v ≠ promoted := fun same => affected (names.mpr same)
      simp [toInner, other, nextForest, AlternatingForestState.grow, selection.targetDormant, alternatingRoleCode]
    · have other : part.blocks.block v ≠ promoted := fun same => affected (names.mpr same)
      simp [toInner, affected, other, nextForest, AlternatingForestState.grow]
  have count := matchingPartitionCounts_congr_top (inherited := inherited) part.blocks ideal newer labelAgreement
  change MatchingStageTransition (matchingPartitionCounts part.blocks older inherited) (1 + promoted.card)
    (matchingPartitionCounts part.blocks newer inherited)
  rw [← count]
  exact matchingPartitionCounts_grow part.blocks (fun _ _ => Finset.subset_univ _) older ideal topNew notOuter (fun _ => Iff.rfl)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowthCredit

/-! matching/MatchingGrowthStageBudget.lean -/
section RppSource_MatchingGrowthStageBudget
namespace VehicleRoutingSurvey.Routing

/-- Charge the number of originals enumerated by the executable promotion
sweep to the stage's physical credit counter. No new record is allocated. -/
theorem MatchingGrowthSelection.ramBudget {k stage : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {eventInput s t : ArithmeticState} {edge : Sym2 (Fin k)}
    (g : MatchingGrowthSelection part forest eventInput edge) (positive : 0 < k) (top : CompactTopMatching part)
    {before : MatchingSearchDualMemory part forest s}
    {after : MatchingSearchDualMemory part (forest.grow g.source g.target g.peer) t}
    (old : MatchingRegistryView before) (new : MatchingRegistryView after)
    (ids : after.node = before.node) (cutoff : t.nr 39 = s.nr 39) (cursor : t.nr 76 = s.nr 76)
    (budget : MatchingRegistryBudget k stage s (matchingStageCountsFromRAM k s (s.nr 39)))
    (fresh : MatchingFreshCutOuter part forest before.node (s.nr 39)) :
    MatchingStageTransition (matchingStageCountsFromRAM k s (s.nr 39)) (1+(part.blocks.block g.peer).card)
      (matchingStageCountsFromRAM k t (t.nr 39)) ∧
    MatchingRegistryBudget k stage t (matchingStageCountsFromRAM k t (t.nr 39)) ∧
    MatchingFreshCutOuter part (forest.grow g.source g.target g.peer) after.node (t.nr 39) := by
  have transition : MatchingStageTransition (matchingStageCountsFromRAM k s (s.nr 39)) (1+(part.blocks.block g.peer).card)
      (matchingStageCountsFromRAM k t (t.nr 39)) := by
    rw [matchingStageCountsFromRAM_eq before positive _ old.trees old.unique old.keys,
      matchingStageCountsFromRAM_eq after positive _ new.trees new.unique new.keys, ids, cutoff]
    exact g.credit top positive _
  refine ⟨transition, budget.advance transition cutoff (by omega) (by omega), ?_⟩
  rw [ids, cutoff]
  intro B hB recent v hv
  have on := fresh B hB recent v hv
  have first : part.representative v ≠ g.target := by
    intro same
    rw [same, g.targetDormant] at on
    contradiction
  have last : part.representative v ≠ g.peer := by
    intro same
    rw [same, g.peerDormant] at on
    contradiction
  simpa only [AlternatingForestState.grow, if_neg first, if_neg last] using on


end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowthStageBudget

/-! matching/MatchingDispatchGrowth.lean -/
section RppSource_MatchingDispatchGrowth
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

private theorem MatchingStageStorage.nodesBeforeWitnesses {k : ℕ} {original s : ArithmeticState}
    (storage : MatchingStageStorage k original s) : s.nr 74 ≤ s.nr 90 := by
  have a := storage.starts
  have b := storage.lengths
  have c := storage.traceLeft
  have d := storage.traceRight
  have e := storage.traceMarks
  have f := storage.witnesses
  omega

/-- The typed growth choice reads its machine operands from natural memory.
The same choice describes the operands before and after saving the selected
edge and advancing the dual variables. -/
private def MatchingGrowthSelection.reframeMachine {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s t : ArithmeticState} {edge : Sym2 (Fin k)}
    (choice : MatchingGrowthSelection part forest s edge) (natural : t.nm = s.nm)
    (ports : ∀ r ∈ ([1, 50, 51, 54, 57] : List ℕ), t.nr r = s.nr r) :
    MatchingGrowthSelection part forest t edge := by
  have reg (r : ℕ) (used : r ∈ ([1, 50, 51, 54, 57] : List ℕ) := by decide) := ports r used
  have words : matchingOriginalGrowthEvent t = matchingOriginalGrowthEvent s := by
    simp only [matchingOriginalGrowthEvent, reg 1, reg 54, natural]
  have left : matchingChosenLeftBlock t = matchingChosenLeftBlock s := by
    simp only [matchingChosenLeftBlock, matchingChosenEdgeAddress, reg 1, reg 54, reg 57, natural]
  have right : matchingChosenRightBlock t = matchingChosenRightBlock s := by
    simp only [matchingChosenRightBlock, matchingChosenEdgeAddress, reg 1, reg 54, reg 57, natural]
  exact ⟨choice.source, choice.target, choice.peer, choice.parent,
    choice.sourceOuter, choice.targetDormant, choice.targetActive, choice.peerDormant,
    by simpa only [matchingChosenGrowSource, left, right, reg 51, natural] using choice.sourceWord,
    by simpa only [matchingChosenGrowTarget, left, right, reg 51, natural] using choice.targetWord,
    by simpa only [reg 50, natural] using choice.peerWord,
    choice.distinct, choice.paired, choice.reversePaired, choice.incoming, choice.matched,
    words.symm ▸ choice.leftValid,
    by simpa only [orientedMatchingOriginalGrowthEvent, words, reg 57, natural] using choice.direction,
    choice.next⟩


private theorem MatchingGrowthSelection.growAndStore {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s original : ArithmeticState} {edge : Sym2 (Fin k)}
    {positive : 0 < k} (g : MatchingGrowthSelection part forest s edge)
    (advanced : MatchingAdvancedStage part forest positive (matchingTopCutAt part) original s)
    (entry : s.pc = 0) (live : s.halted = false) (one : s.nr 9 = 1)
    (storage : MatchingStageStorage k original s) (symmetric : ∀ u v, cost u v = cost v u) :
    let newer := forest.grow g.source g.target g.peer
    let update := appendBlock applyMatchingGrowEventBlock (appendBlock saveMatchingGrowthBlocks matchingGrowthCacheRepairBlock)
    ∃ t ticks, BlockRuns (appendBlock update storeOrientedMatchingGrowthWitnesses) ticks s t ∧
      t.halted = false ∧ t.nr 1 = 0 ∧
      MatchingSearchRows part newer positive (matchingTopCutAt part) t ∧
      MatchingSearchOuterBuckets t part.representative (fun u => alternatingRoleCode (newer.role u)) cost
        (effectiveVertexPotential state.cuts state.potential state.cutDual) ∧
      MatchingRefreshInput t part.representative (fun u => alternatingRoleCode (newer.role u)) cost
        (effectiveVertexPotential state.cuts state.potential state.cutDual) ∧
      AlternatingForestMemory newer (s.nr 51) t.nm ∧
      (∀ r, r = 9 ∨ r = 20 ∨ r = 21 ∨ 29 ≤ r → t.nr r = s.nr r) ∧
      (∀ a, (a < s.nr 51 ∨ s.nr 74 ≤ a) → (a < s.nr 90 ∨ s.nr 90+2*k ≤ a) → t.nm a = s.nm a) ∧
      (∀ a, a < s.nr 59 ∨ s.nr 75 ≤ a → t.rm a = s.rm a) ∧
      (∀ v : Fin k, v ≠ g.target → v ≠ g.peer →
        matchingForestWitnessAt t.nm (t.nr 90) v.val = matchingForestWitnessAt s.nm (s.nr 90) v.val) := by
  intro newer update
  obtain ⟨u, ticks, run, running, empty, rows, pairs, reads, natural, real, _, roles, peer, target, regs⟩ :=
    g.growCaches advanced entry live one storage.warm storage.nodes.ge storage.cutDuals.ge symmetric
  let ready := {u with pc := 0}
  have reg (r : ℕ) (used : r = 9 ∨ r = 20 ∨ r = 21 ∨ 29 ≤ r := by decide) : ready.nr r = s.nr r :=
    regs r used
  have readyReads := reads.keeps (t := ready) ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
  have readyRows : MatchingSearchRows part newer positive (matchingTopCutAt part) ready :=
    ⟨readyReads.layout, rows.count, rows.ids, rows.slacks, rows.rates, rows.valid, rows.least⟩
  have readyPairs : MatchingSearchOuterBuckets ready part.representative (fun v => alternatingRoleCode (newer.role v))
      cost (effectiveVertexPotential state.cuts state.potential state.cutDual) :=
    ⟨pairs.valid, pairs.least, pairs.inactive⟩
  have nodesToWitness := storage.nodesBeforeWitnesses
  have floor : ready.nr 65+2*(k*k) ≤ ready.nr 90 := by
    rw [reg 65, reg 90]
    exact storage.nodes.ge.trans nodesToWitness
  obtain ⟨t, steps, _, stores, tLive, cleared, tRows, tPairs, tReads, written, untouched, realEq, _, ports⟩ :=
    storeOrientedMatchingGrowthWitnesses_rows (s := ready) rfl running ((reg 9).trans one)
      empty g.target g.peer target peer floor readyRows readyPairs readyReads
  let out := relocateState update.length t
  have outReads := tReads.keeps (t := out) ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
  refine ⟨out, ticks+steps, run.append stores, tLive, cleared,
    ⟨outReads.layout, tRows.count, tRows.ids, tRows.slacks, tRows.rates, tRows.valid, tRows.least⟩,
    ⟨tPairs.valid, tPairs.least, tPairs.inactive⟩, outReads, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    have hi := v.isLt
    have a := storage.warm.representativesAfter
    have b := storage.warm.candidatesAfter
    have c := storage.warm.pairsAfter
    have d := storage.nodes
    have keep (a : ℕ) (small : a < s.nr 90) : t.nm a = ready.nm a :=
      untouched a (.inl ((reg 90).symm ▸ small))
    obtain ⟨label, parent, rank⟩ := roles v
    exact ⟨(keep _ (by omega)).trans label, (keep _ (by omega)).trans parent, (keep _ (by omega)).trans rank⟩
  · exact fun r used => (ports r (by simp; omega)).trans (reg r used)
  · intro a outside saved
    exact (untouched a (by rw [reg 90]; exact saved)).trans (natural a outside)
  · exact fun a outside => (congrFun realEq a).trans (real a outside)
  · intro v offTarget offPeer
    have atOut : out.nr 90 = ready.nr 90 := ports 90 (by decide)
    change matchingForestWitnessAt t.nm (out.nr 90) v.val = _
    rw [atOut, written,
      matchingForestWitnessAt_write_other _ _ _ _ _ (fun eq => offPeer (Fin.ext eq)),
      matchingForestWitnessAt_write_other _ _ _ _ _ (fun eq => offTarget (Fin.ext eq)), reg 90]
    let address := s.nr 90 + (v.val + v.val)
    exact congrArg₂ Prod.mk (natural address (.inr (by dsimp [address]; omega)))
      (natural (address+1) (.inr (by dsimp [address]; omega)))


set_option maxRecDepth 16384 in
private theorem MatchingDispatchState.growArm {k i : ℕ} {cost : Fin k → Fin k → ℝ}
    {original s : ArithmeticState} (before : MatchingDispatchState cost original i s)
    (searching : i < k/2) (symmetric : ∀ u v, cost u v = cost v u)
    (entry : s.pc = 0) (running : s.halted = false) (grow : matchingEventClass s = 0) :
    ∃ t ticks charge, BlockRuns matchingGrowHandlerWithWitnesses ticks s t ∧
      t.halted = false ∧ t.nr 33 = s.nr 33 ∧
      Nonempty (MatchingPreparedStage cost original i (matchingStageSnapshot t)) ∧
      MatchingStageTransition (matchingStageCountsFromRAM k s (s.nr 39)) charge
        (matchingStageCountsFromRAM k (matchingStageSnapshot t) ((matchingStageSnapshot t).nr 39)) ∧
      ticks + 32 ≤ 1024 * (k+1) * charge := by
  obtain ⟨saved, save, savedLive, _, natSaved, realSaved, rrSaved, portsSaved⟩ :=
    saveMatchingGrowthOriginalEdge_spec s entry running before.one
  let a := {saved with pc := 0}
  have savedReg (r : ℕ) (safe : r ∉ ([0,6,22,23] : List ℕ) := by decide) : a.nr r = s.nr r :=
    portsSaved r safe
  have aNat : a.nm = s.nm := natSaved
  let picked := before.reframe (t := a) aNat realSaved rrSaved (savedReg 1)
    (fun r keep => savedReg r (by simp; omega))
  have aGrow : matchingEventClass a = 0 := by
    simpa only [matchingEventClass, matchingEventLeftRep, matchingEventRightRep, matchingOriginalGrowthEvent,
      savedReg 1, savedReg 51, savedReg 54, savedReg 55, savedReg 57, aNat] using! grow
  obtain ⟨dualExit, dualTicks, dualRun, _, dualLive, edge, _, selection, _, tight⟩ :=
    picked.selected.advanceGrowth picked.search picked.internal picked.top rfl savedLive picked.one picked.storage aGrow
  obtain ⟨z, _, run, _, _, _, nm, ports, advanced, ids, trees⟩ :=
    picked.selected.advance picked.search picked.internal rfl savedLive picked.one picked.storage
  have sameExit := (run.same_exit dualRun).2
  subst z
  let b := {dualExit with pc := 0}
  let advancedReady := advanced.atEntry
  have bReg (r : ℕ) (safe : r ∉ ([0,6,7,10,11,12,14] : List ℕ) := by decide) : b.nr r = a.nr r :=
    ports r safe
  have bNat : b.nm = a.nm := nm
  let delta : DualBound (MatchingDualEvent k) := ⟨picked.selected.event, a.rr 1⟩
  let state := picked.state.advanceSearch picked.part picked.search picked.positive picked.internal delta picked.selected.adjustment
  let part := picked.part.advanceSearch picked.search picked.positive picked.internal delta picked.selected.adjustment
  have nodeIds : advancedReady.dual.node = picked.selected.dual.node := ids
  have sameTrees : advancedReady.registry.trees.tree = picked.selected.registry.trees.tree := trees
  have bStorage := picked.storage.keeps (t := b)
    (fun r used => bReg r (by simp [matchingFixedStorageRegisters] at used; simp; omega))
  have top : CompactTopMatching part := ⟨picked.top.interior, picked.top.matchedBase⟩
  obtain ⟨t, suffixTicks, suffix, live, clear, rows, pairs, reads, roles, suffixRegs, natural, real, witnesses⟩ :=
    selection.growAndStore advancedReady rfl dualLive ((bReg 9).trans picked.one) bStorage symmetric
  have originalReg (r : ℕ) (safe : r ∉ ([0,6,7,10,11,12,14,22,23] : List ℕ) := by decide) :
      b.nr r = s.nr r :=
    (bReg r (by simp at safe ⊢; omega)).trans (savedReg r (by simp at safe ⊢; omega))
  have originalNat : b.nm = s.nm := bNat.trans aNat
  let chooseAt := selection.reframeMachine (t := s) originalNat.symm
    (fun r used => (originalReg r (by simp at used ⊢; omega)).symm)
  have originalRoles : AlternatingForestMemory picked.forest (s.nr 51) s.nm := by
    have encoded : AlternatingForestMemory picked.forest (b.nr 51) b.nm := advancedReady.dual.roles
    rwa [originalReg 51, originalNat] at encoded
  have originalReps (v : Fin k) : s.nm (s.nr 57+v.val) = (part.representative v).val := by
    have encoded : b.nm (b.nr 57+v.val) = (part.representative v).val := advancedReady.dual.reps v
    rwa [originalReg 57, originalNat] at encoded
  have witnessRoom : s.nr 58 ≤ s.nr 90 := by
    have a := before.storage.warm.pairsAfter
    have b := before.storage.nodes
    have c := before.storage.nodesBeforeWitnesses
    omega
  obtain ⟨raw, rawTicks, budget, rawRun, _, _, _, inner, outer, _⟩ :=
    chooseAt.run top entry running before.one advancedReady.search before.storage.warm originalRoles originalReps witnessRoom
  let out := relocateState saveMatchingGrowthOriginalEdge.length (relocateState advanceMatchingEventDuals.length t)
  have whole : BlockRuns matchingGrowHandlerWithWitnesses (6 + (dualTicks + suffixTicks)) s out :=
    save.append (dualRun.append suffix)
  have exitEq := (whole.same_exit rawRun).2
  subst raw
  let final := matchingStageSnapshot out
  let forest := picked.forest.grow selection.source selection.target selection.peer
  have snapReg (r : ℕ) (safe : r ≠ 30 := by decide) : final.nr r = t.nr r :=
    Function.update_of_ne safe _ _
  have finalReg (r : ℕ) (kept : r = 9 ∨ r = 20 ∨ r = 21 ∨ 29 ≤ r := by decide)
      (safe : r ≠ 30 := by decide) : final.nr r = b.nr r :=
    (snapReg r safe).trans (suffixRegs r kept)
  have words : matchingOriginalGrowthEvent b = matchingOriginalGrowthEvent s := by
    simp only [matchingOriginalGrowthEvent, originalReg 1, originalReg 54, originalNat]
  have innerAtFinal : matchingForestWitnessAt final.nm (final.nr 90) selection.target.val =
      orientedMatchingOriginalGrowthEvent b selection.target.val := by
    rw [finalReg 90, originalReg 90]
    simpa only [orientedMatchingOriginalGrowthEvent, words, originalReg 57, originalNat] using! inner
  have outerAtFinal : matchingForestWitnessAt final.nm (final.nr 90) selection.peer.val =
      (selection.target.val, selection.peer.val) := by
    rw [finalReg 90, originalReg 90]
    exact outer
  obtain ⟨links, edgeWitnesses⟩ := selection.forestLinks (t := final) top advancedReady.links advancedReady.witnesses
    tight innerAtFinal outerAtFinal (fun v offTarget offPeer => by
      rw [snapReg 90]
      exact witnesses v offTarget offPeer)
  have finalNat (address : ℕ) (outside : address < b.nr 51 ∨ b.nr 74 ≤ address)
      (saved : address < b.nr 90 ∨ b.nr 90+2*k ≤ address) : final.nm address = b.nm address :=
    natural address outside saved
  have finalReal (address : ℕ) (outside : address < b.nr 59 ∨ b.nr 75 ≤ address) :
      final.rm address = b.rm address := real address outside
  have headerEnd : b.nr 78 + matchingBlossomCapacity k ≤ b.nr 90 := by
    have a := bStorage.traceLeft
    have c := bStorage.traceRight
    have d := bStorage.traceMarks
    have e := bStorage.witnesses
    omega
  have nodeWord (v : Fin k) : blossomNodeAt final v = blossomNodeAt b v := by
    unfold blossomNodeAt
    rw [finalReg 74]
    have hi := v.isLt
    have first := bStorage.starts
    have counts := bStorage.lengths
    exact finalNat _ (.inr (Nat.le_add_right _ _)) (.inl (by omega))
  have finalReads := reads.keeps (t := final) ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    (fun r used => snapReg r (by simp [matchingRefreshTableRegisters] at used; omega))
  have finalRows : MatchingSearchRows part forest picked.positive (matchingTopCutAt part) final :=
    ⟨finalReads.layout, rows.count, rows.ids, rows.slacks, rows.rates, rows.valid, rows.least⟩
  have finalPairs : MatchingSearchOuterBuckets final part.representative (fun v => alternatingRoleCode (forest.role v))
      cost (effectiveVertexPotential state.cuts state.potential state.cutDual) :=
    ⟨pairs.valid, pairs.least, pairs.inactive⟩
  let dual : MatchingSearchDualMemory part forest final := {
    dimension := finalReads.layout.dimension
    separated := by
      rw [finalReg 62, finalReg 75]
      exact advancedReady.dual.separated
    reps := finalReads.representatives
    roles := by
      rw [finalReg 51]
      exact roles
    effective := finalReads.potentials
    node := advancedReady.dual.node
    nodeNonzero := advancedReady.dual.nodeNonzero
    nodeInjective := advancedReady.dual.nodeInjective
    cutValues B h := by
      rw [finalReg 75]
      exact (finalReal _ (.inr (Nat.le_add_right _ _))).trans (advancedReady.dual.cutValues B h)
    top v := (nodeWord v).trans (advancedReady.dual.top v) }
  have sameBefore : matchingStageCountsFromRAM k b (b.nr 39) = matchingStageCountsFromRAM k s (s.nr 39) := by
    rw [matchingStageCountsFromRAM_eq advancedReady.dual picked.positive _ advancedReady.registry.trees
          advancedReady.registry.unique advancedReady.registry.keys,
        matchingStageCountsFromRAM_eq before.selected.dual before.positive _ before.selected.registry.trees
          before.selected.registry.unique before.selected.registry.keys,
        nodeIds, originalReg 39]
    rfl
  have bBudget := before.budget.keeps (originalReg 39) (originalReg 76) sameBefore
  have bFresh : MatchingFreshCutOuter part picked.forest advancedReady.dual.node (b.nr 39) := by
    simpa only [nodeIds, bReg 39] using! picked.fresh
  have bOrder := picked.order.transport (s := a) (t := b)
    (by simp only [matchingRebaseScratchEnd, bReg 80, bReg 55]) (bReg 76) (bReg 68)
    (fun _ _ _ => by simp only [matchingCycleRecordStart, bReg 77, bNat])
    (fun _ _ _ => by simp only [matchingCycleRecordEnd, matchingCycleRecordStart, bReg 77, bReg 78, bNat])
  let bCycles : MatchingLiveCycles advancedReady.registry :=
    picked.cycles.advanceDual picked.search picked.positive picked.internal delta picked.selected.adjustment
      advancedReady.registry nodeIds sameTrees bNat (fun r used => bReg r (by simp at used ⊢; omega))
  let registry : MatchingRegistryView dual := advancedReady.registry.afterWitnesses
    bStorage bOrder bBudget searching rfl (finalReg 77) (finalReg 78) (finalReg 76)
    (finalReg 65) nodeWord (fun address hi off => natural address (.inr (bStorage.nodes.symm ▸ hi)) off)
  obtain ⟨transition, budgetAfter, freshAfter⟩ := selection.ramBudget picked.positive top advancedReady.registry registry
    rfl (finalReg 39) (finalReg 76) bBudget bFresh
  have firstHeader := bStorage.starts
  have secondHeader := bStorage.lengths
  have witnessEnd : b.nr 90+2*k ≤ b.nr 80 := by
    have a := bStorage.records
    have c := bStorage.promotion
    have d := bStorage.mask
    have e := bStorage.memberMap
    have f := bStorage.memberStack
    omega
  have archiveBytes (address : ℕ) (stored : matchingExpansionArchiveCell k b address) :
      final.nm address = b.nm address := by
    rcases stored with ⟨above, below⟩ | high
    · exact finalNat address (.inr (by omega)) (.inl below)
    · have nodes := bStorage.nodesBeforeWitnesses
      exact finalNat address (.inr (by omega)) (.inr (by omega))
  let cycles : MatchingLiveCycles registry := bCycles.sameNodes registry rfl rfl
    (bCycles.memoryOnExpansionArchive bStorage bOrder bBudget searching
      (fun r used => finalReg r (by simp at used; omega) (by simp at used; omega)) archiveBytes)
  have headerByte (r n : ℕ) (header : r = 77 ∨ r = 78) (allocated : n < b.nr 76) :
      final.nm (b.nr r+n) = b.nm (b.nr r+n) := by
    have fits := bBudget.allocated_fits searching allocated
    rcases header with rfl | rfl <;> exact archiveBytes _ (.inl ⟨by omega, by omega⟩)
  have starts (n : ℕ) (allocated : n < b.nr 76) :
      matchingCycleRecordStart final n = matchingCycleRecordStart b n := by
    rw [matchingCycleRecordStart, finalReg 77]
    exact headerByte 77 n (.inl rfl) allocated
  have order := bOrder.transport (s := b) (t := final)
    (by simp only [matchingRebaseScratchEnd, finalReg 80, finalReg 55]) (finalReg 76) (finalReg 68)
    (fun n _ fits => starts n fits) (fun n _ fits => by
      simp only [matchingCycleRecordEnd, starts n fits, finalReg 78, headerByte 78 n (.inr rfl) fits])
  have finalStorage := bStorage.keeps (t := final) (fun r used =>
    finalReg r (by simp [matchingFixedStorageRegisters] at used; omega)
      (by simp [matchingFixedStorageRegisters] at used; omega))
  have matesBefore := bStorage.warm.matesBefore
  have roleBeforeWitness : b.nr 51 ≤ b.nr 90 := by
    have a := bStorage.warm.representativesAfter
    have c := bStorage.warm.candidatesAfter
    have d := bStorage.warm.pairsAfter
    have e := bStorage.nodes
    have f := bStorage.nodesBeforeWitnesses
    omega
  have oldPrimal : CompactMatchingPrimalDualMemory state original b := advancedReady.primal
  have effectiveBefore : b.nr 62+k ≤ b.nr 59 := advancedReady.reads.effectiveBefore
  have primal : CompactMatchingPrimalDualMemory state original final := {
    dimension := dual.dimension
    oddMap := (finalReg 56).trans oldPrimal.oddMap
    mateAbove := by rw [finalReg 50]; exact oldPrimal.mateAbove
    mate v := by
      rw [finalReg 50]
      have hi := v.isLt
      have low : b.nr 50+v.val < b.nr 51 := by omega
      exact (finalNat _ (.inl low) (.inl (low.trans_le roleBeforeWitness))).trans (oldPrimal.mate v)
    saved r hi := (finalReg r (by omega) (by omega)).trans (oldPrimal.saved r hi)
    natural address low := by
      have space := oldPrimal.mateAbove
      have below : address < b.nr 51 := by omega
      exact (finalNat address (.inl below) (.inl (below.trans_le roleBeforeWitness))).trans (oldPrimal.natural address low)
    real address low := by
      have floor := bStorage.inputFloor
      exact (finalReal address (.inl (by omega))).trans (oldPrimal.real address low) }
  let post : MatchingActiveStage part forest picked.positive (matchingTopCutAt part) original i final :=
    ⟨primal, top, picked.internal, selection.next, edgeWitnesses, links, dual, registry, freshAfter,
      finalRows, finalPairs, finalReads, budgetAfter, clear, (finalReg 9).trans ((bReg 9).trans picked.one)⟩
  let prepared : MatchingPreparedStage cost original i final :=
    ⟨state, part, forest, picked.positive, picked.count, post, cycles, finalStorage, order⟩
  refine ⟨out, _, 1+(part.blocks.block selection.peer).card, whole, live,
    (suffixRegs 33 (by decide)).trans (originalReg 33), ⟨prepared⟩, ?_, ?_⟩
  · rw [← sameBefore]
    exact transition
  · rw [(whole.same_exit rawRun).1]
    exact budget


set_option maxRecDepth 16384 in
/-- The executable dispatcher takes a selected growth event all the way to
the next selector invocation and pays for the run from the stage credit. -/
theorem MatchingDispatchState.grow {k i : ℕ} {cost : Fin k → Fin k → ℝ}
    {original s : ArithmeticState} (before : MatchingDispatchState cost original i s)
    (searching : i < k/2) (symmetric : ∀ u v, cost u v = cost v u)
    (entry : s.pc = 0) (running : s.halted = false)
    (active : s.nr 33 ≠ 0) (grow : matchingEventClass s = 0) :
    ∃ next ticks charge, BlockRuns weightedBlossomEventHandler ticks s next ∧
      next.halted = false ∧ next.nr 33 ≠ 0 ∧
      Nonempty (MatchingPreparedStage cost original i (matchingStageSnapshot next)) ∧
      MatchingStageTransition (matchingLoopCounts k i s) charge (matchingLoopCounts k i (matchingStageSnapshot next)) ∧
      ticks ≤ 1024 * (k+1) * charge := by
  obtain ⟨middle, classifiedTicks, classified, classBound, middleLive, tag, zero, one, two, _, winner, natural,
    real, rr, ports, _⟩ := before.selected.dispatchDirect entry running before.one (Or.inl grow)
  let a := {middle with pc := 0}
  have port (r : ℕ) (used : r = 9 ∨ r = 20 ∨ r = 21 ∨ (30 ≤ r ∧ r ≤ 34) ∨
      (39 ≤ r ∧ r ≤ 90) ∨ 100 ≤ r := by decide) : a.nr r = s.nr r := ports r used
  have bytes : a.nm = s.nm := natural
  have selectedId : a.nr 1 = s.nr 1 := winner
  let picked := before.reframe (t := a) bytes real rr winner (fun r used => port r (by omega))
  have aGrow : matchingEventClass a = 0 := by
    simpa only [matchingEventClass, matchingEventLeftRep, matchingEventRightRep, matchingOriginalGrowthEvent,
      selectedId, port 51, port 54, port 55, port 57, bytes] using! grow
  obtain ⟨t, armTicks, charge, arm, live, activeAtExit, prepared, transition, armBound⟩ :=
    picked.growArm searching symmetric rfl middleLive aGrow
  have tagAt : a.nr 35 = 0 := tag.trans grow
  have armByTag : BlockRuns (match a.nr 35 with
      | 0 => matchingGrowHandlerWithWitnesses
      | 1 => matchingContractionHandlerBlock
      | 2 => matchingExpandHandlerBlock
      | _ => matchingAugmentationHandlerBlock) armTicks a t := by
    rw [tagAt]
    exact arm
  obtain ⟨dispatchTicks, dispatchBound, dispatched⟩ :=
    dispatchMatchingActionBlock_spec (s := a) (t := t) rfl middleLive live
      zero one two (by omega) armByTag
  have countEq : matchingStageCountsFromRAM k a (a.nr 39) =
      matchingStageCountsFromRAM k s (s.nr 39) := by
    rw [matchingStageCountsFromRAM_eq picked.selected.dual picked.positive _
          picked.selected.registry.trees picked.selected.registry.unique picked.selected.registry.keys,
        matchingStageCountsFromRAM_eq before.selected.dual before.positive _
          before.selected.registry.trees before.selected.registry.unique before.selected.registry.keys,
        port 39]
    rfl
  refine ⟨_, classifiedTicks + dispatchTicks, charge, classified.append dispatched, live,
    ?_, prepared, ?_, by omega⟩
  · exact fun off => active ((activeAtExit.trans (port 33)).symm.trans off)
  · change MatchingStageTransition (matchingStageCountsFromRAM k s (s.nr 39)) charge
      (matchingStageCountsFromRAM k (matchingStageSnapshot t) ((matchingStageSnapshot t).nr 39))
    rw [← countEq]
    exact transition

end VehicleRoutingSurvey.Routing
end RppSource_MatchingDispatchGrowth

open VehicleRoutingSurvey.Routing in
theorem solution {k i : ℕ} {cost : Fin k → Fin k → ℝ}
    {original s : ArithmeticState} (before : MatchingDispatchState cost original i s)
    (searching : i < k/2) (symmetric : ∀ u v, cost u v = cost v u)
    (entry : s.pc = 0) (running : s.halted = false)
    (active : s.nr 33 ≠ 0) (grow : matchingEventClass s = 0) :
    ∃ next ticks charge, BlockRuns weightedBlossomEventHandler ticks s next ∧
      next.halted = false ∧ next.nr 33 ≠ 0 ∧
      Nonempty (MatchingPreparedStage cost original i (matchingStageSnapshot next)) ∧
      MatchingStageTransition (matchingLoopCounts k i s) charge (matchingLoopCounts k i (matchingStageSnapshot next)) ∧
      ticks ≤ 1024 * (k+1) * charge :=
  VehicleRoutingSurvey.Routing.MatchingDispatchState.grow before searching symmetric entry running active grow
