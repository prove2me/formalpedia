-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.MatchingDispatchState.expand
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T16:02:59.208181+00:00
-- url     : https://prove2.me/submissions/65a3fd16-f35b-4b39-b2c1-c2197131c691

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces
import Theorems.Thm_VehicleRoutingSurvey_Routing_MatchingSelectedExpansion_openedCore
import Theorems.Thm_VehicleRoutingSurvey_Routing_MatchingExpansionChildPorts_searchRows

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

/-! matching/MatchingSearchTopology.lean -/
section RppSource_MatchingSearchTopology
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory











theorem CompactMatchingPrimalDual.InternalCuts.eraseZeroCut {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (internal : state.InternalCuts)
    {B : Finset (Fin k)} (present : B ∈ state.cuts) (zero : state.cutDual B = 0) :
    (state.eraseZeroCut present zero).InternalCuts :=
  fun S member => internal S (Finset.mem_of_mem_erase member)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingSearchTopology

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

/-- The original matching still has a single exposed port on each new top
block after expansion, including blocks that were outside the selected cut. -/
theorem CompactTopMatching.openZeroCut {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    (matching : CompactTopMatching part)
    {B : Finset (Fin k)} (top : B ∈ Finset.univ.image part.blocks.block)
    (present : B ∈ state.cuts) (zero : state.cutDual B = 0)
    (children : MatchingExpansionChildren state B) :
    CompactTopMatching (part.openZeroCut top present zero children) := by
  have block := part.openZeroCut_block top present zero children
  have representative (v : Fin k) : (part.openZeroCut top present zero children).representative v =
      if v ∈ B then children.representative v else part.representative v := rfl
  constructor
  · intro v w member different
    rw [block] at member
    rw [representative] at different
    by_cases hv : v ∈ B
    · rw [if_pos hv] at member different
      simpa only [block, if_pos hv, show (state.eraseZeroCut present zero).edges = state.edges from rfl] using children.interior v hv w member different
    · rw [if_neg hv] at member different
      simpa only [block, if_neg hv, show (state.eraseZeroCut present zero).edges = state.edges from rfl] using matching.interior v w member different
  · intro v w base mate same
    rw [representative] at base
    rw [state.partialMate_eraseZeroCut present zero] at mate
    rw [block, block] at same
    by_cases hv : v ∈ B <;> by_cases hw : w ∈ B
    · rw [if_pos hv] at base
      rw [if_pos hv, if_pos hw] at same
      have incident := children.self w hw
      rw [← same] at incident
      exact children.matchedBase v hv w (base.symm ▸ mate) incident
    · rw [if_pos hv, if_neg hw] at same
      exact hw (children.subset v hv (same.symm ▸ part.blocks.self_mem w (Finset.mem_univ w)))
    · rw [if_neg hv, if_pos hw] at same
      exact hv (children.subset w hw (same ▸ part.blocks.self_mem v (Finset.mem_univ v)))
    · rw [if_neg hv] at base
      rw [if_neg hv, if_neg hw] at same
      exact matching.matchedBase base mate same

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionPartition

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

/-! matching/MatchingMemberTopRAM.lean -/
section RppSource_MatchingMemberTopRAM
namespace VehicleRoutingSurvey.Routing

def topMatchingMemberNodeInput (s : ArithmeticState) : ArithmeticState :=
  let address := s.nr 74 + s.nr 97
  {s with pc := 0, nr := Function.update (Function.update s.nr 6 address) 22 (s.nm address)}



end VehicleRoutingSurvey.Routing
end RppSource_MatchingMemberTopRAM

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



end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestGrowPairs

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



end VehicleRoutingSurvey.Routing
end RppSource_ExpansionArcRAM

/-! matching/ExpansionParentModel.lean -/
section RppSource_ExpansionParentModel
namespace VehicleRoutingSurvey.Routing





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





end VehicleRoutingSurvey.Routing
end RppSource_ExpansionParentModel

/-! matching/ExpansionArcRecords.lean -/
section RppSource_ExpansionArcRecords
namespace VehicleRoutingSurvey.Routing









/-- The persistent cycle rows couple each child with the oriented original edge
from that child to the next, modulo the physical cycle length. -/
structure ExpansionCycleWitnessRows {k : ℕ} (s : ArithmeticState) (cycle : List (Fin k))
    (edges : Fin cycle.length → Fin k × Fin k) : Prop where
  length : expansionRegisteredCycleLength s = cycle.length
  records : ∀ i : Fin cycle.length,
    let row := matchingCycleChildAt s.nm (expansionRegisteredCycleBase s + 4 * i.val)
    row.representative = cycle[i.val].val ∧
      (row.endpointA, row.endpointB) = ((edges i).1.val, (edges i).2.val)





end VehicleRoutingSurvey.Routing
end RppSource_ExpansionArcRecords

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

/-! matching/MatchingExpansionHandler.lean -/
section RppSource_MatchingExpansionHandler
namespace VehicleRoutingSurvey.Routing

def selectedExpansionBaseState (s : ArithmeticState) : ArithmeticState :=
  {s with pc := 0, nr := Function.update s.nr 97 (s.nr 92)}









end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionHandler

/-! matching/ExpansionMemberSemantics.lean -/
section RppSource_ExpansionMemberSemantics
namespace VehicleRoutingSurvey.Routing



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

theorem ExpansionPublication.keepsMembers {s t : ArithmeticState}
    (publication : ExpansionPublication s t)
    (before : s.nr 57 + s.nr 55 ≤ s.nr 79) (nodes : s.nr 74 + s.nr 55 ≤ s.nr 79)
    (bounded : ∀ j < s.nr 19, (expansionCycleRow s j).representative < s.nr 55) (v : ℕ) :
    t.nm (t.nr 79 + v) = s.nm (s.nr 79 + v) := by
  rw [publication.fixed 79 (by decide)]
  apply publication.natural _ (.inr (by omega))
  intro j hj
  have size := bounded j hj
  omega

theorem MatchingExpandedForest.keepsMembers {k : ℕ} {s t : ArithmeticState}
    {forest : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)}
    {tightRep tightOriginal : Sym2 (Fin k) → Prop} {rep : Fin k → Fin k}
    (expanded : MatchingExpandedForest forest mate tightRep tightOriginal rep s t)
    (role : s.nr 51 + 3 * k ≤ s.nr 79) (witness : s.nr 90 + 2 * k ≤ s.nr 79) (v : ℕ) :
    t.nm (t.nr 79 + v) = s.nm (s.nr 79 + v) := by
  rw [expanded.fixed 79 (by decide)]
  exact expanded.natural _ (.inr (by omega)) (.inr (by omega))





end VehicleRoutingSurvey.Routing
end RppSource_ExpansionMemberSemantics

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

/-! matching/BlossomCreditExpansion.lean -/
section RppSource_BlossomCreditExpansion
namespace VehicleRoutingSurvey.Routing

/-- Expanding an inherited inner blossom preserves all current outer
blocks. Every additional outer block accounts for a newly outer vertex. -/
theorem matchingPartitionCounts_expand {k : ℕ} {vertices : Finset (Fin k)}
    {oldCuts newCuts inherited : Finset (Finset (Fin k))}
    (blocks : TopLevelMatchingBlocks vertices oldCuts) (opened : TopLevelMatchingBlocks vertices newCuts)
    (before after : Finset (Fin k) → Prop) [DecidablePred before] [DecidablePred after]
    {blossom : Finset (Fin k)} (inheritedMember : blossom ∈ inherited)
    (keepsOuter : ∀ v ∈ vertices, before (blocks.block v) →
      after (opened.block v) ∧ opened.block v = blocks.block v) :
    let pendingBefore := vertices.filter (fun v => ¬before (blocks.block v))
    let pendingAfter := vertices.filter (fun v => ¬after (opened.block v))
    MatchingStageTransition (matchingPartitionCounts blocks before inherited)
      (1 + (pendingBefore \ pendingAfter).card)
      (matchingPartitionCounts opened after (inherited.erase blossom)) := by
  intro oldNonouter newNonouter
  let fresh := oldNonouter \ newNonouter
  let oldOuter := (vertices.image blocks.block).filter before
  let newOuter := (vertices.image opened.block).filter after
  have fewerPending : newNonouter ⊆ oldNonouter := by
    intro v pending
    obtain ⟨inside, noAfter⟩ := Finset.mem_filter.mp pending
    exact Finset.mem_filter.mpr ⟨inside, fun found => noAfter (keepsOuter v inside found).1⟩
  have vertexCounts : oldNonouter.card = newNonouter.card + fresh.card := by
    have counts := Finset.card_sdiff_add_card_eq_card fewerPending
    rw [Nat.add_comm]
    exact counts.symm
  have outerCover : newOuter ⊆ oldOuter ∪ fresh.image opened.block := by
    intro B found
    obtain ⟨visible, nowOuter⟩ := Finset.mem_filter.mp found
    obtain ⟨v, inVertices, identifies⟩ := Finset.mem_image.mp visible
    by_cases wasOuter : before (blocks.block v)
    · have old : blocks.block v = B := (keepsOuter v inVertices wasOuter).2.symm.trans identifies
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨v, inVertices, old⟩, old ▸ wasOuter⟩)
    · have newly : v ∈ fresh := Finset.mem_sdiff.mpr
        ⟨Finset.mem_filter.mpr ⟨inVertices, wasOuter⟩,
          fun past => (Finset.mem_filter.mp past).2 (identifies.symm ▸ nowOuter)⟩
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, newly, identifies⟩)
  have outerCounts : newOuter.card ≤ oldOuter.card + fresh.card :=
    (Finset.card_le_card outerCover).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left Finset.card_image_le _))
  have fewerInherited : (inherited.erase blossom).card < inherited.card := by
    have counts := Finset.card_erase_add_one inheritedMember
    omega
  exact MatchingStageTransition.expand fresh.card vertexCounts outerCounts fewerInherited

end VehicleRoutingSurvey.Routing
end RppSource_BlossomCreditExpansion

/-! matching/MatchingExpansionStage.lean -/
section RppSource_MatchingExpansionStage
namespace VehicleRoutingSurvey.Routing

theorem not_on_blossom_expansion {α : Type*} {base vertex : α} {children : List α}
    (entry : ℕ) (outside : vertex ∉ base :: children) :
    vertex ∉ (blossomExpansionPath base (base :: children) entry).dropLast := by
  intro member
  have found := (List.dropLast_sublist _).subset member
  by_cases reverse : entry % 2 = 0
  · rw [blossomExpansionPath, if_pos reverse] at found
    exact outside ((List.take_sublist _ _).subset (List.mem_reverse.mp found))
  · rw [blossomExpansionPath, if_neg reverse] at found
    rcases List.mem_append.mp found with afterEntry | atBase
    · exact outside ((List.drop_sublist _ _).subset afterEntry)
    · have atBase := List.mem_singleton.mp atBase
      exact outside (List.mem_cons.mpr (Or.inl atBase))





end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionStage

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

theorem MatchingExpansionChildPorts.outside_port_avoids_cycle {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {B : Finset (Fin k)}
    {part : CompactMatchingPartition state} (registry : MatchingExpansionChildPorts state B)
    (top : B ∈ Finset.univ.image part.blocks.block) (cycle : List (Fin k))
    (ports : registry.ports = cycle.toFinset) {v : Fin k} (outside : v ∉ B) :
    part.representative v ∉ cycle := by
  intro found
  have port : part.representative v ∈ registry.ports := ports.symm ▸ List.mem_toFinset.mpr found
  have member := registry.subset _ port (registry.containsPort _ port)
  have same := part.blocks.same_of_mem (Finset.mem_univ v) (part.inside v)
  have isCut := (part.block_eq_iff_member top (part.representative v)).mpr member
  exact outside ((part.block_eq_iff_member top v).mp (same.symm.trans isCut))

/-- Opening the selected inner cut keeps both representatives and forest roles
on its complement. These are the source rows already present in the cache. -/
theorem MatchingExpansionChildPorts.keepsOutsideRoles {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {B : Finset (Fin k)}
    {part : CompactMatchingPartition state} (registry : MatchingExpansionChildPorts state B)
    (top : B ∈ Finset.univ.image part.blocks.block)
    (present : B ∈ state.cuts) (zero : state.cutDual B = 0)
    (internal : state.InternalCuts)
    (external : ∀ p ∈ registry.ports, ∀ w, state.partialMate p = some w → w ∉ registry.block p)
    (forest : AlternatingForestState (Fin k)) (source base : Fin k)
    (children : List (Fin k)) (entry : ℕ)
    (ports : registry.ports = (base :: children).toFinset)
    (v : Fin k) (outside : v ∉ B) :
    let opened := part.openZeroCut top present zero (registry.toExpansionChildren internal external)
    let expanded := forest.expandBlossom source base children entry
    opened.representative v = part.representative v ∧
      expanded.role (opened.representative v) = forest.role (part.representative v) := by
  intro opened expanded
  have away := registry.outside_port_avoids_cycle top (base :: children) ports outside
  have noBase : part.representative v ≠ base := fun eq => away (eq.symm ▸ List.mem_cons_self)
  have same : opened.representative v = part.representative v := by
    change (if v ∈ B then registry.owner v else part.representative v) = part.representative v
    rw [if_neg outside]
  refine ⟨same, ?_⟩
  rw [same]
  exact forest.expandAlong_keeps_role source base _ _ (not_on_blossom_expansion entry away) noBase

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionOwnerMap

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

/-! matching/ExpansionIncomingRAM.lean -/
section RppSource_ExpansionIncomingRAM
namespace VehicleRoutingSurvey.Routing





def expansionOriginalHasRole (s : ArithmeticState) (role v : ℕ) : Prop :=
  expansionChildOf s v < s.nr 55 ∧ expansionRepRole s (expansionChildOf s v) = role

noncomputable def expansionIncomingNat (s : ArithmeticState) (count address : ℕ) : ℕ := by
  classical
  exact if ∃ v < count, address = s.nr 58 + (s.nr 55 + v) ∧ expansionOriginalHasRole s 1 v then
    0 else s.nm address

noncomputable def expansionIncomingReal (s : ArithmeticState) (count address : ℕ) : ℝ := by
  classical
  exact if ∃ v < count, address = s.nr 60 + (s.nr 55 + v) ∧ expansionOriginalHasRole s 0 v then
    1 else s.rm address

open Classical in
theorem expansionIncomingCell_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0) :
    ∃ t steps, BlockRuns expansionIncomingCell steps s t ∧ t.halted = false ∧ steps ≤ 11 ∧
      t.nm = (if expansionOriginalHasRole s 1 (s.nr 7) then
        Function.update s.nm (s.nr 58 + (s.nr 55 + s.nr 7)) 0 else s.nm) ∧
      t.rm = (if expansionOriginalHasRole s 0 (s.nr 7) then
        Function.update s.rm (s.nr 60 + (s.nr 55 + s.nr 7)) 1 else s.rm) ∧
      ∀ r, r ∉ [0, 6, 10, 11, 19] → t.nr r = s.nr r := by
  classical
  let c := expansionChildOf s (s.nr 7)
  let role := expansionRepRole s c
  by_cases outside : s.nr 55 ≤ c
  · let t := (arithmeticStep expansionIncomingCell)^[3] s
    have outsideMap : s.nr 55 ≤ s.nm (s.nr 79 + s.nr 7) := outside
    have result : t.pc = expansionIncomingCell.length ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm := by
      simp [t, expansionIncomingCell, arithmeticStep, Function.iterate_succ_apply', entry, running, outsideMap]
    refine ⟨t, 3, BlockRuns.of_running_exit rfl result.2.1 result.1, result.2.1, by decide,
      ?_, ?_, fun r safe => arithmeticRun_keeps_from_destination_list _ (by decide) safe s 3⟩
    · have skip : ¬expansionOriginalHasRole s 1 (s.nr 7) := fun h => (Nat.not_lt.mpr outside) h.1
      rw [if_neg skip]; exact result.2.2.1
    · have skip : ¬expansionOriginalHasRole s 0 (s.nr 7) := fun h => (Nat.not_lt.mpr outside) h.1
      rw [if_neg skip]; exact result.2.2.2
  · have childWithin : c < s.nr 55 := Nat.lt_of_not_ge outside
    have direct : ¬s.nr 55 ≤ s.nm (s.nr 79 + s.nr 7) := outside
    by_cases unlabelled : role = 0
    · let t := (arithmeticStep expansionIncomingCell)^[11] s
      have atRole : s.nm (s.nr 51 + s.nm (s.nr 79 + s.nr 7)) = 0 := unlabelled
      have result : t.pc = expansionIncomingCell.length ∧ t.halted = false ∧ t.nm = s.nm ∧
          t.rm = Function.update s.rm (s.nr 60 + (s.nr 55 + s.nr 7)) 1 := by
        simp [t, expansionIncomingCell, arithmeticStep, Function.iterate_succ_apply', entry, running, zero,
          direct, atRole]
      refine ⟨t, 11, BlockRuns.of_running_exit rfl result.2.1 result.1, result.2.1, le_rfl,
        ?_, ?_, fun r safe => arithmeticRun_keeps_from_destination_list _ (by decide) safe s 11⟩
      · have no : ¬expansionOriginalHasRole s 1 (s.nr 7) := by
          intro h
          have different : role = 1 := h.2
          omega
        rw [if_neg no]; exact result.2.2.1
      · have yes : expansionOriginalHasRole s 0 (s.nr 7) := ⟨childWithin, unlabelled⟩
        rw [if_pos yes]; exact result.2.2.2
    · have active : ¬s.nm (s.nr 51 + s.nm (s.nr 79 + s.nr 7)) ≤ 0 := by change ¬role ≤ 0; omega
      by_cases outer : role = 1
      · let t := (arithmeticStep expansionIncomingCell)^[11] s
        have atRole : s.nm (s.nr 51 + s.nm (s.nr 79 + s.nr 7)) = 1 := outer
        have result : t.pc = expansionIncomingCell.length ∧ t.halted = false ∧
            t.nm = Function.update s.nm (s.nr 58 + (s.nr 55 + s.nr 7)) 0 ∧ t.rm = s.rm := by
          simp [t, expansionIncomingCell, arithmeticStep, Function.iterate_succ_apply', entry, running, zero,
            one, direct, atRole]
        refine ⟨t, 11, BlockRuns.of_running_exit rfl result.2.1 result.1, result.2.1, le_rfl,
          ?_, ?_, fun r safe => arithmeticRun_keeps_from_destination_list _ (by decide) safe s 11⟩
        · have yes : expansionOriginalHasRole s 1 (s.nr 7) := ⟨childWithin, outer⟩
          rw [if_pos yes]; exact result.2.2.1
        · have no : ¬expansionOriginalHasRole s 0 (s.nr 7) := fun h => unlabelled h.2
          rw [if_neg no]; exact result.2.2.2
      · let t := (arithmeticStep expansionIncomingCell)^[8] s
        have inner : ¬s.nm (s.nr 51 + s.nm (s.nr 79 + s.nr 7)) ≤ 1 := by change ¬role ≤ 1; omega
        have result : t.pc = expansionIncomingCell.length ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm := by
          simp [t, expansionIncomingCell, arithmeticStep, Function.iterate_succ_apply', entry, running, zero,
            one, direct, active, inner]
        refine ⟨t, 8, BlockRuns.of_running_exit rfl result.2.1 result.1, result.2.1, by decide,
          ?_, ?_, fun r safe => arithmeticRun_keeps_from_destination_list _ (by decide) safe s 8⟩
        · have no : ¬expansionOriginalHasRole s 1 (s.nr 7) := fun h => outer h.2
          rw [if_neg no]; exact result.2.2.1
        · have no : ¬expansionOriginalHasRole s 0 (s.nr 7) := fun h => unlabelled h.2
          rw [if_neg no]; exact result.2.2.2

private theorem existsEarlierOrNow (P : ℕ → Prop) (i : ℕ) :
    (∃ j < i + 1, P j) ↔ (∃ j < i, P j) ∨ P i := by
  constructor
  · rintro ⟨j, within, p⟩
    obtain earlier | eq := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ within)
    · exact Or.inl ⟨j, earlier, p⟩
    · exact Or.inr (eq ▸ p)
  · rintro (⟨j, earlier, p⟩ | now)
    · exact ⟨j, by omega, p⟩
    · exact ⟨i, by omega, now⟩

private structure ExpansionIncomingScan (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 7 = i
  fixed : ∀ r, r ∉ [0, 6, 7, 10, 11, 19] → s.nr r = initial.nr r
  natural : ∀ a, s.nm a = expansionIncomingNat initial i a
  real : ∀ a, s.rm a = expansionIncomingReal initial i a

/-- Convert affected dormant rows to rate one and discard incoming rows of
newly outer originals. The old inner rows already have rate zero. -/
theorem restoreExpansionIncomingRates_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (forestBelow : s.nr 51 + s.nr 55 ≤ s.nr 58)
    (mapAbove : s.nr 58 + 2 * s.nr 55 ≤ s.nr 79) :
    ∃ t steps, BlockRuns restoreExpansionIncomingRates steps s t ∧ t.halted = false ∧
      steps ≤ 14 * s.nr 55 + 2 ∧ (∀ a, t.nm a = expansionIncomingNat s (s.nr 55) a) ∧
      (∀ a, t.rm a = expansionIncomingReal s (s.nr 55) a) ∧
      ∀ r, r ∉ [0, 6, 7, 10, 11, 19] → t.nr r = s.nr r := by
  classical
  let inv := ExpansionIncomingScan s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, ?_, ?_⟩
    · intro r away
      exact Function.update_of_ne (by simp at away; omega) _ _
    · intro a; simp [expansionIncomingNat]
    · intro a; simp [expansionIncomingReal]
  have control (i : ℕ) (m : ArithmeticState) (h : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 55 = s.nr 55 :=
    ⟨h.entry, h.running, h.index, h.fixed 55 (by decide)⟩
  have next (i : ℕ) (within : i < s.nr 55) (m : ArithmeticState) (h : inv i m) :
      ∃ t steps, steps ≤ 11 ∧ BlockRuns expansionIncomingCell steps m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    obtain ⟨t, steps, runs, live, budget, nat, real, fixed⟩ := expansionIncomingCell_spec h.entry h.running
      ((h.fixed 9 (by decide)).trans one) ((h.fixed 14 (by decide)).trans zero)
    have outsideNat (addr : ℕ) (safe : addr < s.nr 58 ∨ s.nr 58 + 2 * s.nr 55 ≤ addr) :
        m.nm addr = s.nm addr := by
      rw [h.natural, expansionIncomingNat, if_neg]
      rintro ⟨j, hj, eq, _⟩
      omega
    have child : expansionChildOf m (m.nr 7) = expansionChildOf s i := by
      rw [expansionChildOf, h.fixed 79 (by decide), h.index, outsideNat _ (.inr (by omega))]
      rfl
    have sameRole (role : ℕ) : expansionOriginalHasRole m role (m.nr 7) ↔ expansionOriginalHasRole s role i := by
      unfold expansionOriginalHasRole
      rw [child, h.fixed 55 (by decide), expansionRepRole, h.fixed 51 (by decide)]
      have read (bound : expansionChildOf s i < s.nr 55) :
          m.nm (s.nr 51 + expansionChildOf s i) = expansionRepRole s (expansionChildOf s i) :=
        outsideNat _ (.inl (by omega))
      exact and_congr_right (fun bound => by rw [read bound])
    refine ⟨t, steps, budget, runs, live, rfl, live, ?_, ?_, ?_, ?_⟩
    · simp [fixed 7 (by decide), fixed 9 (by decide), h.index, h.fixed 9 (by decide), one]
    · intro r away
      change Function.update t.nr 7 (t.nr 7 + t.nr 9) r = s.nr r
      rw [Function.update_of_ne (by simp at away; omega : r ≠ 7)]
      exact (fixed r (by simp at away ⊢; omega)).trans (h.fixed r away)
    · intro addr
      change t.nm addr = _
      rw [nat, h.fixed 58 (by decide), h.fixed 55 (by decide)]
      simp only [sameRole, expansionIncomingNat, existsEarlierOrNow]
      by_cases outer : expansionOriginalHasRole s 1 i <;>
        by_cases writes : addr = s.nr 58 + (s.nr 55 + i) <;>
        simp only [h.index, outer, writes, if_true, if_false, h.natural, expansionIncomingNat,
          Function.update_apply, and_true, and_false, true_and, false_and, or_true, or_false]
    · intro addr
      change t.rm addr = _
      rw [real, h.fixed 60 (by decide), h.fixed 55 (by decide)]
      simp only [sameRole, expansionIncomingReal, existsEarlierOrNow]
      by_cases free : expansionOriginalHasRole s 0 i <;>
        by_cases writes : addr = s.nr 60 + (s.nr 55 + i) <;>
        simp only [h.index, free, writes, if_true, if_false, h.real, expansionIncomingReal,
          Function.update_apply, and_true, and_false, true_and, false_and, or_true, or_false]
  obtain ⟨_, steps, result, budget, runs⟩ := countedLoopFromZero_bounded 9 7 55 (s.nr 55) 11
    expansionIncomingCell inv entry running initial control next
  exact ⟨_, steps, runs, result.running, by omega, result.natural, result.real, result.fixed⟩

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionIncomingRAM

/-! matching/ExpansionCutRAM.lean -/
section RppSource_ExpansionCutRAM
namespace VehicleRoutingSurvey.Routing

def expansionCutReadyFull (s : ArithmeticState) : ArithmeticState :=
  let pointer := Function.update s.nr 6 (s.nr 79 + s.nr 7)
  let owner := Function.update pointer 10 (expansionChildOf s (s.nr 7))
  let representative := Function.update owner 28 (s.nr 7)
  let labelPointer := Function.update representative 6 (s.nr 51 + s.nr 7)
  { s with pc := 0, nr := Function.update labelPointer 19 (expansionRepRole s (s.nr 7)) }

noncomputable def expansionCutNat (s : ArithmeticState) : ℕ → ℕ :=
  if expansionChildOf s (s.nr 7) ≠ s.nr 7 then s.nm
  else if expansionRepRole s (s.nr 7) ≤ 1 then
    Function.update s.nm (s.nr 58 + (s.nr 55 + s.nr 55 + s.nr 7)) 0
  else installedMatchingInnerCutNat (expansionCutReadyFull s)

noncomputable def expansionCutReal (s : ArithmeticState) : ℕ → ℝ :=
  if expansionChildOf s (s.nr 7) ≠ s.nr 7 ∨ expansionRepRole s (s.nr 7) ≤ 1 then s.rm
  else installedMatchingInnerCutReal (expansionCutReadyFull s)

private theorem expandCutClear_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 14 = 0) :
    ∃ t, BlockRuns clearExpansionCut 4 s t ∧ t.halted = false ∧
      t.nm = Function.update s.nm (s.nr 58 + innerCutCandidateSlot s) 0 ∧ t.rm = s.rm := by
  let t := (arithmeticStep clearExpansionCut)^[4] s
  have computes : t.pc = clearExpansionCut.length ∧ t.halted = false ∧
      t.nm = Function.update s.nm (s.nr 58 + innerCutCandidateSlot s) 0 ∧ t.rm = s.rm := by
    simp [t, clearExpansionCut, innerCutCandidateSlot, arithmeticStep, Function.iterate_succ_apply',
      entry, running, zero]
  exact ⟨t, BlockRuns.of_running_exit rfl computes.2.1 computes.1, computes.2⟩

theorem restoreExpansionCutCell_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0) :
    ∃ t steps, BlockRuns restoreExpansionCutCell steps s t ∧ t.halted = false ∧
      steps ≤ 32 ∧ t.nm = expansionCutNat s ∧ t.rm = expansionCutReal s ∧
      ∀ r, r ∉ [0, 6, 10, 15, 16, 18, 19, 28] → t.nr r = s.nr r := by
  let pointer := Function.update s.nr 6 (s.nr 79 + s.nr 7)
  let read := { s with pc := 0, nr := Function.update pointer 10 (expansionChildOf s (s.nr 7)) }
  have reads : BlockRuns readExpansionCutOwner 2 s {read with pc := 2} := by
    apply BlockRuns.of_running_exit
    · simp [read, pointer, readExpansionCutOwner, expansionChildOf, arithmeticStep, Function.iterate_succ_apply', entry, running]
    · exact running
    · rfl
  have owner : read.nr 10 = expansionChildOf s (s.nr 7) := by simp [read, pointer]
  have index : read.nr 7 = s.nr 7 := by simp [read, pointer]
  have noOp : BlockRuns [] 0 read read := ⟨fun _ h => (Nat.not_lt_zero _ h).elim, by simp, rfl⟩
  have fixed {t : ArithmeticState} {steps : ℕ} (runs : BlockRuns restoreExpansionCutCell steps s t)
      (r : ℕ) (outside : r ∉ [0, 6, 10, 15, 16, 18, 19, 28]) : t.nr r = s.nr r := by
    rw [← runs.run]
    exact arithmeticRun_keeps_from_destination_list _ (by decide) outside s steps
  rcases lt_trichotomy (expansionChildOf s (s.nr 7)) (s.nr 7) with earlier | atRep | later
  · have inactive := branchOnAtMost_right 7 10 handleExpansionCutRepresentative [] (s := read) rfl running
      (by rwa [owner, index]) noOp running
    have runs : BlockRuns restoreExpansionCutCell _ s _ := reads.append
      (branchOnAtMost_left 10 7 _ [] (s := read) rfl running (by rw [owner, index]; exact earlier.le) inactive running)
    refine ⟨_, _, runs, running, by decide, ?_, ?_, fixed runs⟩
    · change s.nm = expansionCutNat s
      simp [expansionCutNat, earlier.ne]
    · change s.rm = expansionCutReal s
      simp [expansionCutReal, earlier.ne]
  · let a := expansionCutReadyFull s
    have roles : BlockRuns readExpansionCutRole 3 read {a with pc := 3} := by
      apply BlockRuns.of_running_exit
      · simp [read, pointer, a, expansionCutReadyFull, readExpansionCutRole, expansionRepRole, arithmeticStep,
          Function.iterate_succ_apply', running, zero]
      · exact running
      · rfl
    have role : a.nr 19 = expansionRepRole s (s.nr 7) := by simp [a, expansionCutReadyFull]
    have aOne : a.nr 9 = 1 := by simp [a, expansionCutReadyFull, one]
    have aZero : a.nr 14 = 0 := by simp [a, expansionCutReadyFull, zero]
    by_cases inner : expansionRepRole s (s.nr 7) ≤ 1
    · obtain ⟨t, clears, live, nat, real⟩ := expandCutClear_spec (s := a) rfl running aZero
      have handler := roles.append (branchOnAtMost_left 19 9 clearExpansionCut activateMatchingInnerCut
        (s := a) rfl running (by simpa only [role, aOne] using inner) clears live)
      have lower := branchOnAtMost_left 7 10 handleExpansionCutRepresentative [] (s := read) rfl running
        (by rw [owner, index, atRep]) handler live
      have total : BlockRuns restoreExpansionCutCell _ s _ := reads.append
        (branchOnAtMost_left 10 7 _ [] (s := read) rfl running (by rw [owner, index, atRep]) lower live)
      refine ⟨_, _, total, live, by decide, ?_, ?_, fixed total⟩
      · change t.nm = _
        rw [nat]
        simp [expansionCutNat, atRep, inner, innerCutCandidateSlot, a, expansionCutReadyFull]
      · change t.rm = _
        rw [real]
        simp [expansionCutReal, atRep, inner, a, expansionCutReadyFull]
    · obtain ⟨t, steps, cost, cuts, live, nat, real⟩ := activateMatchingInnerCut_spec a rfl running aOne aZero
      have handler := roles.append (branchOnAtMost_right 19 9 clearExpansionCut activateMatchingInnerCut
        (s := a) rfl running (by rw [role, aOne]; exact Nat.lt_of_not_ge inner) cuts live)
      have lower := branchOnAtMost_left 7 10 handleExpansionCutRepresentative [] (s := read) rfl running
        (by rw [owner, index, atRep]) handler live
      have total : BlockRuns restoreExpansionCutCell _ s _ := reads.append
        (branchOnAtMost_left 10 7 _ [] (s := read) rfl running (by rw [owner, index, atRep]) lower live)
      refine ⟨_, _, total, live, by omega, ?_, ?_, fixed total⟩
      · change t.nm = _
        rw [nat]
        simp [expansionCutNat, atRep, inner, a]
      · change t.rm = _
        rw [real]
        simp [expansionCutReal, atRep, inner, a]
  · have total : BlockRuns restoreExpansionCutCell _ s _ := reads.append
      (branchOnAtMost_right 10 7 _ [] (s := read) rfl running (by rwa [owner, index]) noOp running)
    refine ⟨_, _, total, running, by decide, ?_, ?_, fixed total⟩
    · change s.nm = expansionCutNat s
      simp [expansionCutNat, later.ne']
    · change s.rm = expansionCutReal s
      simp [expansionCutReal, later.ne']









end VehicleRoutingSurvey.Routing
end RppSource_ExpansionCutRAM

/-! matching/ExpansionFreshRAM.lean -/
section RppSource_ExpansionFreshRAM
namespace VehicleRoutingSurvey.Routing



theorem freshExpansionOriginals_card {k : ℕ} {s : ArithmeticState} (dim : s.nr 55 = k)
    (fresh : Finset (Fin k)) (encoded : ∀ v : Fin k, expansionOriginalHasRole s 1 v.val ↔ v ∈ fresh) :
    (freshExpansionOriginals s (s.nr 55)).length = fresh.card := by
  let pick := fun v => decide (expansionChildOf s v < s.nr 55) &&
    decide (expansionRepRole s (expansionChildOf s v) = 1)
  let numbers := (List.range k).filter pick
  let asNatural : Fin k ↪ ℕ := ⟨Fin.val, fun _ _ same => Fin.ext same⟩
  have noDuplicates : numbers.Nodup := List.nodup_range.filter pick
  have setEq : numbers.toFinset = fresh.map asNatural := by
    ext j
    simp only [numbers, pick, List.mem_toFinset, List.mem_filter, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq, Finset.mem_map]
    constructor
    · rintro ⟨within, selected⟩
      exact ⟨⟨j, within⟩, (encoded ⟨j, within⟩).mp selected, rfl⟩
    · rintro ⟨v, member, rfl⟩
      exact ⟨v.isLt, (encoded v).mpr member⟩
  change ((List.range (s.nr 55)).filter pick).length = fresh.card
  conv_lhs => rw (occs := [1]) [dim]
  change numbers.length = fresh.card
  rw [← List.toFinset_card_of_nodup noDuplicates, setEq, Finset.card_map]

open Classical in
theorem collectExpansionOuterCell_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ t steps, BlockRuns collectExpansionOuterCell steps s t ∧ t.halted = false ∧ steps ≤ 11 ∧
      t.nr 99 = s.nr 99 + (if expansionOriginalHasRole s 1 (s.nr 7) then 1 else 0) ∧
      t.nm = (if expansionOriginalHasRole s 1 (s.nr 7) then
        Function.update s.nm (s.nr 88 + s.nr 99) (s.nr 7) else s.nm) ∧
      t.rm = s.rm ∧ ∀ r, r ∉ [0, 6, 10, 19, 99] → t.nr r = s.nr r := by
  classical
  let owner := expansionChildOf s (s.nr 7)
  let role := expansionRepRole s owner
  have fixed {t : ArithmeticState} {steps : ℕ} (runs : BlockRuns collectExpansionOuterCell steps s t)
      (r : ℕ) (outside : r ∉ [0, 6, 10, 19, 99]) : t.nr r = s.nr r := by
    rw [← runs.run]
    exact arithmeticRun_keeps_from_destination_list _ (by decide) outside s steps
  by_cases absent : s.nr 55 ≤ owner
  · let t := (arithmeticStep collectExpansionOuterCell)^[3] s
    have skip : s.nr 55 ≤ s.nm (s.nr 79 + s.nr 7) := absent
    have effect : t.pc = collectExpansionOuterCell.length ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
        t.nr 99 = s.nr 99 := by
      simp [t, collectExpansionOuterCell, arithmeticStep, Function.iterate_succ_apply', entry, running, skip]
    have runs : BlockRuns collectExpansionOuterCell 3 s t := BlockRuns.of_running_exit rfl effect.2.1 effect.1
    have notOuter : ¬expansionOriginalHasRole s 1 (s.nr 7) := by
      intro h; exact (Nat.not_lt.mpr absent) h.1
    exact ⟨t, 3, runs, effect.2.1, by decide, by simp [notOuter, effect.2.2.2.2],
      by simpa only [if_neg notOuter] using effect.2.2.1, effect.2.2.2.1, fixed runs⟩
  · have present : owner < s.nr 55 := Nat.lt_of_not_ge absent
    have visit : ¬s.nr 55 ≤ s.nm (s.nr 79 + s.nr 7) := absent
    rcases lt_trichotomy role 1 with earlier | outer | later
    · let t := (arithmeticStep collectExpansionOuterCell)^[7] s
      have below : s.nm (s.nr 51 + s.nm (s.nr 79 + s.nr 7)) ≤ 1 := earlier.le
      have different : ¬1 ≤ s.nm (s.nr 51 + s.nm (s.nr 79 + s.nr 7)) := Nat.not_le.mpr earlier
      have effect : t.pc = collectExpansionOuterCell.length ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
          t.nr 99 = s.nr 99 := by
        simp [t, collectExpansionOuterCell, arithmeticStep, Function.iterate_succ_apply', entry, running, one,
          visit, below, different]
      have runs : BlockRuns collectExpansionOuterCell 7 s t := BlockRuns.of_running_exit rfl effect.2.1 effect.1
      have notOuter : ¬expansionOriginalHasRole s 1 (s.nr 7) := fun h => earlier.ne h.2
      exact ⟨t, 7, runs, effect.2.1, by decide, by simp [notOuter, effect.2.2.2.2],
        by simpa only [if_neg notOuter] using effect.2.2.1, effect.2.2.2.1, fixed runs⟩
    · let t := (arithmeticStep collectExpansionOuterCell)^[11] s
      have tag : s.nm (s.nr 51 + s.nm (s.nr 79 + s.nr 7)) = 1 := outer
      have effect : t.pc = collectExpansionOuterCell.length ∧ t.halted = false ∧
          t.nm = Function.update s.nm (s.nr 88 + s.nr 99) (s.nr 7) ∧ t.rm = s.rm ∧ t.nr 99 = s.nr 99 + 1 := by
        simp [t, collectExpansionOuterCell, arithmeticStep, Function.iterate_succ_apply', entry, running, one, visit, tag]
      have runs : BlockRuns collectExpansionOuterCell 11 s t := BlockRuns.of_running_exit rfl effect.2.1 effect.1
      have isOuter : expansionOriginalHasRole s 1 (s.nr 7) := ⟨present, outer⟩
      exact ⟨t, 11, runs, effect.2.1, le_rfl, by simpa only [if_pos isOuter] using effect.2.2.2.2,
        by simpa only [if_pos isOuter] using effect.2.2.1, effect.2.2.2.1, fixed runs⟩
    · let t := (arithmeticStep collectExpansionOuterCell)^[6] s
      have above : ¬s.nm (s.nr 51 + s.nm (s.nr 79 + s.nr 7)) ≤ 1 := Nat.not_le.mpr later
      have effect : t.pc = collectExpansionOuterCell.length ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
          t.nr 99 = s.nr 99 := by
        simp [t, collectExpansionOuterCell, arithmeticStep, Function.iterate_succ_apply', entry, running, one, visit, above]
      have runs : BlockRuns collectExpansionOuterCell 6 s t := BlockRuns.of_running_exit rfl effect.2.1 effect.1
      have notOuter : ¬expansionOriginalHasRole s 1 (s.nr 7) := fun h => later.ne' h.2
      exact ⟨t, 6, runs, effect.2.1, by decide, by simp [notOuter, effect.2.2.2.2],
        by simpa only [if_neg notOuter] using effect.2.2.1, effect.2.2.2.1, fixed runs⟩

private theorem freshExpansionOriginals_succ (s : ArithmeticState) (i : ℕ) :
    freshExpansionOriginals s (i + 1) = freshExpansionOriginals s i ++
      if decide (expansionChildOf s i < s.nr 55) && decide (expansionRepRole s (expansionChildOf s i) = 1)
      then [i] else [] := by
  simp only [freshExpansionOriginals, List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]

private theorem freshExpansionOriginals_length_le (s : ArithmeticState) (i : ℕ) :
    (freshExpansionOriginals s i).length ≤ i := by
  simpa [freshExpansionOriginals] using List.length_filter_le
    (fun v => decide (expansionChildOf s v < s.nr 55) && decide (expansionRepRole s (expansionChildOf s v) = 1)) (List.range i)

private structure ExpansionFreshScan (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 7 = i
  fixed : ∀ r, r ∉ [0, 6, 7, 10, 19, 99] → s.nr r = initial.nr r
  count : s.nr 99 = (freshExpansionOriginals initial i).length
  words : ∀ (j : ℕ) (within : j < (freshExpansionOriginals initial i).length),
    s.nm (initial.nr 88 + j) = (freshExpansionOriginals initial i)[j]
  outside : ∀ a, (a < initial.nr 88 ∨ initial.nr 88 + i ≤ a) → s.nm a = initial.nm a
  real : s.rm = initial.rm

/-- Collect exactly the originals which became outer during this expansion.
The compact list bounds the number of subsequent neighbor scans. -/
theorem collectExpansionOuterOriginals_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (forestBelow : s.nr 51 + s.nr 55 ≤ s.nr 88) (mapAbove : s.nr 88 + s.nr 55 ≤ s.nr 79) :
    ∃ t steps, BlockRuns collectExpansionOuterOriginals steps s t ∧ t.halted = false ∧
      steps ≤ 14 * s.nr 55 + 3 ∧ t.nr 99 = (freshExpansionOriginals s (s.nr 55)).length ∧
      (∀ (j : ℕ) (within : j < (freshExpansionOriginals s (s.nr 55)).length),
        t.nm (s.nr 88 + j) = (freshExpansionOriginals s (s.nr 55))[j]) ∧
      (∀ a, (a < s.nr 88 ∨ s.nr 88 + s.nr 55 ≤ a) → t.nm a = s.nm a) ∧ t.rm = s.rm ∧
      ∀ r, r ∉ [0, 6, 7, 10, 19, 99] → t.nr r = s.nr r := by
  classical
  let seeded := {s with pc := 1, nr := Function.update s.nr 99 0}
  have seed : BlockRuns [.natConst 99 0] 1 s seeded := by
    apply BlockRuns.of_running_exit
    · simp [seeded, arithmeticStep, entry, running]
    · exact running
    · rfl
  let source := {seeded with pc := 0}
  let inv := ExpansionFreshScan s
  have start : inv 0 {source with pc := 0, nr := Function.update source.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, by simp [source, seeded, freshExpansionOriginals], ?_, fun _ _ => rfl, rfl⟩
    · intro r safe
      have seven : r ≠ 7 := by simp at safe; omega
      have counter : r ≠ 99 := by simp at safe; omega
      simp [source, seeded, Function.update_of_ne seven, Function.update_of_ne counter]
    · intro j hj
      simp [freshExpansionOriginals] at hj
  have control (i : ℕ) (m : ArithmeticState) (h : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 55 = s.nr 55 :=
    ⟨h.entry, h.running, h.index, h.fixed 55 (by decide)⟩
  have next (i : ℕ) (within : i < s.nr 55) (m : ArithmeticState) (h : inv i m) :
      ∃ t steps, steps ≤ 11 ∧ BlockRuns collectExpansionOuterCell steps m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    obtain ⟨t, steps, runs, live, cost, newCount, nat, real, fixed⟩ :=
      collectExpansionOuterCell_spec h.entry h.running ((h.fixed 9 (by decide)).trans one)
    have sameChild : expansionChildOf m (m.nr 7) = expansionChildOf s i := by
      unfold expansionChildOf
      rw [h.fixed 79 (by decide), h.index, h.outside _ (.inr (by omega))]
    have sameFlag : expansionOriginalHasRole m 1 (m.nr 7) ↔ expansionOriginalHasRole s 1 i := by
      unfold expansionOriginalHasRole expansionRepRole
      rw [sameChild, h.fixed 55 (by decide), h.fixed 51 (by decide)]
      exact and_congr_right (fun inRange => by rw [h.outside _ (.inl (by omega))])
    have accepts : (decide (expansionChildOf s i < s.nr 55) &&
        decide (expansionRepRole s (expansionChildOf s i) = 1)) = true ↔ expansionOriginalHasRole s 1 i := by
      simp [expansionOriginalHasRole]
    have lengthLe := freshExpansionOriginals_length_le s i
    have writeAddr : m.nr 88 + m.nr 99 = s.nr 88 + (freshExpansionOriginals s i).length := by
      rw [h.fixed 88 (by decide), h.count]
    refine ⟨t, steps, cost, runs, live, rfl, live, ?_, ?_, ?_, ?_, ?_, real.trans h.real⟩
    · simp [fixed 7 (by decide), fixed 9 (by decide), h.index, h.fixed 9 (by decide), one]
    · intro r safe
      change Function.update t.nr 7 (t.nr 7 + t.nr 9) r = s.nr r
      rw [Function.update_of_ne (by simp at safe; omega : r ≠ 7)]
      exact (fixed r (by simp at safe ⊢; omega)).trans (h.fixed r safe)
    · change t.nr 99 = _
      rw [newCount, h.count, freshExpansionOriginals_succ]
      by_cases selected : expansionOriginalHasRole s 1 i
      · rw [if_pos (sameFlag.mpr selected), if_pos (accepts.mpr selected)]
        simp
      · have no : ¬expansionOriginalHasRole m 1 (m.nr 7) := fun yes => selected (sameFlag.mp yes)
        rw [if_neg no, if_neg (fun yes => selected (accepts.mp yes))]
        simp
    · intro j hj
      change t.nm (s.nr 88 + j) = _
      by_cases selected : expansionOriginalHasRole s 1 i
      · have yes := sameFlag.mpr selected
        have extend : freshExpansionOriginals s (i + 1) = freshExpansionOriginals s i ++ [i] := by
          rw [freshExpansionOriginals_succ, if_pos (accepts.mpr selected)]
        rw [nat, if_pos yes, writeAddr, h.index]
        by_cases earlier : j < (freshExpansionOriginals s i).length
        · rw [Function.update_of_ne (by omega), h.words j earlier]
          exact ((getElem_congr_coll extend).trans (List.getElem_append_left earlier)).symm
        · have last : j = (freshExpansionOriginals s i).length := by
            rw [extend, List.length_append, List.length_singleton] at hj
            omega
          have atNext : j < (freshExpansionOriginals s i ++ [i]).length := extend ▸ hj
          have appended : (freshExpansionOriginals s (i + 1))[j] = (freshExpansionOriginals s i ++ [i])[j] :=
            getElem_congr_coll extend
          have lastWord : ([i] : List ℕ)[j - (freshExpansionOriginals s i).length]'(by simp; omega) = i := by
            have position : j - (freshExpansionOriginals s i).length = 0 := by omega
            exact (getElem_congr_idx position).trans (by rfl)
          have actual := (appended.trans (List.getElem_append_right (by omega))).trans lastWord
          calc
            Function.update m.nm (s.nr 88 + (freshExpansionOriginals s i).length) i (s.nr 88 + j) = i := by simp [last]
            _ = (freshExpansionOriginals s (i + 1))[j] := actual.symm
      · have no : ¬expansionOriginalHasRole m 1 (m.nr 7) := fun yes => selected (sameFlag.mp yes)
        have unchanged : freshExpansionOriginals s (i + 1) = freshExpansionOriginals s i := by
          rw [freshExpansionOriginals_succ, if_neg (fun yes => selected (accepts.mp yes)), List.append_nil]
        rw [nat, if_neg no, h.words j (unchanged ▸ hj)]
        exact (getElem_congr_coll unchanged).symm
    · intro address away
      change t.nm address = _
      rw [nat]
      split
      · rw [Function.update_of_ne (by rw [writeAddr]; omega)]
        exact h.outside address (by omega)
      · exact h.outside address (by omega)
  have sourceEntry : source.pc = 0 := rfl
  obtain ⟨_, steps, done, small, loop⟩ := countedLoopFromZero_bounded 9 7 55 (s.nr 55) 11
    collectExpansionOuterCell inv (s := source) sourceEntry running start control next
  exact ⟨_, _, seed.append loop, done.running, by omega, done.count, done.words, done.outside, done.real, done.fixed⟩

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionFreshRAM

/-! matching/ExpansionCacheRAM.lean -/
section RppSource_ExpansionCacheRAM
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096







theorem expansionHandlerCost_le_charge {k fresh : ℕ} (positive : 0 < k) :
    238 * k + 110 + (63 * k + (98 * k + 9) * fresh + 14) ≤ 425 * k * (1 + fresh) := by
  have rise : 98 * k + 9 ≤ 425 * k := by omega
  have charged := Nat.mul_le_mul_right fresh rise
  rw [Nat.mul_add, Nat.mul_one]
  omega

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionCacheRAM

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

/-! matching/MatchingCacheFootprint.lean -/
section RppSource_MatchingCacheFootprint
namespace VehicleRoutingSurvey.Routing



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

/-! matching/ExpansionCutFootprint.lean -/
section RppSource_ExpansionCutFootprint
namespace VehicleRoutingSurvey.Routing

theorem expansionCutCell_footprint {k : ℕ} {s t : ArithmeticState}
    (layout : MatchingCacheLayout k s) (within : s.nr 7 < k)
    (nat : t.nm = expansionCutNat s) (real : t.rm = expansionCutReal s) : MatchingCacheFootprint k s t := by
  have slot : s.nr 55 + s.nr 55 + s.nr 7 < s.nr 61 := by rw [layout.dimension, layout.rows]; omega
  have ids := layout.idsBefore
  have records := layout.recordsBefore
  have slack := layout.slacksBefore
  have rates := layout.ratesBefore
  constructor
  · intro a outside
    rw [nat, expansionCutNat]
    split
    · rfl
    · split
      · exact Function.update_of_ne (by omega) _ _
      · unfold installedMatchingInnerCutNat
        split
        · change Function.update s.nm (s.nr 58 + (s.nr 55 + s.nr 55 + s.nr 7)) 0 a = s.nm a
          exact Function.update_of_ne (by omega) _ _
        · simp (disch := omega) [installedMatchingCandidateNat, growthInnerCutData, readyGrowthInnerNode,
            innerCutCandidateSlot, expansionCutReadyFull, Function.update_of_ne]
  · intro a outside
    rw [real, expansionCutReal]
    split
    · rfl
    · unfold installedMatchingInnerCutReal
      split
      · rfl
      · simp (disch := omega) [installedMatchingCandidateReal, growthInnerCutData, readyGrowthInnerNode,
          innerCutCandidateSlot, expansionCutReadyFull, Function.update_of_ne]

private structure ExpansionCutFootprintScan (k : ℕ) (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 7 = i
  fixed : ∀ r, r ∉ [0, 6, 7, 10, 15, 16, 18, 19, 28] → s.nr r = initial.nr r
  footprint : MatchingCacheFootprint k initial s

theorem restoreExpansionCuts_footprint {k : ℕ} {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (layout : MatchingCacheLayout k s) :
    ∃ t steps, BlockRuns restoreExpansionCuts steps s t ∧ t.halted = false ∧ steps ≤ 35 * k + 2 ∧
      MatchingCacheFootprint k s t ∧ ∀ r, r ∉ [0, 6, 7, 10, 15, 16, 18, 19, 28] → t.nr r = s.nr r := by
  let inv := ExpansionCutFootprintScan k s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, MatchingCacheFootprint.unchanged rfl rfl⟩
    intro r away
    exact Function.update_of_ne (by simp at away; omega) _ _
  have control (i : ℕ) (m : ArithmeticState) (h : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 55 = k :=
    ⟨h.entry, h.running, h.index, (h.fixed 55 (by decide)).trans layout.dimension⟩
  have next (i : ℕ) (inside : i < k) (m : ArithmeticState) (h : inv i m) :
      ∃ t steps, steps ≤ 32 ∧ BlockRuns restoreExpansionCutCell steps m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    obtain ⟨t, steps, runs, live, budget, nat, real, fixed⟩ := restoreExpansionCutCell_spec h.entry h.running
      ((h.fixed 9 (by decide)).trans one) ((h.fixed 14 (by decide)).trans zero)
    have stageLayout := layout.keeps (fun r high => h.fixed r (by simp; omega))
    have changed := expansionCutCell_footprint stageLayout (h.index.symm ▸ inside) nat real
    have total := h.footprint.chain changed (fun r hr => h.fixed r (by simp at hr ⊢; omega))
    refine ⟨t, steps, budget, runs, live, rfl, live, ?_, ?_, total.natural, total.real⟩
    · simp [fixed 7 (by decide), fixed 9 (by decide), h.index, h.fixed 9 (by decide), one]
    · intro r away
      change Function.update t.nr 7 (t.nr 7 + t.nr 9) r = s.nr r
      rw [Function.update_of_ne (by simp at away; omega : r ≠ 7)]
      exact (fixed r (by simp at away ⊢; omega)).trans (h.fixed r away)
  obtain ⟨_, steps, result, budget, runs⟩ := countedLoopFromZero_bounded 9 7 55 k 32
    restoreExpansionCutCell inv entry running initial control next
  exact ⟨_, steps, runs, result.running, by omega, ⟨result.footprint.natural, result.footprint.real⟩, result.fixed⟩

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionCutFootprint

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

/-! matching/ExpansionNeighborFootprint.lean -/
section RppSource_ExpansionNeighborFootprint
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

structure ExpansionOuterListFrame (k : ℕ) (s : ArithmeticState) : Prop where
  above : s.nr 65 + 2 * (k * k) ≤ s.nr 88
  originals : ∀ i < s.nr 99, s.nm (s.nr 88 + i) < k

theorem ExpansionOuterListFrame.keeps {k : ℕ} {s t : ArithmeticState} (list : ExpansionOuterListFrame k s)
    (footprint : MatchingCacheFootprint k s t) (table : t.nr 88 = s.nr 88)
    (pairs : t.nr 65 = s.nr 65) (count : t.nr 99 = s.nr 99) : ExpansionOuterListFrame k t := by
  constructor
  · rw [table, pairs]
    exact list.above
  · intro i within
    have hi : i < s.nr 99 := count ▸ within
    rw [table, footprint.natural _ (.inr (list.above.trans (Nat.le_add_right _ _)))]
    exact list.originals i hi

theorem refreshExpansionOuterCell_footprint {k : ℕ} {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (layout : MatchingCacheLayout k s) (offsets : MatchingCacheOffsets k s) (reps : MatchingCacheRepresentatives k s)
    (source : s.nm (s.nr 88 + s.nr 24) < k) :
    ∃ t steps, BlockRuns refreshExpansionOuterCell steps s t ∧ t.halted = false ∧
      steps ≤ 98 * k + 6 ∧ MatchingCacheFootprint k s t ∧
      ∀ r, r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 25, 26] → t.nr r = s.nr r := by
  let addr := s.nr 88 + s.nr 24
  let original := s.nm addr
  let repAddr := s.nr 57 + original
  let loaded := Function.update (Function.update (Function.update s.nr 6 addr) 15 original) 6 repAddr
  let a := { s with pc := 0, nr := Function.update loaded 26 (s.nm repAddr) }
  have loads : BlockRuns readExpansionOuterOriginal 4 s {a with pc := 4} := by
    apply BlockRuns.of_running_exit
    · simp [a, loaded, addr, original, repAddr, readExpansionOuterOriginal, arithmeticStep, entry, running,
        Function.iterate_succ_apply']
    · exact running
    · rfl
  have fixed (r : ℕ) (safe : r ∉ [6, 15, 26] := by decide) : a.nr r = s.nr r := by
    have no6 : r ≠ 6 := by simp at safe; omega
    have no15 : r ≠ 15 := by simp at safe; omega
    have no26 : r ≠ 26 := by simp at safe; omega
    simp [a, loaded, Function.update_of_ne no6, Function.update_of_ne no15, Function.update_of_ne no26]
  have noWrite : MatchingCacheFootprint k s a := MatchingCacheFootprint.unchanged rfl rfl
  have aLayout := layout.keeps (fun r high => fixed r (by simp; omega))
  have aOffsets := offsets.keeps noWrite (fixed 21) (fixed 58)
  have aReps := reps.keeps noWrite (fixed 57) (fixed 58)
  have sourceRep : a.nr 26 < k := by simpa [a, repAddr, original, addr] using reps.rep _ source
  obtain ⟨t, steps, scans, live, cost, footprint⟩ := refreshSelectedOuterVertex_footprint (s := a) rfl running
    ((fixed 9).trans one) ((fixed 14).trans zero) aLayout aOffsets aReps sourceRep
  have runs : BlockRuns refreshExpansionOuterCell (4 + steps) s _ := loads.append scans
  have frame := noWrite.chain footprint (fun r listed => fixed r (by simp at listed ⊢; omega))
  refine ⟨_, _, runs, live, by omega, ⟨frame.natural, frame.real⟩, ?_⟩
  intro r away
  rw [← runs.run]
  exact arithmeticRun_keeps_from_destination_list _ (by decide) away s _

private structure ExpansionNeighborFootprintScan (k : ℕ) (initial : ArithmeticState) (i : ℕ)
    (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  cursor : s.nr 24 = i
  fixed : ∀ r, r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 26] → s.nr r = initial.nr r
  footprint : MatchingCacheFootprint k initial s

theorem refreshExpansionOuterOriginals_footprint {k : ℕ} {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (layout : MatchingCacheLayout k s) (offsets : MatchingCacheOffsets k s) (reps : MatchingCacheRepresentatives k s)
    (list : ExpansionOuterListFrame k s) :
    ∃ t steps, BlockRuns refreshExpansionOuterOriginals steps s t ∧ t.halted = false ∧
      steps ≤ (98 * k + 9) * s.nr 99 + 2 ∧ MatchingCacheFootprint k s t := by
  let inv := ExpansionNeighborFootprintScan k s
  have start : inv 0 {s with pc := 0, nr := Function.update s.nr 24 0} := by
    refine ⟨rfl, running, by simp, ?_, MatchingCacheFootprint.unchanged rfl rfl⟩
    intro r safe
    exact Function.update_of_ne (by simp at safe; omega) _ _
  have control (i : ℕ) (m : ArithmeticState) (h : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 24 = i ∧ m.nr 99 = s.nr 99 :=
    ⟨h.entry, h.running, h.cursor, h.fixed 99 (by decide)⟩
  have next (i : ℕ) (within : i < s.nr 99) (m : ArithmeticState) (h : inv i m) :
      ∃ t steps, steps ≤ 98 * k + 6 ∧ BlockRuns refreshExpansionOuterCell steps m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)} := by
    have keep (r : ℕ) (safe : r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 26] := by decide) :
        m.nr r = s.nr r := h.fixed r safe
    have listNow := list.keeps h.footprint (keep 88) (keep 65) (keep 99)
    have source : m.nm (m.nr 88 + m.nr 24) < k := listNow.originals _ (by rwa [h.cursor, keep 99])
    obtain ⟨t, steps, runs, live, cost, effect, fixed⟩ := refreshExpansionOuterCell_footprint h.entry h.running
      ((keep 9).trans one) ((keep 14).trans zero) (layout.keeps (fun r hr => keep r (by simp; omega)))
      (offsets.keeps h.footprint (keep 21) (keep 58)) (reps.keeps h.footprint (keep 57) (keep 58)) source
    have total := h.footprint.chain effect (fun r hr => keep r (by simp at hr ⊢; omega))
    refine ⟨t, steps, cost, runs, live, rfl, live, ?_, ?_, total.natural, total.real⟩
    · simp [fixed 24 (by decide), fixed 9 (by decide), h.cursor, keep 9, one]
    · intro r safe
      change Function.update t.nr 24 (t.nr 24 + t.nr 9) r = s.nr r
      rw [Function.update_of_ne (by simp at safe; omega : r ≠ 24)]
      exact (fixed r (by simp at safe ⊢; omega)).trans (keep r safe)
  obtain ⟨_, steps, result, budget, runs⟩ := countedLoopFromZero_bounded 9 24 99 (s.nr 99) (98 * k + 6)
    refreshExpansionOuterCell inv entry running start control next
  have ticks : 1 + (s.nr 99 * (98 * k + 6 + 3) + 1) = (98 * k + 9) * s.nr 99 + 2 := by
    rw [show 98 * k + 6 + 3 = 98 * k + 9 by omega, Nat.mul_comm (98 * k + 9)]
    omega
  exact ⟨_, steps, runs, result.running, budget.trans_eq ticks, result.footprint.natural, result.footprint.real⟩

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionNeighborFootprint

/-! matching/ExpansionCacheFootprint.lean -/
section RppSource_ExpansionCacheFootprint
namespace VehicleRoutingSurvey.Routing

theorem expansionIncoming_footprint {k : ℕ} {s t : ArithmeticState}
    (layout : MatchingCacheLayout k s)
    (nat : ∀ a, t.nm a = expansionIncomingNat s (s.nr 55) a)
    (real : ∀ a, t.rm a = expansionIncomingReal s (s.nr 55) a) : MatchingCacheFootprint k s t := by
  have ids := layout.idsBefore
  have dict := layout.recordsBefore
  have slack := layout.slacksBefore
  have rate := layout.ratesBefore
  have size := layout.rows
  have dimension := layout.dimension
  constructor
  · intro a outside
    rw [nat, expansionIncomingNat, if_neg]
    rintro ⟨i, hi, atSlot, _⟩
    omega
  · intro a outside
    rw [real, expansionIncomingReal, if_neg]
    rintro ⟨i, hi, atSlot, _⟩
    omega

structure ExpansionRepairFootprint (k : ℕ) (s t : ArithmeticState) : Prop where
  natural : ∀ a, (a < s.nr 58 ∨ s.nr 65 + 2 * (k * k) ≤ a) →
    (a < s.nr 88 ∨ s.nr 88 + k ≤ a) → t.nm a = s.nm a
  real : ∀ a, (a < s.nr 59 ∨ s.nr 66 + k * k ≤ a) → t.rm a = s.rm a

/-- The cache repair touches only candidate rows, pair buckets, and the
temporary packed list. Its registry and original-witness tables stay intact. -/
theorem restoreExpansionCacheBlock_footprint {k : ℕ} {s t : ArithmeticState} {steps : ℕ}
    (runs : BlockRuns restoreExpansionCacheBlock steps s t) (entry : s.pc = 0) (running : s.halted = false)
    (work : ExpansionCacheFrame s) (layout : MatchingCacheLayout k s) (offsets : MatchingCacheOffsets k s)
    (reps : MatchingCacheRepresentatives k s) (listAbove : s.nr 65 + 2 * (k * k) ≤ s.nr 88) :
    ExpansionRepairFootprint k s t := by
  have size := layout.dimension
  obtain ⟨collected, collectedSteps, collects, collectLive, _, count, entries, colNat, colReal, colFixed⟩ :=
    collectExpansionOuterOriginals_spec entry running work.one
      (work.rolesBelowIncoming.trans work.cacheBelowWorkList) work.workListBelowMembers
  let a := {collected with pc := 0}
  have afix (r : ℕ) (safe : r ∉ [0, 6, 7, 10, 19, 99] := by decide) : a.nr r = s.nr r := colFixed r safe
  have aLayout : MatchingCacheLayout k a := by
    refine ⟨(afix 55).trans layout.dimension, (afix 61).trans layout.rows, ?_, ?_, ?_, ?_⟩
    · rw [afix 58, afix 61, afix 54]; exact layout.idsBefore
    · rw [afix 54, afix 61, afix 65]; exact layout.recordsBefore
    · rw [afix 59, afix 61, afix 60]; exact layout.slacksBefore
    · rw [afix 60, afix 61, afix 66]; exact layout.ratesBefore
  have aOne : a.nr 9 = 1 := (afix 9).trans work.one
  have aZero : a.nr 14 = 0 := (afix 14).trans work.zero
  have combNat (address : ℕ) (below : address < s.nr 58) : a.nm address = s.nm address :=
    colNat address (.inl (below.trans_le work.cacheBelowWorkList))
  have aOffsets : MatchingCacheOffsets k a := by
    constructor
    · intro v hi
      rw [afix 21, afix 58]
      exact offsets.addresses v hi
    · intro v hi
      rw [afix 21, combNat _ (offsets.addresses v hi)]
      exact offsets.offsets v hi
  have aReps : MatchingCacheRepresentatives k a := by
    constructor
    · intro v hi
      rw [afix 57, afix 58]
      exact reps.address v hi
    · intro v hi
      rw [afix 57, combNat _ (reps.address v hi)]
      exact reps.rep v hi
  have aList : ExpansionOuterListFrame k a := by
    constructor
    · rw [afix 65, afix 88]
      exact listAbove
    · intro i hi
      have inList : i < (freshExpansionOriginals s (s.nr 55)).length := count ▸ hi
      have chosen := List.getElem_mem inList
      have selected : (freshExpansionOriginals s (s.nr 55))[i] < s.nr 55 := by
        exact List.mem_range.mp (List.mem_filter.mp chosen).1
      rw [afix 88, entries i inList, ← size]
      exact selected
  obtain ⟨rerated, rateSteps, rates, rateLive, _, rateNat, rateReal, aFixed⟩ :=
    restoreExpansionIncomingRates_spec (s := a) rfl collectLive aOne aZero
      (by rw [afix 51, afix 55, afix 58]; exact work.rolesBelowIncoming)
      (by rw [afix 58, afix 55, afix 79]; exact work.incomingBelowMembers)
  let b := {rerated with pc := 0}
  have bf (r : ℕ) (safe : r ∉ [0, 6, 7, 10, 11, 19] := by decide) : b.nr r = a.nr r := aFixed r safe
  have rateFrame : MatchingCacheFootprint k a b := expansionIncoming_footprint aLayout rateNat rateReal
  have bLayout := aLayout.keeps (fun r high => bf r (by simp; omega))
  have bOffsets := aOffsets.keeps rateFrame (bf 21) (bf 58)
  have bReps := aReps.keeps rateFrame (bf 57) (bf 58)
  have bList := aList.keeps rateFrame (bf 88) (bf 65) (bf 99)
  have bOne : b.nr 9 = 1 := (bf 9).trans aOne
  have bZero : b.nr 14 = 0 := (bf 14).trans aZero
  obtain ⟨tagged, cutSteps, cuts, cutLive, _, cutFrame, bFixed⟩ :=
    restoreExpansionCuts_footprint (s := b) rfl rateLive bOne bZero bLayout
  let c := {tagged with pc := 0}
  have cf (r : ℕ) (safe : r ∉ [0, 6, 7, 10, 15, 16, 18, 19, 28] := by decide) : c.nr r = b.nr r := bFixed r safe
  have cFrame : MatchingCacheFootprint k b c := ⟨cutFrame.natural, cutFrame.real⟩
  have cLayout := bLayout.keeps (fun r high => cf r (by simp; omega))
  have cOffsets := bOffsets.keeps cFrame (cf 21) (cf 58)
  have cReps := bReps.keeps cFrame (cf 57) (cf 58)
  have cList := bList.keeps cFrame (cf 88) (cf 65) (cf 99)
  have cZero : c.nr 14 = 0 := (cf 14).trans bZero
  obtain ⟨refreshed, refreshSteps, refreshes, refreshLive, _, dFrame⟩ :=
    refreshExpansionOuterOriginals_footprint (s := c) rfl cutLive ((cf 9).trans bOne) cZero cLayout cOffsets cReps cList
  let d := {refreshed with pc := 0}
  have dZero : d.nr 14 = 0 := by
    change refreshed.nr 14 = 0
    rw [← refreshes.run, arithmeticRun_keeps_from_destination_list
      [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 26] (by decide) (by decide) c refreshSteps]
    exact cZero
  obtain ⟨u, resets, _, lastNat, lastReal, _⟩ := resetMatchingSelector_spec d rfl refreshLive dZero
  have first := rateFrame.chain cFrame (fun r safe => bf r (by simp at safe ⊢; omega))
  have last := first.chain dFrame
    (fun r safe => (cf r (by simp at safe ⊢; omega)).trans (bf r (by simp at safe ⊢; omega)))
  have replay : BlockRuns restoreExpansionCacheBlock
      (collectedSteps + (rateSteps + (cutSteps + (refreshSteps + 5)))) s _ :=
    collects.append (rates.append (cuts.append (refreshes.append resets)))
  rw [(runs.same_exit replay).2]
  constructor
  · intro aIndex safe workArea
    change u.nm aIndex = _
    have source : a.nm aIndex = s.nm aIndex := colNat aIndex (by simpa only [size] using workArea)
    have outside : aIndex < a.nr 58 ∨ a.nr 65 + 2 * (k * k) ≤ aIndex := by rwa [afix 58, afix 65]
    exact (congrFun lastNat aIndex).trans ((last.natural aIndex outside).trans source)
  · intro address safe
    change u.rm address = _
    have outside : address < a.nr 59 ∨ a.nr 66 + k * k ≤ address := by rwa [afix 59, afix 66]
    exact (congrFun lastReal address).trans ((last.real address outside).trans (congrFun colReal address))

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionCacheFootprint

/-! matching/MatchingExpandRegisterFrame.lean -/
section RppSource_MatchingExpandRegisterFrame
namespace VehicleRoutingSurvey.Routing

def matchingExpansionWrittenRegisters : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27, 28,
    43, 44, 45, 46, 47, 49, 81, 82, 87, 94, 95, 96, 97, 98, 99]

set_option maxRecDepth 4096 in
theorem matchingExpandHandler_keeps_register {s t : ArithmeticState} {steps r : ℕ}
    (runs : BlockRuns matchingExpandHandlerBlock steps s t) (outside : r ∉ matchingExpansionWrittenRegisters) :
    t.nr r = s.nr r := by
  rw [← runs.run]
  exact arithmeticRun_keeps_from_destination_list matchingExpansionWrittenRegisters (by decide) outside s steps



end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpandRegisterFrame

/-! matching/ExpansionPersistentState.lean -/
section RppSource_ExpansionPersistentState
namespace VehicleRoutingSurvey.Routing

structure ExpansionPersistentLayout (k : ℕ) (s : ArithmeticState) : Prop where
  forestBelowCache : s.nr 51 + 3 * k ≤ s.nr 58
  representativesBelowCache : s.nr 57 + k ≤ s.nr 58
  cacheBelowNodes : s.nr 65 + 2 * (k * k) ≤ s.nr 74
  nodesBelowWork : s.nr 74 + k ≤ s.nr 88
  cacheBelowWitnesses : s.nr 65 + 2 * (k * k) ≤ s.nr 90
  witnessesBelowWork : s.nr 90 + 2 * k ≤ s.nr 88
  potentialsBelowCache : s.nr 62 + k ≤ s.nr 59
  cacheBelowDuals : s.nr 66 + k * k ≤ s.nr 75

/-- The forest and its original parent witnesses remain usable after the cache
is rebuilt. The published representatives, child nodes and duals remain in place. -/
structure ExpansionPersistentState {k : ℕ} (s t : ArithmeticState)
    (forest : AlternatingForestState (Fin k)) (mate : Fin k → Option (Fin k))
    (tightRep tightOriginal : Sym2 (Fin k) → Prop) (rep : Fin k → Fin k) : Prop where
  encoding : AlternatingForestMemory forest (t.nr 51) t.nm
  valid : forest.valid mate (fun a b => tightRep s(a, b))
  witnesses : ∀ child parent : Fin k, (forest.role child).parent = some parent →
    ∃ edge : Fin k × Fin k,
      matchingForestWitnessAt t.nm (t.nr 90) child.val = (edge.1.val, edge.2.val) ∧
      (rep edge.1, rep edge.2) = (parent, child) ∧ tightOriginal s(edge.1, edge.2)
  representatives : ∀ v < k, t.nm (t.nr 57 + v) = s.nm (s.nr 57 + v)
  nodes : ∀ v < k, t.nm (t.nr 74 + v) = s.nm (s.nr 74 + v)
  potentials : ∀ v < k, t.rm (t.nr 62 + v) = s.rm (s.nr 62 + v)
  cutDuals : ∀ node, t.rm (t.nr 75 + node) = s.rm (s.nr 75 + node)

theorem restoreExpansionCacheBlock_keeps_persistentState {k : ℕ} {published s t : ArithmeticState}
    {forest : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)}
    {tightRep tightOriginal : Sym2 (Fin k) → Prop} {rep : Fin k → Fin k}
    (opened : MatchingExpandedForest forest mate tightRep tightOriginal rep published s)
    (restored : ExpansionCacheRestored s t) (footprint : ExpansionRepairFootprint k s t)
    (layout : ExpansionPersistentLayout k s) : ExpansionPersistentState s t forest mate tightRep tightOriginal rep := by
  have forestAt : s.nr 51 = published.nr 51 := opened.fixed 51 (by decide)
  have witnessAt : s.nr 90 = published.nr 90 := opened.fixed 90 (by decide)
  have fixed (r : ℕ) (high : 50 ≤ r := by decide) (away : r ≠ 99 := by decide) : t.nr r = s.nr r :=
    restored.fixed r high away
  refine ⟨?_, opened.valid, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fixed 51]
    intro v
    have smaller := v.isLt
    have lower := layout.forestBelowCache
    have encoded := opened.encoding v
    rw [← forestAt] at encoded
    exact ⟨(restored.natural _ (by omega)).trans encoded.1,
      (restored.natural _ (by omega)).trans encoded.2.1, (restored.natural _ (by omega)).trans encoded.2.2⟩
  · intro child parent linked
    obtain ⟨edge, words, direction, tight⟩ := opened.edgeWitness child parent linked
    rw [← witnessAt] at words
    have bound := child.isLt
    have above := layout.cacheBelowWitnesses
    have below := layout.witnessesBelowWork
    let addr := forestWitnessAddress (s.nr 90) child.val
    have address : addr = s.nr 90 + (child.val + child.val) := rfl
    have first : t.nm addr = s.nm addr := footprint.natural addr (.inr (by omega)) (.inl (by omega))
    have second : t.nm (addr + 1) = s.nm (addr + 1) := footprint.natural _ (.inr (by omega)) (.inl (by omega))
    refine ⟨edge, ?_, direction, tight⟩
    rw [fixed 90, matchingForestWitnessAt]
    change (t.nm addr, t.nm (addr + 1)) = _
    rw [first, second]
    exact words
  · intro v within
    rw [fixed 57]
    exact restored.natural _ (by have := layout.representativesBelowCache; omega)
  · intro v within
    rw [fixed 74]
    have above := layout.cacheBelowNodes
    have below := layout.nodesBelowWork
    exact footprint.natural _ (.inr (by omega)) (.inl (by omega))
  · intro v within
    rw [fixed 62]
    exact restored.real _ (by have := layout.potentialsBelowCache; omega)
  · intro node
    rw [fixed 75]
    exact footprint.real _ (.inr (by have := layout.cacheBelowDuals; omega))



end VehicleRoutingSurvey.Routing
end RppSource_ExpansionPersistentState

/-! matching/MatchingExpansionSearchExit.lean -/
section RppSource_MatchingExpansionSearchExit
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The final encoded links recover the exact tightness relation of the new
partition, including the new child hit by the original incoming edge. -/
theorem ExpansionPersistentState.toSearch {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s t : ArithmeticState}
    {tightRep : Sym2 (Fin k) → Prop} (top : CompactTopMatching part)
    (final : ExpansionPersistentState s t forest state.partialMate tightRep
      (fun e => oddCutDualEdgeValue state.cuts state.potential state.cutDual e = edgeCost cost e) part.representative)
    (unmatched : ∀ v ∉ state.covered, forest.role (part.representative v) = .outer none) :
    MatchingForestOriginalWitnesses part forest t ∧ CompactMatchingSearchForest part forest state.partialMate part.tightBetween := by
  have witnesses : MatchingForestOriginalWitnesses part forest t := by
    intro child parent link
    obtain ⟨edge, words, ends, tight⟩ := final.witnesses child parent link
    exact ⟨edge.1, edge.2, words, congrArg Prod.fst ends, congrArg Prod.snd ends, tight⟩
  refine ⟨witnesses, ⟨?_, ?_, unmatched⟩⟩
  · apply AlternatingForestState.valid_of_parent_tight final.valid
    intro child parent link
    obtain ⟨a, b, _, first, second, tight⟩ := witnesses link
    exact ⟨a, b, first, second, tight⟩
  · intro u v edge separate
    obtain ⟨first, second⟩ := top.crossing_endpoints edge separate
    rw [first, second]
    exact ⟨state.partialMate_some_iff.mpr edge, state.partialMate_some_iff.mpr (Sym2.eq_swap ▸ edge)⟩

/-- A selected inner blossom contains no unmatched original. All exposed
roots are therefore untouched when its direct children become active. -/
theorem MatchingExpansionChildPorts.exposedRoots {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {B : Finset (Fin k)} (registry : MatchingExpansionChildPorts state B)
    (top : B ∈ Finset.univ.image part.blocks.block) (present : B ∈ state.cuts) (zero : state.cutDual B = 0)
    (internal : state.InternalCuts)
    (external : ∀ p ∈ registry.ports, ∀ w, state.partialMate p = some w → w ∉ registry.block p)
    {forest : AlternatingForestState (Fin k)} {tight : Fin k → Fin k → Prop}
    (before : CompactMatchingSearchForest part forest state.partialMate tight)
    (source base : Fin k) (children : List (Fin k)) (entry : ℕ)
    (baseBlock : part.blocks.block base = B) (baseFixed : part.representative base = base)
    (inner : forest.role base = .inner source) (ports : registry.ports = (base :: children).toFinset) :
    let opened := part.openZeroCut top present zero (registry.toExpansionChildren internal external)
    let expanded := forest.expandBlossom source base children entry
    ∀ v ∉ (state.eraseZeroCut present zero).covered, expanded.role (opened.representative v) = .outer none := by
  intro opened expanded v hv
  have lonely := before.exposed v hv
  have outside : v ∉ B := by
    intro inside
    have same := part.same_block.mpr (((part.block_eq_iff_member top v).mpr inside).trans baseBlock.symm)
    rw [same, baseFixed, inner] at lonely
    contradiction
  exact (registry.keepsOutsideRoles top present zero internal external forest source base children entry ports v outside).2.trans lonely

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionSearchExit

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



end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionMapRefinement

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



/-- Recover the exact RAM cut port from the typed event picked by the selector. -/
theorem matchingSelectedExpansion_ofView {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {s : ArithmeticState} {B : Finset (Fin k)}
    (view : MatchingEventClassView part.blocks forest (part.representativeOf positive) (matchingTopCutAt part) s (.cut B)) :
    Nonempty (MatchingSelectedExpansion part forest positive s B) := by
  obtain ⟨base, ports, assigned, tag, top, nontrivial, parent, inner⟩ := view
  obtain ⟨w, _, same⟩ := Finset.mem_image.mp top
  have populated : B.Nonempty := ⟨w, same ▸ part.blocks.self_mem w (Finset.mem_univ w)⟩
  obtain ⟨active, block, rep⟩ := matchingTopCutAt_port part positive populated assigned.symm
  exact ⟨⟨base, parent, ports, tag, block, active, rep, top, nontrivial, rep ▸ inner⟩⟩



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

/-! matching/MatchingExpansionRoot.lean -/
section RppSource_MatchingExpansionRoot
namespace VehicleRoutingSurvey.Routing

theorem MatchingMemberTree.eq_nil_of_rootKeys {tree : MatchingMemberTree}
    (empty : tree.rootKeys = []) : tree = .nil := by
  cases tree <;> simp_all [MatchingMemberTree.rootKeys]









end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionRoot

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

/-! matching/MatchingFreshCutOuter.lean -/
section RppSource_MatchingFreshCutOuter
namespace VehicleRoutingSurvey.Routing





/-- Growth, dual steps, and expansion preserve fresh-cut ownership whenever
old outer originals remain outer and surviving registry identifiers agree. -/
theorem MatchingFreshCutOuter.restrict {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state next : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {opened : CompactMatchingPartition next} {forest after : AlternatingForestState (Fin k)}
    {oldNode node : Finset (Fin k) → ℕ} {cutoff : ℕ}
    (before : MatchingFreshCutOuter part forest oldNode cutoff)
    (subset : next.cuts ⊆ state.cuts) (same : ∀ B ∈ next.cuts, node B = oldNode B)
    (outer : ∀ v, (forest.role (part.representative v)).outerTag = true →
      (after.role (opened.representative v)).outerTag = true) :
    MatchingFreshCutOuter opened after node cutoff :=
  fun B present fresh v member => outer v (before B (subset present) (same B present ▸ fresh) v member)



/-- In particular, the cut selected for expansion predates the current stage. -/
theorem MatchingSelectedExpansion.inherited {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {s : ArithmeticState} {B : Finset (Fin k)}
    (selected : MatchingSelectedExpansion part forest positive s B) {node : Finset (Fin k) → ℕ} {cutoff : ℕ}
    (old : MatchingFreshCutOuter part forest node cutoff) (present : B ∈ state.cuts) :
    B ∈ state.cuts.filter (fun C => node C < cutoff) := by
  refine Finset.mem_filter.mpr ⟨present, ?_⟩
  apply Nat.lt_of_not_ge
  intro fresh
  have member : selected.base ∈ B := by
    exact (congrArg (fun C : Finset (Fin k) => selected.base ∈ C) selected.block).mp
      (part.blocks.self_mem selected.base (Finset.mem_univ _))
  have outside := old B present fresh selected.base member
  rw [selected.active, selected.inner] at outside
  contradiction

end VehicleRoutingSurvey.Routing
end RppSource_MatchingFreshCutOuter

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

private theorem finRange_perm_cycle {k : ℕ} (cycle : List (Fin k)) (unique : cycle.Nodup) :
    (List.finRange k).Perm (cycle ++ (List.finRange k).filter (fun v => decide (v ∉ cycle))) := by
  let rest := (List.finRange k).filter (fun v => decide (v ∉ cycle))
  have separated : (cycle ++ rest).Nodup := by
    refine List.nodup_append.mpr ⟨unique,(List.nodup_finRange k).filter _,?_⟩
    intro a ha b hb eq
    have outside := of_decide_eq_true (List.mem_filter.mp hb).2
    exact outside (eq ▸ ha)
  apply (List.perm_ext_iff_of_nodup (List.nodup_finRange k) separated).mpr
  intro v
  by_cases member : v ∈ cycle <;> simp [rest,member]

/-- Splitting one root distributes its child subtrees among their own top
slots. As a multiset of allocated IDs the only removal is the root itself. -/
theorem MatchingTopMemberTrees.expansionIds {k : ℕ} {s t : ArithmeticState}
    (old : MatchingTopMemberTrees k s) (next : MatchingTopMemberTrees k t)
    {node : ℕ} {base : Fin k} (children : List (Fin k)) (cycle : List (Fin k)) (offset : ℕ)
    (tree : MatchingMemberTree) (unique : cycle.Nodup) (rotate : cycle.rotate offset = base :: children)
    (root : old.tree base = .blossom base.val node tree .nil)
    (dormant : ∀ p ∈ children, old.tree p = .nil)
    (keeps : ∀ p ∉ cycle, next.tree p = old.tree p)
    (restored : cycle.flatMap (fun p => (next.tree p).registryIds) = tree.registryIds) :
    old.registryIds.Perm (node :: next.registryIds) := by
  let outside := (List.finRange k).filter (fun v => decide (v ∉ cycle))
  let a := fun p => (old.tree p).registryIds
  let b := fun p => (next.tree p).registryIds
  have outsideEq : outside.flatMap b = outside.flatMap a := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro p hp
    exact congrArg MatchingMemberTree.registryIds (keeps _ (of_decide_eq_true (List.mem_filter.mp hp).2))
  have empty : children.flatMap a = [] := List.flatMap_eq_nil_iff.mpr fun p hp => by
    simp [a,dormant p hp,MatchingMemberTree.registryIds]
  have rotateOrder : cycle.Perm (base :: children) := rotate ▸ (List.rotate_perm cycle offset).symm
  have oldSeg := rotateOrder.flatMap_right a
  have baseRows : a base = node :: tree.registryIds := by simp [a,root,MatchingMemberTree.registryIds]
  rw [List.flatMap_cons,empty,List.append_nil,baseRows] at oldSeg
  have enumeration := finRange_perm_cycle cycle unique
  have prior : old.registryIds.Perm ((node :: tree.registryIds) ++ outside.flatMap a) := by
    have ordered := enumeration.flatMap_right a
    rw [List.flatMap_append] at ordered
    exact ordered.trans (oldSeg.append_right _)
  have later : next.registryIds.Perm (tree.registryIds ++ outside.flatMap a) := by
    have ordered := enumeration.flatMap_right b
    rw [List.flatMap_append] at ordered
    change next.registryIds.Perm (cycle.flatMap b ++ outside.flatMap b) at ordered
    rwa [show cycle.flatMap b = tree.registryIds from restored,outsideEq] at ordered
  exact prior.trans (List.Perm.cons node later.symm)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionRegistryIds

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

/-! matching/MatchingExpansionPromotedJobs.lean -/
section RppSource_MatchingExpansionPromotedJobs
namespace VehicleRoutingSurvey.Routing

theorem MatchingLiveCycle.jobsLength {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    (e : MatchingLiveCycle state node B) : (e.tree.jobs none).length = e.geometry.cycle.length :=
  (e.tree.jobs_length none).trans e.arity

def MatchingLiveCycle.jobAt {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    (e : MatchingLiveCycle state node B) (i : Fin e.geometry.cycle.length) : MatchingMemberJob :=
  (e.tree.jobs none)[i.val]'(e.jobsLength.symm ▸ i.isLt)

theorem MatchingLiveCycle.jobAt_mem {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    (e : MatchingLiveCycle state node B) (i : Fin e.geometry.cycle.length) : e.jobAt i ∈ e.tree.jobs none :=
  List.getElem_mem _

theorem MatchingLiveCycle.jobAt_key {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    (e : MatchingLiveCycle state node B) (i : Fin e.geometry.cycle.length) :
    (e.jobAt i).representative = (e.geometry.cycle.get i).val := by
  have keys := e.keys
  rw [← e.tree.jobs_rootKeys none,List.map_map] at keys
  have atKey := congrArg (fun ws : List ℕ => ws[i.val]?) keys
  have inside : i.val < (e.tree.jobs none).length := by rw [e.jobsLength]; exact i.isLt
  simpa only [List.getElem?_map,List.getElem?_eq_getElem inside,
    List.getElem?_eq_getElem i.isLt,Option.map_some,Option.some.injEq,Function.comp_apply,
    MatchingMemberTree.rootKey,List.get_eq_getElem,jobAt] using atKey

noncomputable def MatchingLiveCycle.promotedTrees {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    (e : MatchingLiveCycle state node B) (old : Fin k → MatchingMemberTree) (v : Fin k) : MatchingMemberTree :=
  if h : ∃ i : Fin e.geometry.cycle.length, e.geometry.cycle.get i = v then (e.jobAt h.choose).promotedTree else old v

theorem MatchingLiveCycle.promotedTrees_row {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    (e : MatchingLiveCycle state node B) (old : Fin k → MatchingMemberTree) (i : Fin e.geometry.cycle.length) :
    e.promotedTrees old (e.geometry.cycle.get i) = (e.jobAt i).promotedTree := by
  let h : ∃ j : Fin e.geometry.cycle.length, e.geometry.cycle.get j = e.geometry.cycle.get i := ⟨i,rfl⟩
  have index : h.choose = i := Fin.ext ((List.Nodup.getElem_inj_iff e.geometry.distinct).mp h.choose_spec)
  rw [promotedTrees,dif_pos h,index]

theorem MatchingLiveCycle.promotedTrees_outside {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    (e : MatchingLiveCycle state node B) (old : Fin k → MatchingMemberTree) (v : Fin k) (out : v ∉ e.geometry.cycle) :
    e.promotedTrees old v = old v := by
  apply dif_neg
  rintro ⟨i,rfl⟩
  exact out (List.getElem_mem i.isLt)

theorem MatchingLiveCycle.promotedTrees_ids {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    (e : MatchingLiveCycle state node B) (old : Fin k → MatchingMemberTree) :
    e.geometry.cycle.flatMap (fun v => (e.promotedTrees old v).registryIds) = e.tree.registryIds := by
  rw [← e.tree.promoted_ids none]
  apply congrArg List.flatten
  apply List.ext_getElem (by simp [e.jobsLength])
  intro i hi hj
  have ic : i < e.geometry.cycle.length := by simpa using hi
  have row := e.promotedTrees_row old ⟨i,ic⟩
  simpa only [List.getElem_map,MatchingLiveCycle.jobAt,List.get_eq_getElem] using congrArg MatchingMemberTree.registryIds row

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionPromotedJobs

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

/-- No surviving registered cut can contain the selected top. -/
theorem MatchingSelectedExpansion.noAncestor {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {s : ArithmeticState} {B : Finset (Fin k)}
    (event : MatchingSelectedExpansion part forest positive s B)
    (nested : ∀ C ∈ state.cuts, ∀ u ∈ C, ∀ v ∈ C, part.blocks.block u = part.blocks.block v)
    {C : Finset (Fin k)} (survives : C ∈ state.cuts.erase B) : ¬ B ⊆ C := by
  intro contains
  have base : event.base ∈ B := by
    exact (congrArg (fun C : Finset (Fin k) => event.base ∈ C) event.block).mp
      (part.blocks.self_mem event.base (Finset.mem_univ _))
  apply ((Finset.mem_erase.mp survives).1)
  apply Finset.Subset.antisymm _ contains
  intro v member
  exact (part.block_eq_iff_member event.top v).mp ((nested C (Finset.mem_of_mem_erase survives) v member
    event.base (contains base)).trans event.block)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingLiveCycleDescendants

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




end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowthAfterDual

/-! matching/ExpansionFreshSemantics.lean -/
section RppSource_ExpansionFreshSemantics
namespace VehicleRoutingSurvey.Routing

theorem alternatingRoleCode_eq_outerTag {k : ℕ} (role : AlternatingForestRole (Fin k)) :
    alternatingRoleCode role = 1 ↔ role.outerTag = true := by
  cases role <;> simp [alternatingRoleCode, AlternatingForestRole.outerTag]





end VehicleRoutingSurvey.Routing
end RppSource_ExpansionFreshSemantics

/-! matching/MatchingExpansionSplitFacts.lean -/
section RppSource_MatchingExpansionSplitFacts
namespace VehicleRoutingSurvey.Routing

/-- Each surviving live cut inside the opened top belongs entirely to one of
its direct registry children. This preserves the nesting used to compute
cross-block raw slack from effective endpoint potentials. -/
theorem MatchingExpansionChildPorts.nestedAfter {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state} {B : Finset (Fin k)}
    (registry : MatchingExpansionChildPorts state B) (top : B ∈ Finset.univ.image part.blocks.block)
    (present : B ∈ state.cuts) (zero : state.cutDual B = 0)
    (internal : state.InternalCuts)
    (external : ∀ p ∈ registry.ports, ∀ w, state.partialMate p = some w → w ∉ registry.block p)
    (prior : ∀ S ∈ state.cuts, ∀ u ∈ S, ∀ v ∈ S, part.blocks.block u = part.blocks.block v)
    (descendants : ∀ S ∈ state.cuts.erase B, S ⊆ B → ∃ p ∈ registry.ports, S ⊆ registry.block p) :
    let opened := part.openZeroCut top present zero (registry.toExpansionChildren internal external)
    ∀ S ∈ state.cuts.erase B, ∀ u ∈ S, ∀ v ∈ S, opened.blocks.block u = opened.blocks.block v := by
  intro opened S live u hu v hv
  have share (a : Fin k) (ha : a ∈ S) := prior S (Finset.mem_of_mem_erase live) a ha u hu
  have member (a : Fin k) (ha : a ∈ S) : a ∈ B ↔ u ∈ B := by
    rw [← part.block_eq_iff_member top a, ← part.block_eq_iff_member top u, share a ha]
  have atBlock := part.openZeroCut_block top present zero (registry.toExpansionChildren internal external)
  rw [atBlock, atBlock]
  by_cases inside : u ∈ B
  · have subset : S ⊆ B := fun a ha => (member a ha).mpr inside
    obtain ⟨p, port, all⟩ := descendants S live subset
    rw [if_pos inside, if_pos (subset hv)]
    change registry.block (registry.owner u) = registry.block (registry.owner v)
    rw [registry.unique p port u (all hu), registry.unique p port v (all hv)]
  · rw [if_neg inside, if_neg (fun h => inside ((member v hv).mp h))]
    exact (share v hv).symm

/-- An original already outer before the expansion retains its port and
remains outer after it. Newly outer originals are exactly those accepted by
the executable owner-and-role test. -/
theorem MatchingExpansionChildPorts.outerOriginals {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state} {B : Finset (Fin k)}
    (registry : MatchingExpansionChildPorts state B) (top : B ∈ Finset.univ.image part.blocks.block)
    (present : B ∈ state.cuts) (zero : state.cutDual B = 0)
    (internal : state.InternalCuts)
    (external : ∀ p ∈ registry.ports, ∀ w, state.partialMate p = some w → w ∉ registry.block p)
    {forest : AlternatingForestState (Fin k)} {source base : Fin k} (children : List (Fin k)) (entry : ℕ)
    (baseBlock : part.blocks.block base = B) (baseFixed : part.representative base = base)
    (inner : forest.role base = .inner source) (ports : registry.ports = (base :: children).toFinset)
    {s : ArithmeticState} (size : s.nr 55 = k)
    (encoding : AlternatingForestMemory (forest.expandBlossom source base children entry) (s.nr 51) s.nm)
    (owners : ∀ v : Fin k, expansionChildOf s v.val = if v ∈ B then (registry.owner v).val else k) :
    let opened := part.openZeroCut top present zero (registry.toExpansionChildren internal external)
    let after := forest.expandBlossom source base children entry
    (∀ v, alternatingRoleCode (forest.role (part.representative v)) = 1 →
      opened.representative v = part.representative v ∧ alternatingRoleCode (after.role (opened.representative v)) = 1) ∧
    ∀ v : Fin k, expansionOriginalHasRole s 1 v.val ↔ alternatingRoleCode (forest.role (part.representative v)) ≠ 1 ∧
      alternatingRoleCode (after.role (opened.representative v)) = 1 := by
  intro opened after
  have isBase (v : Fin k) (member : v ∈ B) : part.representative v = base :=
    (part.same_block.mpr (((part.block_eq_iff_member top v).mpr member).trans baseBlock.symm)).trans baseFixed
  have unaffected (v : Fin k) (outside : v ∉ B) := registry.keepsOutsideRoles top present zero internal external
    forest source base children entry ports v outside
  constructor
  · intro v was
    have outside : v ∉ B := by
      intro inside
      rw [isBase v inside, inner] at was
      exact (by decide : (2 : ℕ) ≠ 1) was
    exact ⟨(unaffected v outside).1, (congrArg alternatingRoleCode (unaffected v outside).2).trans was⟩
  · intro v
    by_cases inside : v ∈ B
    · have port : opened.representative v = registry.owner v := by
        change (if v ∈ B then registry.owner v else part.representative v) = _
        rw [if_pos inside]
      simp only [expansionOriginalHasRole, owners v, if_pos inside, size, (registry.owner v).isLt, true_and,
        expansionRepRole, (encoding (registry.owner v)).1, isBase v inside, inner, port] <;> simp [alternatingRoleCode, after]
    · have role : after.role (opened.representative v) = forest.role (part.representative v) :=
        (unaffected v inside).2
      simp [expansionOriginalHasRole, owners v, inside, size, role]

theorem MatchingExpansionChildPorts.inactiveAfter {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state} {B : Finset (Fin k)}
    (ports : MatchingExpansionChildPorts state B) (chosen : B ∈ Finset.univ.image part.blocks.block)
    (present : B ∈ state.cuts) (zero : state.cutDual B = 0) (internal : state.InternalCuts)
    (external : ∀ p ∈ ports.ports, ∀ w, state.partialMate p = some w → w ∉ ports.block p)
    {forest : AlternatingForestState (Fin k)} {source base : Fin k} (children : List (Fin k)) (entry : ℕ)
    (atBase : part.representative base = base) (atBlock : part.blocks.block base = B)
    (cycle : ports.ports = (base :: children).toFinset)
    (inactive : ∀ v, part.representative v ≠ v → forest.role v = .unlabelled) :
    let opened := part.openZeroCut chosen present zero (ports.toExpansionChildren internal external)
    let after := forest.expandBlossom source base children entry
    ∀ v, opened.representative v ≠ v → after.role v = .unlabelled := by
  intro opened after v hidden
  have fixed (p : Fin k) (hp : p ∈ ports.ports) : opened.representative p = p := by
    have member := ports.containsPort p hp
    change (if p ∈ B then ports.owner p else part.representative p) = p
    rw [if_pos (ports.subset p hp member),ports.unique p hp p member]
  have away : v ∉ base :: children := fun h => hidden (fixed v (cycle.symm ▸ List.mem_toFinset.mpr h))
  have offBase : v ≠ base := fun eq => away (eq.symm ▸ List.mem_cons_self)
  have oldInactive : part.representative v ≠ v := by
    intro old
    by_cases member : v ∈ B
    · exact offBase (old.symm.trans ((part.same_block.mpr (((part.block_eq_iff_member chosen v).mpr member).trans atBlock.symm)).trans atBase))
    · apply hidden
      change (if v ∈ B then ports.owner v else part.representative v) = v
      rwa [if_neg member]
  exact (forest.expandAlong_keeps_role source base v _ (not_on_blossom_expansion entry away) offBase).trans (inactive v oldInactive)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionSplitFacts

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







end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionCoreFrame

/-! matching/MatchingExpansionExactLinks.lean -/
section RppSource_MatchingExpansionExactLinks
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory





/-- At the actual full-arm exit, matching parent links decode to the
original endpoint pair and all parent links witness tightness in the opened partition. -/
theorem ExpansionPersistentState.exactSearch {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s t : ArithmeticState}
    {tightRep : Sym2 (Fin k) → Prop} (top : CompactTopMatching part)
    (final : ExpansionPersistentState s t forest state.partialMate tightRep
      (matchingExactExpansionEdge state part.representative) part.representative)
    (unmatched : ∀ v ∉ state.covered, forest.role (part.representative v) = .outer none)
    (inactive : ∀ v, part.representative v ≠ v → forest.role v = .unlabelled) :
    MatchingForestLinkMemory part forest t ∧ MatchingForestOriginalWitnesses part forest t ∧
      CompactMatchingSearchForest part forest state.partialMate part.tightBetween := by
  have weak : ExpansionPersistentState s t forest state.partialMate tightRep
      (fun e => oddCutDualEdgeValue state.cuts state.potential state.cutDual e = edgeCost cost e) part.representative := by
    refine ⟨final.encoding,final.valid,?_,final.representatives,final.nodes,final.potentials,final.cutDuals⟩
    intro child parent attached
    obtain ⟨e,bytes,ends,value,_⟩ := final.witnesses child parent attached
    exact ⟨e,bytes,ends,value⟩
  refine ⟨⟨inactive,?_⟩,weak.toSearch top unmatched⟩
  intro child parent outer
  have row := final.valid child
  rw [outer] at row
  have matched := state.partialMate_some_iff.mp row.2.2.1
  have attached : (forest.role child).parent = some parent := by rw [outer]; rfl
  obtain ⟨e,words,ends,_,physical⟩ := final.witnesses child parent attached
  have head : part.representative e.1 = parent := congrArg Prod.fst ends
  have tail : part.representative e.2 = child := congrArg Prod.snd ends
  have original := physical (by simpa only [Sym2.map_mk,head,tail] using matched)
  have distinct : parent ≠ child := mt Sym2.mk_isDiag_iff.mpr (state.perfect.1 _ matched).1
  have endpoints := top.crossing_endpoints original (fun same =>
    distinct (head.symm.trans ((part.same_block.mpr same).trans tail)))
  exact words.trans (Prod.ext (congrArg Fin.val (endpoints.1.symm.trans head))
    (congrArg Fin.val (endpoints.2.symm.trans tail)))

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionExactLinks

/-! matching/MatchingExpansionOpenedCore.lean -/
section RppSource_MatchingExpansionOpenedCore
namespace VehicleRoutingSurvey.Routing

/-- The cut arm of the dispatcher consumes the cut represented by the
selector's original dictionary words. -/
theorem MatchingChosenStage.cutSelection {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {original s : ArithmeticState}
    (chosen : MatchingChosenStage part forest positive (matchingTopCutAt part) original s)
    (tag : matchingEventClass s = 2) :
    ∃ B, chosen.event = .cut B ∧ Nonempty (MatchingSelectedExpansion part forest positive s B) := by
  exact match event : chosen.event with
  | .cut B => ⟨B,rfl,matchingSelectedExpansion_ofView (event ▸ chosen.kind)⟩
  | .edge e =>
    let view : MatchingEventClassView part.blocks forest (part.representativeOf positive)
        (matchingTopCutAt part) s (.edge e) := event ▸ chosen.kind
    match view with
    | ⟨_,_,_,_,_,_,_,Or.inl ⟨eq,_⟩⟩ => ((by decide : (2 : ℕ) ≠ 1) (tag.symm.trans eq)).elim
    | ⟨_,_,_,_,_,_,_,Or.inr ⟨eq,_⟩⟩ => ((by decide : (2 : ℕ) ≠ 0) (tag.symm.trans eq)).elim





end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionOpenedCore

/-! matching/MatchingExpansionCacheLayout.lean -/
section RppSource_MatchingExpansionCacheLayout
namespace VehicleRoutingSurvey.Routing

theorem MatchingStageStorage.expansionCache {k : ℕ} {original s : ArithmeticState}
    (store : MatchingStageStorage k original s) (layout : MatchingCacheLayout k s)
    (unit : s.nr 9 = 1) (zero : s.nr 14 = 0) (potentials : s.nr 62+k ≤ s.nr 59) :
    ExpansionCacheFrame s ∧ s.nr 65+2*(k*k) ≤ s.nr 88 ∧ s.nr 74+k ≤ s.nr 88 ∧
      ExpansionCutReadLayout k s ∧ ExpansionPersistentLayout k s := by
  have dim := store.warm.size
  have forest := store.warm.representativesAfter
  have rep := store.warm.candidatesAfter
  have three := layout.rows
  have dict := layout.idsBefore
  have pairs := layout.recordsBefore
  have rates := layout.slacksBefore
  have scores := layout.ratesBefore
  have nodes := store.nodes
  have duals := store.cutDuals
  have work := store.promotion
  have mask := store.mask
  have map := store.memberMap
  obtain ⟨r,n,w,p,m⟩ := store.expansion
  refine ⟨⟨unit,zero,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_,?_,?_,potentials,?_⟩⟩ <;> omega

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionCacheLayout

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

/-! matching/MatchingExpansionCoreTables.lean -/
section RppSource_MatchingExpansionCoreTables
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 8192

/-- The post-advance blocks keep the constants and metric-table pointers.
Their few low writable registers can be checked directly on the code. -/
theorem matchingExpansionCore_low {s t : ArithmeticState} {ticks : ℕ}
    (run : BlockRuns (appendBlock prepareExpansionChildrenBlock expandMatchingAfterMembersBlock) ticks s t)
    (r : ℕ) (used : r ∈ ([9,14,20,21] : List ℕ)) : t.nr r = s.nr r := by
  rw [← run.run]
  apply arithmeticRun_keeps_from_destination_list
    [0,1,2,3,4,5,6,7,8,10,11,12,15,16,17,18,19,22,23,24,25,26,27,28,43,44,45,46,47,49,81,82,87,94,95,96,97,98,99]
    (by decide)
  simp at used ⊢
  omega

theorem MatchingExpansionCoreFrame.keepsStorage {k : ℕ} {original s t : ArithmeticState} {ticks : ℕ}
    (frame : MatchingExpansionCoreFrame k s t) (storage : MatchingStageStorage k original s)
    (run : BlockRuns (appendBlock prepareExpansionChildrenBlock expandMatchingAfterMembersBlock) ticks s t) :
    MatchingStageStorage k original t := by
  exact storage.keeps fun r used =>
    if low : r ∈ ([20,21] : List ℕ) then
      matchingExpansionCore_low run r (by simp at low ⊢; omega)
    else
      frame.ports r (by simp [matchingFixedStorageRegisters] at used; simp at low; omega)
        (by simp [matchingFixedStorageRegisters] at used; simp; omega)

theorem MatchingExpansionCoreFrame.oldCache {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {cutAt : Fin k → Finset (Fin k)}
    {original s t : ArithmeticState} (frame : MatchingExpansionCoreFrame k s t)
    (stage : MatchingAdvancedStage part forest positive cutAt original s) (storage : MatchingStageStorage k original s) :
    (∀ i < t.nr 61, MatchingCandidateRowValid cutAt t i) ∧
    (∀ group : MatchingCandidateGroup k, LeastSlackEntry ((matchingSearchSlacks part forest positive).filter fun d =>
      @decide _ (Classical.propDecidable (group.admits part.blocks forest (part.representativeOf positive) d)))
      (readMatchingCandidate cutAt t group.slot)) ∧
    MatchingSearchOuterBuckets t part.representative (fun v => alternatingRoleCode (forest.role v)) cost
      (effectiveVertexPotential state.cuts state.potential state.cutDual) := by
  have keep (r : ℕ) (high : 30 ≤ r := by decide)
      (away : r ∉ [43,44,45,46,47,49,81,82,87,94,95,96,97,98] := by decide) := frame.ports r high away
  have read := matchingCacheRegionReads stage.reads.layout (fun r h => keep r (by simp at h; omega) (by simp at h ⊢; omega))
    (fun a lo hi => frame.natural a (.inr (.inl ⟨lo,storage.nodes.symm ▸ hi⟩))) (fun _ _ _ => congrFun frame.real _) cutAt stage.valid
  refine ⟨fun i hi => (read.1 i (keep 61 ▸ hi)).1,?_,?_,?_,?_⟩
  · intro g
    rw [(read.1 g.slot (stage.reads.layout.rows.symm ▸ g.slot_lt)).2]
    exact stage.least g
  · intro i hi
    rw [(read.2 i hi).1]
    exact stage.pairs.valid i hi
  · intro a b diff left right
    rw [frame.realRegisters,(read.2 _ (matchingPairSlot_lt a b)).2]
    exact stage.pairs.least a b diff left right
  · intro a b off
    rw [(read.2 _ (matchingPairSlot_lt a b)).2]
    exact stage.pairs.inactive a b off

theorem MatchingExpansionCoreFrame.openedReads {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state next : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {opened : CompactMatchingPartition next} {forest after : AlternatingForestState (Fin k)}
    {positive : 0 < k} {cutAt : Fin k → Finset (Fin k)} {original s t : ArithmeticState}
    (frame : MatchingExpansionCoreFrame k s t) (stage : MatchingAdvancedStage part forest positive cutAt original s)
    (storage : MatchingStageStorage k original s) (metricReg : t.nr 20 = s.nr 20) (offsetReg : t.nr 21 = s.nr 21)
    (dual : MatchingSearchDualMemory opened after t) :
    MatchingRefreshInput t opened.representative (fun v => alternatingRoleCode (after.role v)) cost
      (effectiveVertexPotential next.cuts next.potential next.cutDual) := by
  have keep (r : ℕ) (high : 30 ≤ r := by decide)
      (away : r ∉ [43,44,45,46,47,49,81,82,87,94,95,96,97,98] := by decide) := frame.ports r high away
  have old := stage.reads
  have layout := old.layout
  have off := storage.warm.offsetsBefore
  have mates := storage.warm.matesBefore
  refine ⟨⟨dual.dimension,(keep 61).trans layout.rows,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,dual.reps,
    fun v => (dual.roles v).1,?_,dual.effective⟩
  · rw [keep 58,keep 61,keep 54]; exact layout.idsBefore
  · rw [keep 54,keep 61,keep 65]; exact layout.recordsBefore
  · rw [keep 59,keep 61,keep 60]; exact layout.slacksBefore
  · rw [keep 60,keep 61,keep 66]; exact layout.ratesBefore
  · rw [offsetReg,keep 58]; exact old.offsetsBefore
  · rw [keep 57,keep 58]; exact old.representativesBefore
  · rw [keep 51,keep 58]; exact old.rolesBefore
  · rw [metricReg,keep 59]; exact old.metricBefore
  · rw [keep 62,keep 59]; exact old.effectiveBefore
  · intro v
    rw [offsetReg,frame.natural _ (.inl (by have := v.isLt; omega))]
    exact old.offsets v
  · intro i j
    rw [metricReg,frame.real]
    exact old.metric i j

theorem MatchingExpansionCoreFrame.openedPrimal {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {B : Finset (Fin k)} {original s t : ArithmeticState}
    (frame : MatchingExpansionCoreFrame k s t) (storage : MatchingStageStorage k original s)
    (primal : CompactMatchingPrimalDualMemory state original s) (present : B ∈ state.cuts) (zero : state.cutDual B = 0) :
    CompactMatchingPrimalDualMemory (state.eraseZeroCut present zero) original t := by
  have keep (r : ℕ) (high : 30 ≤ r := by decide)
      (away : r ∉ [43,44,45,46,47,49,81,82,87,94,95,96,97,98] := by decide) := frame.ports r high away
  have mates := storage.warm.matesBefore
  refine ⟨(keep 55).trans primal.dimension,(keep 56).trans primal.oddMap,?_,?_,?_,?_,?_⟩
  · rw [keep 50]; exact primal.mateAbove
  · intro v
    rw [keep 50,frame.natural _ (.inl (by have := v.isLt; omega))]
    exact primal.mate v
  · intro r high
    exact (keep r (by omega) (by simp; omega)).trans (primal.saved r high)
  · intro a hi
    have below := primal.mateAbove
    exact (frame.natural _ (.inl (by omega))).trans (primal.natural _ hi)
  · intro a hi
    rw [frame.real]; exact primal.real _ hi

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionCoreTables

/-! matching/MatchingExpansionCollectTables.lean -/
section RppSource_MatchingExpansionCollectTables
namespace VehicleRoutingSurvey.Routing





theorem matchingExpansionFreshSources_values {k : ℕ} {s : ArithmeticState} (size : s.nr 55 = k) :
    freshExpansionOriginals s (s.nr 55) = (matchingExpansionFreshSources k s).map Fin.val := by
  let pick (v : ℕ) := decide (expansionChildOf s v < s.nr 55) &&
    decide (expansionRepRole s (expansionChildOf s v) = 1)
  have range : (List.finRange k).map Fin.val = List.range k := by
    apply List.ext_getElem <;> simp
  change (List.range (s.nr 55)).filter pick = _
  rw [size,← range,List.filter_map]
  rfl



end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionCollectTables

/-! matching/MatchingExpansionArchiveFrame.lean -/
section RppSource_MatchingExpansionArchiveFrame
namespace VehicleRoutingSurvey.Routing

theorem matchingExpansionArchiveCell_protected {k : ℕ} {s : ArithmeticState} {a : ℕ}
    (h : matchingExpansionArchiveCell k s a) : matchingExpansionProtected k s a := .inr (.inr h)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionArchiveFrame

/-! matching/MatchingExpansionFinalFrame.lean -/
section RppSource_MatchingExpansionFinalFrame
namespace VehicleRoutingSurvey.Routing

theorem MatchingRefreshInput.expansionFootprint {k : ℕ} {s t : ArithmeticState} {ticks : ℕ}
    {rep : Fin k → Fin k} {role : Fin k → ℕ} {cost : Fin k → Fin k → ℝ} {eff : Fin k → ℝ}
    (input : MatchingRefreshInput s rep role cost eff) (run : BlockRuns restoreExpansionCacheBlock ticks s t)
    (entry : s.pc = 0) (running : s.halted = false) (work : ExpansionCacheFrame s)
    (above : s.nr 65+2*(k*k) ≤ s.nr 88) : ExpansionRepairFootprint k s t := by
  exact restoreExpansionCacheBlock_footprint run entry running work input.layout
    ⟨fun v h => (Nat.add_lt_add_left h _).trans_le input.offsetsBefore,
      fun v h => input.offsets ⟨v,h⟩⟩
    ⟨fun v h => (Nat.add_lt_add_left h _).trans_le input.representativesBefore,
      fun v h => (input.representatives ⟨v,h⟩).symm ▸ (rep ⟨v,h⟩).isLt⟩ above

/-- Cache repair changes the search rows while preserving the relabelled
representatives, node IDs, forest roles, and both dual tables. -/
def ExpansionPersistentState.dualAfterRepair {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s t : ArithmeticState}
    {tightRep tightOriginal : Sym2 (Fin k) → Prop}
    (fixed : ExpansionCacheRestored s t)
    (memory : ExpansionPersistentState s t forest state.partialMate tightRep tightOriginal part.representative)
    (dual : MatchingSearchDualMemory part forest s) :
    { after : MatchingSearchDualMemory part forest t // after.node = dual.node } := by
  exact ⟨{
    dimension := (fixed.fixed 55 (by decide) (by decide)).trans dual.dimension
    separated := (fixed.fixed 62 (by decide) (by decide)).symm ▸
      (fixed.fixed 75 (by decide) (by decide)).symm ▸ dual.separated
    reps v := (memory.representatives v.val v.isLt).trans (dual.reps v)
    roles := memory.encoding
    effective v := (memory.potentials v.val v.isLt).trans (dual.effective v)
    node := dual.node
    nodeNonzero := dual.nodeNonzero
    nodeInjective := dual.nodeInjective
    cutValues C present := (memory.cutDuals (dual.node C)).trans (dual.cutValues C present)
    top v := (memory.nodes v.val v.isLt).trans (dual.top v) }, rfl⟩

theorem ExpansionCacheRestored.keepsPrimal {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {original s t : ArithmeticState}
    (restored : ExpansionCacheRestored s t) (storage : MatchingStageStorage k original s)
    (layout : ExpansionPersistentLayout k s) (primal : CompactMatchingPrimalDualMemory state original s) :
    CompactMatchingPrimalDualMemory state original t := by
  exact
    let matesBelow := storage.warm.matesBefore.trans ((Nat.le_add_right _ _).trans layout.forestBelowCache)
    let naturalPrefix := primal.mateAbove.trans ((Nat.le_add_right _ _).trans matesBelow)
    let realPrefix := storage.inputFloor.symm ▸ (Nat.le_add_right (s.nr 62) k).trans layout.potentialsBelowCache
    {
      dimension := (restored.fixed 55 (by decide) (by decide)).trans primal.dimension
      oddMap := (restored.fixed 56 (by decide) (by decide)).trans primal.oddMap
      mateAbove := (restored.fixed 50 (by decide) (by decide)).symm ▸ primal.mateAbove
      mate v := (restored.fixed 50 (by decide) (by decide)).symm ▸
        (restored.natural _ ((Nat.add_lt_add_left v.isLt _).trans_le matesBelow)).trans (primal.mate v)
      saved r high := (restored.fixed r (Nat.le_trans (by decide) high)
        (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) high))).trans (primal.saved r high)
      natural a ha := (restored.natural a (ha.trans_le naturalPrefix)).trans (primal.natural a ha)
      real a ha := (restored.real a (ha.trans_le realPrefix)).trans (primal.real a ha) }

/-- The final cache work list is disjoint from both fixed header arrays and
the dynamic archives. Thus the full branch keeps each original cycle row. -/
theorem MatchingExpansionCoreFrame.archiveAfterCache {k : ℕ} {original s m t : ArithmeticState}
    (frame : MatchingExpansionCoreFrame k s m) (storage : MatchingStageStorage k original s)
    (cache : ExpansionRepairFootprint k m t) :
    ∀ a, matchingExpansionArchiveCell k s a → t.nm a = s.nm a := by
  intro a h
  apply Eq.trans _ (frame.natural _ (matchingExpansionArchiveCell_protected h))
  have keep (r : ℕ) (high : 30 ≤ r := by decide)
      (away : r ∉ [43,44,45,46,47,49,81,82,87,94,95,96,97,98] := by decide) := frame.ports r high away
  have nodes := storage.nodes
  have first := storage.starts
  have work := storage.promotion
  have mask := storage.mask
  have map := storage.memberMap
  obtain ⟨rn,nw,wp,pm,ms⟩ := storage.expansion
  apply cache.natural
  · right
    rw [keep 65]
    rcases h with ⟨lo,hi⟩ | high <;> omega
  · rw [keep 88]
    rcases h with ⟨lo,hi⟩ | high
    · exact .inl (by omega)
    · exact .inr (by omega)

theorem MatchingCycleRecordOrder.afterExpansion {k stage : ℕ} {original s t : ArithmeticState}
    (order : MatchingCycleRecordOrder s) (storage : MatchingStageStorage k original s)
    {counts : MatchingStageCounts} (budget : MatchingRegistryBudget k stage s counts) (searching : stage < k/2)
    (regs : ∀ r ∈ ([55,68,76,77,78,80] : List ℕ), t.nr r = s.nr r)
    (bytes : ∀ a, matchingExpansionArchiveCell k s a → t.nm a = s.nm a) : MatchingCycleRecordOrder t := by
  have keep (r : ℕ) (on : r ∈ ([55,68,76,77,78,80] : List ℕ) := by decide) := regs r on
  have lengths := storage.lengths
  have left := storage.traceLeft
  have right := storage.traceRight
  have marks := storage.traceMarks
  have witness := storage.witnesses
  have base (i : ℕ) (inside : i < s.nr 76) : matchingCycleRecordStart t i = matchingCycleRecordStart s i := by
    have small := budget.allocated_fits searching inside
    rw [matchingCycleRecordStart,keep 77]
    exact bytes _ (.inl ⟨by omega,by omega⟩)
  apply order.transport (by simp only [matchingRebaseScratchEnd,keep 80,keep 55]) (keep 76) (keep 68)
    (fun i _ hi => base i hi)
  intro i _ hi
  have small := budget.allocated_fits searching hi
  simp only [matchingCycleRecordEnd,base i hi,keep 78,bytes (s.nr 78+i) (.inl ⟨by omega,by omega⟩)]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionFinalFrame

/-! matching/MatchingExpansionOwnersAtExit.lean -/
section RppSource_MatchingExpansionOwnersAtExit
namespace VehicleRoutingSurvey.Routing

/-- The owner map survives publication and forest relabelling until the
cache collector consumes it, including the sentinel on every outside original. -/
theorem MatchingLiveCycleMemory.ownersAtExit {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    {e : MatchingLiveCycle state node B} {original s m a p t : ArithmeticState}
    (memory : MatchingLiveCycleMemory e s) (storage : MatchingStageStorage k original s)
    (atNode : s.nm (s.nr 74+s.nr 92) = node B) (baseWord : s.nr 92 = e.base.val)
    (map : ExpansionMemberMapResult s m e.tree) (layout : ExpansionInputLayout k m)
    {entry : Fin e.geometry.cycle.length} (arc : ExpansionArcReady m a entry.val e.geometry.baseSlot.val)
    (pub : ExpansionPublication a p) {after : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)}
    {tightRep tightOriginal : Sym2 (Fin k) → Prop} {rep : Fin k → Fin k}
    (exit : MatchingExpandedForest after mate tightRep tightOriginal rep p t) :
    ∀ v : Fin k, expansionChildOf t v.val = if v ∈ B then (e.ports.owner v).val else k := by
  have mReg (r : ℕ) (h : r ∉ [0,6,7,15,16,17,18,19,22,23,24,25,26,28,87,97] := by decide) := map.fixed r h
  have aReg (r : ℕ) (h : r ∉ expansionArcScratch := by decide) := arc.fixed r h
  have pReg (r : ℕ) (h : r ∉ [0,6,7,10,15,16,17,25] := by decide) := pub.fixed r h
  have dim := storage.warm.size
  have roles := storage.warm.representativesAfter
  obtain ⟨repsNodes,nodesWitness,witnessPath,pathMap,mapStack⟩ := storage.expansion
  have within := e.base.isLt
  have nodeSafe : outsideMatchingMemberScratch s (s.nr 74+s.nr 92) := by
    rw [baseWord]; exact ⟨.inl (by omega),.inl (by omega)⟩
  have rows := memory.arcRows atNode nodeSafe map layout arc
  have len := arc.cycleLength.symm.trans rows.1
  have size : e.geometry.cycle.length ≤ k := by simpa using e.geometry.distinct.length_le_card
  have pSize := (aReg 55).trans ((mReg 55).trans dim)
  have bounds (j : ℕ) (hj : j < a.nr 19) : (expansionCycleRow a j).representative < a.nr 55 := by
    let ix : Fin e.geometry.cycle.length := ⟨j,rows.1 ▸ hj⟩
    rw [pSize,(rows.2 ix).1]
    exact (e.geometry.cycle.get ix).isLt
  intro v
  change t.nm (t.nr 79+v.val) = _
  rw [exit.keepsMembers (by rw [pReg 51,pReg 79,aReg 51,aReg 79,mReg 51,mReg 79]; omega)
    (by rw [pReg 90,pReg 79,aReg 90,aReg 79,mReg 90,mReg 79]; omega)]
  rw [pub.keepsMembers (by rw [aReg 57,mReg 57,pSize,aReg 79,mReg 79]; omega)
    (by rw [aReg 74,mReg 74,pSize,aReg 79,mReg 79]; omega) bounds]
  rw [arc.keepsMembers (len.symm ▸ entry.isLt) (len.symm ▸ e.geometry.baseSlot.isLt)
    (by rw [mReg 86,mReg 79,len]; omega)]
  exact map.encodesChildPorts e.geometry.members dim v

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionOwnersAtExit

/-! matching/MatchingExpansionChildTop.lean -/
section RppSource_MatchingExpansionChildTop
namespace VehicleRoutingSurvey.Routing

/-- A non-singleton promoted child uses the exact subtree registered at
the child's cut ID and its old representative becomes the new top base. -/
theorem MatchingLiveCycles.childTop {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (live : MatchingLiveCycles registry) {B : Finset (Fin k)} (h : B ∈ state.cuts)
    (v : Fin k) (port : v ∈ (live.entry B h).ports.ports) (many : ((live.entry B h).ports.block v).card ≠ 1) :
    let e := live.entry B h
    let C := e.ports.block v
    let d := live.entry C (Finset.mem_of_mem_erase (e.ports.live v port many))
    d.base = v ∧ e.promotedTrees registry.trees.tree v = .blossom v.val (dual.node C) d.tree .nil := by
  intro e C d
  have present : C ∈ state.cuts := Finset.mem_of_mem_erase (e.ports.live v port many)
  obtain ⟨i,hi,hit⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp (e.geometry.ports ▸ port))
  let ix : Fin e.geometry.cycle.length := ⟨i,hi⟩
  let job := e.jobAt ix
  have atPort : e.geometry.cycle.get ix = v := hit
  have member : job ∈ e.tree.jobs none := e.jobAt_mem ix
  have key : job.representative = v.val := (e.jobAt_key ix).trans (congrArg Fin.val atPort)
  have id : job.node = dual.node C := by
    have eq := e.childNode job member v key
    rwa [if_neg many] at eq
  have proper : job.proper := e.tree.jobs_proper none (live.memory B h).members.proper.2.2.1 job member
  have row : e.promotedTrees registry.trees.tree v = job.promotedTree := atPort ▸ e.promotedTrees_row registry.trees.tree ix
  cases c : job.children with
  | none =>
    have off : job.node = 0 := by simpa [MatchingMemberJob.proper,c] using proper
    exact (dual.nodeNonzero C present (id.symm.trans off)).elim
  | some sub =>
    obtain ⟨D,known,alloc,tree,base,_⟩ := live.child B h job member sub c
    have same : D = C := dual.nodeInjective known present (alloc.trans id)
    subst D
    have first : d.base = v := Fin.ext (base.trans key)
    refine ⟨first,?_⟩
    rw [row]
    change job.promotedTree = .blossom v.val (dual.node C) (live.entry C present).tree .nil
    simp only [MatchingMemberJob.promotedTree,c,key,id,tree]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionChildTop

/-! matching/MatchingExpansionPromotedTrees.lean -/
section RppSource_MatchingExpansionPromotedTrees
namespace VehicleRoutingSurvey.Routing

/-- A strict child of the selected top block has no tree of its own in the
old top table. Its tree is still nested under the selected root. -/
theorem MatchingLiveCycles.hiddenChildTree {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {chosen s : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (live : MatchingLiveCycles registry) {B : Finset (Fin k)}
    (event : MatchingSelectedExpansion part forest positive chosen B) :
    ∀ p ∈ (live.entry B event.present).geometry.children, registry.trees.tree p = .nil := by
  exact
    let e := live.entry B event.present
    fun p child =>
      let base : e.base = event.base := by
        have select (C : Finset (Fin k)) (present : C ∈ state.cuts) (eq : C = B)
            (port : (live.entry C present).base = event.base) : e.base = event.base := by
          subst C
          exact port
        exact select _ _ event.block (live.top event.base (event.block.symm ▸ event.present) event.active).1
      let rotated : (e.base :: e.geometry.children).Nodup := e.geometry.rotate ▸
        List.nodup_rotate.mpr e.geometry.distinct
      let notBase : p ≠ event.base := fun h => (List.nodup_cons.mp rotated).1
        ((base.trans h.symm).symm ▸ child)
      let port : p ∈ e.ports.ports := e.geometry.rotatedPorts.symm ▸
        List.mem_toFinset.mpr (List.mem_cons_of_mem _ child)
      let inside := e.ports.subset p port (e.ports.containsPort p port)
      let rep : part.representative p = event.base :=
        (part.same_block.mpr (((part.block_eq_iff_member event.top p).mpr inside).trans event.block.symm)).trans event.active
      let empty : blossomNodeAt s p.val = 0 := (dual.top p).trans
        (if_neg (fun fixed => notBase (fixed.1.symm.trans rep)))
      MatchingMemberTree.eq_nil_of_rootKeys ((registry.trees.roots p).trans (if_pos empty))

/-- Restore the direct child trees at their own compact representatives.
The physical table agrees with the decoded split and all allocated IDs
except the retired root retain their multiplicity. -/
theorem MatchingLiveCycles.promoteTrees {k stage : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {original s t : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (live : MatchingLiveCycles registry) {B : Finset (Fin k)} (present : B ∈ state.cuts)
    (storage : MatchingStageStorage k original s) (order : MatchingCycleRecordOrder s)
    {counts : MatchingStageCounts} (budget : MatchingRegistryBudget k stage s counts) (searching : stage < k/2)
    (start : t.nr 77 = s.nr 77) (len : t.nr 78 = s.nr 78) (cache : t.nr 65 = s.nr 65)
    (natural : ∀ a, matchingExpansionArchiveCell k s a → t.nm a = s.nm a) :
    let e := live.entry B present
    let g := e.geometry
    ∀ (root : registry.trees.tree e.base = .blossom e.base.val (dual.node B) e.tree .nil),
      (∀ p ∈ g.children, registry.trees.tree p = .nil) →
      (∀ v : Fin k, blossomNodeAt t v.val = if v ∈ e.ports.ports then
        (if (e.ports.block v).card = 1 then 0 else dual.node (e.ports.block v)) else blossomNodeAt s v.val) →
      ∃ trees : MatchingTopMemberTrees k t, trees.tree = e.promotedTrees registry.trees.tree ∧
        (∀ v, (trees.tree v).readable t.nm (t.nr 77) (t.nr 78) (fun a => t.nr 65+2*(k*k) ≤ a)) ∧
        registry.trees.registryIds.Perm (dual.node B :: trees.registryIds) := by
  intro e g root dormant nodeWords
  let tree := e.promotedTrees registry.trees.tree
  have bound (n : ℕ) (inside : n ∈ registry.trees.registryIds) : 0 < n ∧ n < s.nr 76 := by
    obtain ⟨C,h,rfl⟩ := (registry.keys n).mp inside
    exact ⟨Nat.pos_of_ne_zero (dual.nodeNonzero C h),registry.allocated C h⟩
  have memory := (live.memory B present).members
  have well : e.tree.proper := memory.proper.2.2.1
  have enc : e.tree.encoded s.nm (s.nr 77) (s.nr 78) := memory.encoded.2.2.1
  have safe : e.tree.readable s.nm (s.nr 77) (s.nr 78) (outsideMatchingMemberScratch s) := by
    simpa [matchingRebaseNodeState,outsideMatchingMemberScratch] using! memory.readable.2.2.2.1
  have above : e.tree.recordsAbove s.nm (s.nr 77) (s.nr 80+3*s.nr 55) := by
    simpa [matchingRebaseNodeState] using memory.above.2.1
  have typed (v : Fin k) : (tree v).proper ∧ (tree v).encoded s.nm (s.nr 77) (s.nr 78) ∧
      (∀ n ∈ (tree v).registryIds, n ∈ registry.trees.registryIds) ∧
      (tree v).rootKeys = (if blossomNodeAt t v.val = 0 then [] else [MatchingMemberTree.rootKey v.val (blossomNodeAt t v.val)]) := by
    by_cases inside : v ∈ g.cycle
    · obtain ⟨i,hi,hit⟩ := List.mem_iff_getElem.mp inside
      let ix : Fin g.cycle.length := ⟨i,hi⟩
      let job := e.jobAt ix
      have same : g.cycle.get ix = v := hit
      have selected : tree v = job.promotedTree := same ▸ e.promotedTrees_row registry.trees.tree ix
      have listed := e.jobAt_mem ix
      have key : job.representative = v.val := (e.jobAt_key ix).trans (congrArg Fin.val same)
      have port := (e.owner job listed v key).1
      have id : blossomNodeAt t v.val = job.node := by rw [nodeWords,if_pos port,e.childNode job listed v key]
      have proper : job.proper := e.tree.jobs_proper none well job listed
      have encoded := (e.tree.jobs_encoded none _ _ _ _ _ enc safe above job listed).1
      have ids (n : ℕ) (h : n ∈ job.promotedTree.registryIds) : n ∈ registry.trees.registryIds := by
        apply live.ids B present
        rw [← e.tree.promoted_ids none]
        exact List.mem_flatMap.mpr ⟨job,listed,h⟩
      rw [selected]
      refine ⟨?_,?_,ids,?_⟩
      · cases c : job.children with
        | none => simp [MatchingMemberJob.promotedTree,c,MatchingMemberTree.proper]
        | some sub =>
          simpa [MatchingMemberJob.promotedTree,MatchingMemberJob.proper,c,MatchingMemberTree.proper] using proper
      · cases c : job.children with
        | none => simp [MatchingMemberJob.promotedTree,c,MatchingMemberTree.encoded]
        | some sub => simpa [MatchingMemberJob.promotedTree,MatchingMemberJob.tree,c] using encoded
      · cases c : job.children with
        | none =>
          have z : job.node = 0 := by simpa [MatchingMemberJob.proper,c] using proper
          simp [MatchingMemberJob.promotedTree,c,MatchingMemberTree.rootKeys,id,z]
        | some sub =>
          have liveNode : 0 < job.node := (show 0 < job.node ∧ 2 ≤ sub.arity ∧ sub.proper by
            simpa [MatchingMemberJob.proper,c] using proper).1
          simp [MatchingMemberJob.promotedTree,c,MatchingMemberTree.rootKeys,id,Nat.ne_of_gt liveNode,key]
    · have selected : tree v = registry.trees.tree v := e.promotedTrees_outside _ v inside
      have notPort : v ∉ e.ports.ports := fun h => inside (List.mem_toFinset.mp (g.ports ▸ h))
      have node : blossomNodeAt t v.val = blossomNodeAt s v.val := (nodeWords v).trans (if_neg notPort)
      rw [selected,node]
      exact ⟨registry.trees.proper v,registry.trees.encoded v,fun n h =>
        List.mem_flatMap.mpr ⟨v,List.mem_finRange v,h⟩,registry.trees.roots v⟩
  have footprint (v : Fin k) := (tree v).expansionFootprint storage order budget searching
    (fun n h => bound n ((typed v).2.2.1 n h))
  let out : MatchingTopMemberTrees k t := {
    tree := tree
    roots v := (typed v).2.2.2
    proper v := (typed v).1
    encoded v := by rw [start,len]; exact MatchingMemberTree.encoded_congr (typed v).2.1 (footprint v) natural }
  refine ⟨out,rfl,?_,?_⟩
  · intro v
    rw [start,len,cache]
    have warm := storage.warm
    have floor := storage.nodes
    have starts := storage.starts
    have lengths := storage.lengths
    obtain ⟨_,nw,wp,pm,ms⟩ := storage.expansion
    have high : (tree v).readable s.nm (s.nr 77) (s.nr 78) (fun a => s.nr 65+2*(k*k) ≤ a) :=
      (tree v).readableAbove order (by omega) (by omega) (by unfold matchingRebaseScratchEnd; omega)
        (fun n h => bound n ((typed v).2.2.1 n h))
    exact MatchingMemberTree.readable_after_move (tree := tree v)
      (MatchingMemberTree.readableAnd (tree := tree v) (footprint v) high) natural
  · exact registry.trees.expansionIds out g.children g.cycle g.baseSlot.val e.tree g.distinct g.rotate root dormant
      (e.promotedTrees_outside _) (e.promotedTrees_ids _)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionPromotedTrees

/-! matching/MatchingExpansionRegistryView.lean -/
section RppSource_MatchingExpansionRegistryView
namespace VehicleRoutingSurvey.Routing

/-- Promote the selected archive's direct subtrees and retire exactly its ID.
Other cuts retain their identifiers and their old containment relations. -/
def MatchingRegistryView.afterExpansion {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {B : Finset (Fin k)} {forest expanded : AlternatingForestState (Fin k)} {s t : ArithmeticState}
    {before : MatchingSearchDualMemory part forest s} (registry : MatchingRegistryView before)
    (top : B ∈ Finset.univ.image part.blocks.block) (present : B ∈ state.cuts) (zero : state.cutDual B = 0)
    (ports : MatchingExpansionChildPorts state B) (internal : state.InternalCuts)
    (external : ∀ p ∈ ports.ports, ∀ w, state.partialMate p = some w → w ∉ ports.block p)
    (descendants : ∀ C ∈ state.cuts.erase B, C ⊆ B → ∃ p ∈ ports.ports, C ⊆ ports.block p)
    (after : MatchingSearchDualMemory (part.openZeroCut top present zero (ports.toExpansionChildren internal external)) expanded t)
    (trees : MatchingTopMemberTrees k t)
    (bytes : ∀ v, (trees.tree v).readable t.nm (t.nr 77) (t.nr 78) (fun a => t.nr 65+2*(k*k) ≤ a))
    (promoted : registry.trees.registryIds.Perm (before.node B :: trees.registryIds))
    (ids : ∀ C ∈ state.cuts.erase B, after.node C = before.node C) (cursor : t.nr 76 = s.nr 76) :
    MatchingRegistryView after := by
  have unique := List.nodup_cons.mp (promoted.nodup registry.unique)
  refine ⟨trees,bytes,unique.2,?_,?_,?_,?_,?_⟩
  · intro id
    constructor
    · intro h
      have inAll := promoted.mem_iff.mpr (List.mem_cons_of_mem _ h)
      obtain ⟨C,member,assigned⟩ := (registry.keys id).mp inAll
      have away : C ≠ B := by
        intro same
        apply unique.1
        simpa only [← same,assigned] using h
      have survives := Finset.mem_erase.mpr ⟨away,member⟩
      exact ⟨C,survives,(ids C survives).trans assigned⟩
    · rintro ⟨C,member,assigned⟩
      have survives : C ∈ state.cuts.erase B := member
      obtain ⟨away,old⟩ := Finset.mem_erase.mp survives
      have allocated : before.node C = id := (ids _ survives).symm.trans assigned
      have inAll := promoted.mem_iff.mp ((registry.keys id).mpr ⟨C,old,allocated⟩)
      refine (List.mem_cons.mp inAll).resolve_left ?_
      intro same
      exact away (before.nodeInjective old present (allocated.trans same))
  · intro C live
    rw [cursor,ids C live]
    exact registry.allocated C (Finset.mem_of_mem_erase live)
  · intro C live
    exact registry.nontrivial C (Finset.mem_of_mem_erase live)
  · intro C c D d
    exact registry.laminar C (Finset.mem_of_mem_erase c) D (Finset.mem_of_mem_erase d)
  · exact ports.nestedAfter top present zero internal external registry.nested descendants

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionRegistryView

/-! matching/MatchingLiveCyclesOpened.lean -/
section RppSource_MatchingLiveCyclesOpened
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Canonical archive after an exhausted top has been opened. Each surviving
entry keeps its bases and internal matching, and every promoted top now
points to the original direct-child subtree. -/
noncomputable def MatchingLiveCycles.afterOpening {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest after : AlternatingForestState (Fin k)} {positive : 0 < k} {s chosen t : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (live : MatchingLiveCycles registry) {B : Finset (Fin k)} (event : MatchingSelectedExpansion part forest positive chosen B)
    (zero : state.cutDual B = 0) (internal : state.InternalCuts) :
    let e := live.entry B event.present
    ∀ (external : ∀ p ∈ e.ports.ports, ∀ w, state.partialMate p = some w → w ∉ e.ports.block p),
    let opened := part.openZeroCut event.top event.present zero (e.ports.toExpansionChildren internal external)
    ∀ (next : MatchingSearchDualMemory opened after t) (out : MatchingRegistryView next),
      next.node = dual.node → out.trees.tree = e.promotedTrees registry.trees.tree →
      (∀ C (h : C ∈ state.cuts.erase B), MatchingLiveCycleMemory (live.entry C (Finset.mem_of_mem_erase h)) t) →
      MatchingLiveCycles out := by
  intro e external opened next out ids trees saved
  let state' := state.eraseZeroCut event.present zero
  have survive {C : Finset (Fin k)} (hc : C ∈ state.cuts.erase B) {D : Finset (Fin k)}
      (hd : D ∈ state.cuts) (inside : D ⊆ C) : D ∈ state.cuts.erase B := by
    refine Finset.mem_erase.mpr ⟨?_,hd⟩
    intro eq
    exact event.noAncestor registry.nested hc (eq ▸ inside)
  have sameEntry {C D : Finset (Fin k)} (eq : C = D) (hc : C ∈ state.cuts) (hd : D ∈ state.cuts) :
      (live.entry C hc).base = (live.entry D hd).base ∧ (live.entry C hc).tree = (live.entry D hd).tree := by
    subst D
    exact ⟨rfl,rfl⟩
  let entry (C : Finset (Fin k)) (hc : C ∈ state.cuts.erase B) : MatchingLiveCycle state' next.node C :=
    let d := live.entry C (Finset.mem_of_mem_erase hc)
    d.reindex
      (fun p hp multi => Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (d.ports.live p hp multi)).1,
        survive hc (Finset.mem_of_mem_erase (d.ports.live p hp multi)) (d.ports.subset _ hp)⟩)
      (fun p _ _ => congrFun ids (d.ports.block p))
      (fun D h => d.descendants D (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp h).1,
        Finset.mem_of_mem_erase (Finset.mem_erase.mp h).2⟩)) rfl
      (fun i => (oddCutDualEdgeValue_erase_zero _ event.present _ _ zero _).trans (d.geometry.tight i))
  refine ⟨entry,?_,?_,?_,?_⟩
  · intro C h
    let d := live.entry C (Finset.mem_of_mem_erase h)
    have mem := saved C h
    refine ⟨?_,?_⟩
    · change MatchingMemberRoot (matchingRebaseNodeState t (next.node C)) d.tree
      rw [ids]; exact mem.members
    · change MatchingNodeCycleRows t (next.node C) d.geometry.cycle d.geometry.edges
      rw [ids]; exact mem.rows
  · intro p h fixed
    let C := opened.blocks.block p
    have current : C ∈ state.cuts.erase B := h
    have prior := Finset.mem_of_mem_erase current
    have split := part.openZeroCut_block event.top event.present zero (e.ports.toExpansionChildren internal external) p
    change (live.entry C prior).base = p ∧ out.trees.tree p = .blossom p.val (next.node C) (live.entry C prior).tree .nil
    rw [trees,ids]
    by_cases owned : p ∈ B
    · have itself : e.ports.owner p = p := by
        change (if p ∈ B then e.ports.owner p else part.representative p) = p at fixed
        rwa [if_pos owned] at fixed
      have port : p ∈ e.ports.ports := itself ▸ (e.ports.covered p owned).1
      have name : C = e.ports.block p := by
        rw [if_pos owned] at split
        exact split.trans (congrArg e.ports.block itself)
      have many : (e.ports.block p).card ≠ 1 := by
        have bound := registry.nontrivial C prior
        rw [name] at bound; omega
      have child := live.childTop event.present p port many
      have same := sameEntry name prior (name ▸ prior)
      rw [same.1,same.2,congrArg dual.node name]
      exact child
    · have name : C = part.blocks.block p := split.trans (if_neg owned)
      have oldFixed : part.representative p = p := by
        change (if p ∈ B then e.ports.owner p else part.representative p) = p at fixed
        rwa [if_neg owned] at fixed
      have away : p ∉ e.geometry.cycle := by
        intro on
        have port : p ∈ e.ports.ports := e.geometry.ports.symm ▸ List.mem_toFinset.mpr on
        exact owned (e.ports.subset p port (e.ports.containsPort p port))
      rw [e.promotedTrees_outside _ p away]
      have same := sameEntry name prior (name ▸ prior)
      rw [same.1,same.2,congrArg dual.node name]
      exact live.top p (name ▸ prior) oldFixed
  · intro C h job on sub child
    let d := live.entry C (Finset.mem_of_mem_erase h)
    obtain ⟨D,hd,id,tree,base,block⟩ := live.child C (Finset.mem_of_mem_erase h) job on sub child
    have port := (d.owner job on (live.entry D hd).base base.symm).1
    have inside : D ⊆ C := block.symm ▸ d.ports.subset _ port
    exact ⟨D,survive h hd inside,(congrFun ids D).trans id,tree,base,block⟩
  · intro C h n below
    obtain ⟨D,hd,id,inside⟩ := live.descendantCut C (Finset.mem_of_mem_erase h) n below
    exact (out.keys n).mpr ⟨D,survive h hd inside,(congrFun ids D).trans id⟩

/-- Promote the direct children and recover a full live registry from the
unchanged archive after the selector cache is repaired. -/
theorem MatchingLiveCycles.registryAfterOpening {k stage : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest after : AlternatingForestState (Fin k)} {positive : 0 < k} {original s chosen t : ArithmeticState}
    {dual : MatchingSearchDualMemory part forest s} {registry : MatchingRegistryView dual}
    (live : MatchingLiveCycles registry) {B : Finset (Fin k)}
    (event : MatchingSelectedExpansion part forest positive chosen B)
    (zero : state.cutDual B = 0) (internal : state.InternalCuts)
    (storage : MatchingStageStorage k original s) (order : MatchingCycleRecordOrder s)
    {counts : MatchingStageCounts} (budget : MatchingRegistryBudget k stage s counts) (searching : stage < k/2)
    (fixed : ∀ r ∈ ([55,65,76,77,78,79,80] : List ℕ), t.nr r = s.nr r)
    (archive : ∀ a, matchingExpansionArchiveCell k s a → t.nm a = s.nm a) :
    let e := live.entry B event.present
    ∀ (external : ∀ p ∈ e.ports.ports, ∀ w, state.partialMate p = some w → w ∉ e.ports.block p),
    let opened := part.openZeroCut event.top event.present zero (e.ports.toExpansionChildren internal external)
    ∀ (next : MatchingSearchDualMemory opened after t), next.node = dual.node →
      ∃ out : MatchingRegistryView next, Nonempty (MatchingLiveCycles out) := by
  exact
    let e := live.entry B event.present
    fun external =>
      let opened := part.openZeroCut event.top event.present zero (e.ports.toExpansionChildren internal external)
      fun next ids =>
        let selected := live.selectedBase event
        let base : e.base = event.base := selected.1
        let root : registry.trees.tree e.base = .blossom e.base.val (dual.node B) e.tree .nil := by
          rw [base]
          exact selected.2
        let port : e.base ∈ e.ports.ports := e.geometry.rotatedPorts.symm ▸
          List.mem_toFinset.mpr List.mem_cons_self
        let nodeWords (v : Fin k) : blossomNodeAt t v.val = if v ∈ e.ports.ports then
            (if (e.ports.block v).card = 1 then 0 else dual.node (e.ports.block v)) else blossomNodeAt s v.val := by
          simpa only [next.top,dual.top,ids] using (e.ports.topAfter event.top event.present zero internal external
            (base ▸ event.block) (base ▸ event.active) port dual.node v).symm
        (live.promoteTrees event.present storage order budget searching (fixed 77 (by decide))
          (fixed 78 (by decide)) (fixed 65 (by decide)) archive root (live.hiddenChildTree event) nodeWords).elim
          fun trees ⟨same,safe,retired⟩ =>
            let out := registry.afterExpansion event.top event.present zero e.ports internal external e.descendants
              (show MatchingSearchDualMemory opened after t from next) trees safe retired
              (fun C _ => congrFun ids C) (fixed 76 (by decide))
            let old (C : Finset (Fin k)) (h : C ∈ state.cuts.erase B) :=
              live.memoryOnExpansionArchive storage order budget searching
                (fun r hr => fixed r (by simp at hr ⊢; omega)) archive C (Finset.mem_of_mem_erase h)
            ⟨out, ⟨live.afterOpening event zero internal external next out ids same old⟩⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingLiveCyclesOpened

/-! matching/MatchingExpansionCredit.lean -/
section RppSource_MatchingExpansionCredit
namespace VehicleRoutingSurvey.Routing

/-- Charge the actual collected count against the two RAM states. The
selected cutoff counts only surviving IDs and uses each partition's own
representatives to count its outer originals and top blocks. -/
theorem MatchingSelectedExpansion.stageCharge {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {B : Finset (Fin k)} {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {chosen s m t : ArithmeticState}
    (event : MatchingSelectedExpansion part forest positive chosen B) (zero : state.cutDual B = 0)
    {registry : MatchingExpansionChildPorts state B} (internal : state.InternalCuts)
    (external : ∀ p ∈ registry.ports, ∀ w, state.partialMate p = some w → w ∉ registry.block p)
    (children : List (Fin k)) (entry : ℕ) (ports : registry.ports = (event.base :: children).toFinset)
    (dual : MatchingSearchDualMemory part forest s) (oldRegistry : MatchingRegistryView dual)
    (fresh : MatchingFreshCutOuter part forest dual.node (s.nr 39)) (size : m.nr 55 = k)
    (encoding : AlternatingForestMemory (forest.expandBlossom event.parent event.base children entry) (m.nr 51) m.nm)
    (owners : ∀ v : Fin k, expansionChildOf m v.val = if v ∈ B then (registry.owner v).val else k) :
    let opened := part.openZeroCut event.top event.present zero (registry.toExpansionChildren internal external)
    let expanded := forest.expandBlossom event.parent event.base children entry
    ∀ (next : MatchingSearchDualMemory opened expanded t), MatchingRegistryView next →
      (∀ C ∈ state.cuts.erase B, next.node C = dual.node C) → t.nr 39 = s.nr 39 →
      MatchingStageTransition (matchingStageCountsFromRAM k s (s.nr 39))
        (1+(freshExpansionOriginals m (m.nr 55)).length) (matchingStageCountsFromRAM k t (t.nr 39)) := by
  intro opened expanded next current ids cutoff
  let inherited := state.cuts.filter (fun C => dual.node C < s.nr 39)
  let before := part.outerBlock forest positive
  let after := opened.outerBlock expanded positive
  have counts := matchingStageCountsFromRAM_eq dual positive (s.nr 39) oldRegistry.trees oldRegistry.unique oldRegistry.keys
  have endCounts := matchingStageCountsFromRAM_eq next positive (t.nr 39) current.trees current.unique current.keys
  have inheritedAfter : (state.cuts.erase B).filter (fun C => next.node C < t.nr 39) = inherited.erase B := by
    ext C
    simp only [inherited, Finset.mem_filter, Finset.mem_erase, cutoff]
    constructor
    · rintro ⟨⟨away, live⟩, short⟩
      exact ⟨away, live, ids C (Finset.mem_erase.mpr ⟨away,live⟩) ▸ short⟩
    · rintro ⟨away, live, short⟩
      exact ⟨⟨away,live⟩,(ids C (Finset.mem_erase.mpr ⟨away,live⟩)).symm ▸ short⟩
  have labels := registry.outerOriginals event.top event.present zero internal external children entry
    event.block event.active event.inner ports size encoding owners
  have prev (v : Fin k) : before (part.blocks.block v) ↔ alternatingRoleCode (forest.role (part.representative v)) = 1 := by
    simp only [before,CompactMatchingPartition.outerBlock,part.representativeOf_block]
  have later (v : Fin k) : after (opened.blocks.block v) ↔ alternatingRoleCode (expanded.role (opened.representative v)) = 1 := by
    simp only [after,CompactMatchingPartition.outerBlock,opened.representativeOf_block]
  have stays (v : Fin k) (_ : v ∈ Finset.univ) (on : before (part.blocks.block v)) :
      after (opened.blocks.block v) ∧ opened.blocks.block v = part.blocks.block v := by
    have active := (prev v).mp on
    have outside : v ∉ B := by
      intro inside
      have base := (part.same_block.mpr (((part.block_eq_iff_member event.top v).mpr inside).trans event.block.symm)).trans event.active
      rw [base,event.inner] at active
      exact (by decide : (2 : ℕ) ≠ 1) active
    exact ⟨(later v).mpr (labels.1 v active).2, (part.openZeroCut_block event.top event.present zero _ v).trans (if_neg outside)⟩
  let gained := (Finset.univ.filter (fun v => ¬before (part.blocks.block v))) \
    Finset.univ.filter (fun v => ¬after (opened.blocks.block v))
  have exactGained (v : Fin k) : expansionOriginalHasRole m 1 v.val ↔ v ∈ gained := by
    rw [labels.2 v]
    simp only [gained,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and,prev,later,not_not,expanded,opened]
  have cardinality := freshExpansionOriginals_card size gained exactGained
  have charge := matchingPartitionCounts_expand part.blocks opened.blocks before after
    (event.inherited fresh event.present) stays
  rw [counts, endCounts, cardinality]
  change MatchingStageTransition _ (1+gained.card)
    (matchingPartitionCounts opened.blocks after ((state.cuts.erase B).filter (fun C => next.node C < t.nr 39)))
  rw [inheritedAfter]
  exact charge

/-- The expansion retires one inherited cut and allocates no replacement.
The continuing search keeps its allocation budget and its outer fresh cuts. -/
theorem MatchingSelectedExpansion.ramBudget {k stage : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {B : Finset (Fin k)} {forest : AlternatingForestState (Fin k)} {positive : 0 < k}
    {chosen s m t : ArithmeticState} (event : MatchingSelectedExpansion part forest positive chosen B)
    (zero : state.cutDual B = 0) {ports : MatchingExpansionChildPorts state B} (internal : state.InternalCuts)
    (external : ∀ p ∈ ports.ports, ∀ w, state.partialMate p = some w → w ∉ ports.block p)
    (children : List (Fin k)) (entry : ℕ) (cycle : ports.ports = (event.base :: children).toFinset)
    (before : MatchingSearchDualMemory part forest s) (oldRegistry : MatchingRegistryView before)
    (fresh : MatchingFreshCutOuter part forest before.node (s.nr 39))
    (budget : MatchingRegistryBudget k stage s (matchingStageCountsFromRAM k s (s.nr 39)))
    (size : m.nr 55 = k)
    (encoding : AlternatingForestMemory (forest.expandBlossom event.parent event.base children entry) (m.nr 51) m.nm)
    (owners : ∀ v : Fin k, expansionChildOf m v.val = if v ∈ B then (ports.owner v).val else k)
    (cutoff : t.nr 39 = s.nr 39) (cursor : t.nr 76 = s.nr 76) :
    let opened := part.openZeroCut event.top event.present zero (ports.toExpansionChildren internal external)
    let expanded := forest.expandBlossom event.parent event.base children entry
    ∀ (after : MatchingSearchDualMemory opened expanded t), MatchingRegistryView after → after.node = before.node →
      MatchingStageTransition (matchingStageCountsFromRAM k s (s.nr 39))
        (1+(freshExpansionOriginals m (m.nr 55)).length) (matchingStageCountsFromRAM k t (t.nr 39)) ∧
      MatchingRegistryBudget k stage t (matchingStageCountsFromRAM k t (t.nr 39)) ∧
      MatchingFreshCutOuter opened expanded after.node (t.nr 39) := by
  exact
    let opened := part.openZeroCut event.top event.present zero (ports.toExpansionChildren internal external)
    let expanded := forest.expandBlossom event.parent event.base children entry
    fun after current ids =>
      let labels := ports.outerOriginals event.top event.present zero internal external children entry
        event.block event.active event.inner cycle size encoding owners
      let same : ∀ C ∈ state.cuts.erase B, after.node C = before.node C := fun C _ => congrFun ids C
      let transition := event.stageCharge zero internal external children entry cycle before oldRegistry fresh
        size encoding owners after current same cutoff
      ⟨transition, budget.advance transition cutoff cursor.symm.le (cursor.trans_le (Nat.le_succ _)),
        cutoff.symm ▸ fresh.restrict (opened := opened) (after := expanded)
          (fun _ h => Finset.mem_of_mem_erase h) same (fun v outer =>
            (alternatingRoleCode_eq_outerTag (expanded.role (opened.representative v))).mp
              (labels.1 v ((alternatingRoleCode_eq_outerTag (forest.role (part.representative v))).mpr outer)).2)⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionCredit

/-! matching/MatchingDispatchExpansion.lean -/
section RppSource_MatchingDispatchExpansion
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem MatchingDispatchState.expandArm
    {k i : ℕ} {cost : Fin k → Fin k → ℝ} {original s : ArithmeticState}
    (before : MatchingDispatchState cost original i s)
    (searching : i < k/2) (symmetric : ∀ u v, cost u v = cost v u)
    (entry : s.pc = 0) (running : s.halted = false)
    (expand : matchingEventClass s = 2)
    (saved : (s.nr 92,s.nr 93) = matchingOriginalGrowthEvent s) :
    ∃ t ticks charge, BlockRuns matchingExpandHandlerBlock ticks s t ∧
      t.halted = false ∧ t.nr 33 = s.nr 33 ∧
      Nonempty (MatchingPreparedStage cost original i (matchingStageSnapshot t)) ∧
      MatchingStageTransition (matchingStageCountsFromRAM k s (s.nr 39)) charge
        (matchingStageCountsFromRAM k (matchingStageSnapshot t) ((matchingStageSnapshot t).nr 39)) ∧
      ticks + 32 ≤ 1024*(k+1)*charge := by
  obtain ⟨B,selected,⟨chosen⟩⟩ := before.selected.cutSelection expand
  have baseWord : s.nr 92 = chosen.base.val := congrArg Prod.fst (saved.trans chosen.ports)
  let bound : DualBound (MatchingDualEvent k) := ⟨before.selected.event, s.rr 1⟩
  let state := before.state.advanceSearch before.part before.search before.positive before.internal bound before.selected.adjustment
  let part := before.part.advanceSearch before.search before.positive before.internal bound before.selected.adjustment
  let forest := before.forest
  have exhausted : state.cutDual B = 0 := by
    have tight := before.selected.adjustment.2.2.2
    rw [selected] at tight
    exact tight.2.2
  let event : MatchingSelectedExpansion part forest before.positive s B :=
    ⟨chosen.base, chosen.parent, chosen.ports, chosen.classTag, chosen.block,
      chosen.active, chosen.representative, chosen.top, chosen.nontrivial, chosen.inner⟩
  have inherited := chosen.inherited before.fresh chosen.present
  obtain ⟨d,ticks,advance,limit,dLive,dZero,nm,regs,abstract,ids,trees⟩ :=
    before.selected.advance before.search before.internal entry running before.one before.storage
  let a := {d with pc := 0}
  have port (r : ℕ) (kept : r ∉ ([0,6,7,10,11,12,14] : List ℕ) := by decide) :
      a.nr r = s.nr r := regs r kept
  let advanced : MatchingAdvancedStage part forest before.positive (matchingTopCutAt part) original a := abstract.atEntry
  have nodes : advanced.dual.node = before.selected.dual.node := ids
  have oldTrees : advanced.registry.trees.tree = before.selected.registry.trees.tree := trees
  have storage := before.storage.keeps (t := a) (fun r present =>
    port r (by simp [matchingFixedStorageRegisters] at present; simp; omega))
  let cycles := before.cycles.advanceDual before.search before.positive before.internal bound before.selected.adjustment
    advanced.registry nodes oldTrees nm (fun r pres => port r (by simp at pres ⊢; omega))
  have top : CompactTopMatching part := ⟨before.top.interior,before.top.matchedBase⟩
  have int : state.InternalCuts := before.internal
  obtain ⟨entrySlot, coreExit, mapped, path, published, coreTicks, core, coreLive, coreBound,
    memberMap, coreLayout, arc, publication, openedForest, coreFrame, openedDual, nodeIds⟩ :=
    event.openedCore advanced cycles storage top int exhausted ((port 92).trans baseWord)
      rfl dLive ((port 9).trans before.one) dZero
  have run : BlockRuns expandMatchingRegistryHandlerBlock (ticks+coreTicks) s _ := advance.append core
  let e := cycles.entry B event.present
  let geom := e.geometry
  have baseAt : e.base = event.base := (cycles.selectedBase event).1
  have baseFixed : part.representative e.base = e.base := by rw [baseAt]; exact event.active
  have baseBlock : part.blocks.block e.base = B := by rw [baseAt]; exact event.block
  let selectedBase : MatchingSelectedExpansion part forest before.positive s B :=
    ⟨e.base,event.parent,by rw [baseAt]; exact event.ports,event.classTag,baseBlock,baseFixed,
      by rw [baseAt]; exact event.representative,event.top,event.nontrivial,by rw [baseAt]; exact event.inner⟩
  let external := geom.exposesPorts top baseFixed baseBlock
  let next := state.eraseZeroCut event.present exhausted
  let opened := part.openZeroCut event.top event.present exhausted (e.ports.toExpansionChildren int external)
  let entrance := expansionEntryFromBase geom.cycle.length entrySlot.val geom.baseSlot.val
  let after := forest.expandBlossom event.parent e.base geom.children entrance
  let ready := {coreExit with pc := 0}
  have readyFrame : MatchingExpansionCoreFrame k a ready :=
    ⟨coreFrame.natural,coreFrame.real,coreFrame.realRegisters,coreFrame.ports⟩
  let readyDual : MatchingSearchDualMemory opened after ready :=
    ⟨openedDual.dimension,openedDual.separated,openedDual.reps,openedDual.roles,openedDual.effective,
      openedDual.node,openedDual.nodeNonzero,openedDual.nodeInjective,openedDual.cutValues,openedDual.top⟩
  have readyForest : MatchingExpandedForest after next.partialMate (fun _ => True)
      (matchingExactExpansionEdge next opened.representative) opened.representative published ready :=
    ⟨openedForest.encoding,openedForest.valid,openedForest.edgeWitness,openedForest.natural,
      openedForest.real,openedForest.realRegisters,openedForest.fixed⟩
  have readyStorage := (coreFrame.keepsStorage storage core).keeps (t := ready) (fun _ _ => rfl)
  have corePorts (r : ℕ) (used : r ∈ ([9,14,20,21] : List ℕ) := by decide) :
      ready.nr r = a.nr r := matchingExpansionCore_low core r used
  have reads := readyFrame.openedReads advanced storage (corePorts 20) (corePorts 21) readyDual
  obtain ⟨work,above,nodeBefore,cutLayout,persistentLayout⟩ := readyStorage.expansionCache reads.layout
    ((corePorts 9).trans ((port 9).trans before.one)) ((corePorts 14).trans dZero) reads.effectiveBefore
  have atSelected : a.nr 92 = e.base.val := (port 92).trans (baseWord.trans (congrArg Fin.val baseAt).symm)
  have atNode : a.nm (a.nr 74+a.nr 92) = advanced.dual.node B := by
    rw [show a.nr 92 = event.base.val from (port 92).trans baseWord]
    exact (event.registry_node advanced.dual event.present).1
  have owners := (cycles.memory B event.present).ownersAtExit storage atNode atSelected memberMap coreLayout
    arc publication readyForest
  obtain ⟨valid,least,pairs⟩ := readyFrame.oldCache advanced storage
  have portSet : e.ports.ports = (e.base :: geom.children).toFinset := e.geometry.rotatedPorts
  obtain ⟨t,cacheTicks,cache,live,cacheBound,restored,rows,newPairs,newReads⟩ :=
    e.ports.searchRows selectedBase exhausted int external geom.children entrance portSet advanced.links.inactive
      owners symmetric advanced.registry.nested e.descendants rfl coreLive work above nodeBefore cutLayout valid least pairs readyDual reads
  let result := relocateState expandMatchingRegistryHandlerBlock.length t
  have full : BlockRuns matchingExpandHandlerBlock (ticks+coreTicks+cacheTicks) s result := run.append cache
  have footprint := reads.expansionFootprint cache rfl coreLive work above
  have persistent := restoreExpansionCacheBlock_keeps_persistentState readyForest restored footprint persistentLayout
  have afterPrimal := restored.keepsPrimal readyStorage persistentLayout
    (readyFrame.openedPrimal storage advanced.primal event.present exhausted)
  let nextDual := ExpansionPersistentState.dualAfterRepair restored persistent readyDual
  let final := matchingStageSnapshot result
  have snapshotPort (r : ℕ) (safe : r ≠ 30 := by decide) : final.nr r = t.nr r :=
    Function.update_of_ne safe _ _
  have outputPort (r : ℕ) (safe : r ∉ matchingExpansionWrittenRegisters := by decide) : result.nr r = s.nr r :=
    matchingExpandHandler_keeps_register full safe
  have finalPort (r : ℕ) (safe : r ∉ matchingExpansionWrittenRegisters := by decide) (away : r ≠ 30 := by decide) :
      final.nr r = a.nr r := (snapshotPort r away).trans
    ((outputPort r safe).trans (port r (by simp [matchingExpansionWrittenRegisters] at safe; simp; omega)).symm)
  have finalStorage := storage.keeps (t := final) (fun r h =>
    finalPort r (by simp [matchingFixedStorageRegisters] at h; simp [matchingExpansionWrittenRegisters]; omega)
      (by simp [matchingFixedStorageRegisters] at h; omega))
  have naturalAdvance : a.nm = s.nm := nm
  have order := before.order.transport (t := a) (by simp only [matchingRebaseScratchEnd,port 80,port 55])
    (port 76) (port 68)
    (fun _ _ _ => by simp only [matchingCycleRecordStart,port 77,naturalAdvance])
    (fun _ _ _ => by simp only [matchingCycleRecordEnd,matchingCycleRecordStart,port 77,port 78,naturalAdvance])
  have startCounts : matchingStageCountsFromRAM k a (a.nr 39) = matchingStageCountsFromRAM k s (s.nr 39) := by
    rw [matchingStageCountsFromRAM_eq advanced.dual before.positive _ advanced.registry.trees
      advanced.registry.unique advanced.registry.keys,
      matchingStageCountsFromRAM_eq before.selected.dual before.positive _ before.selected.registry.trees
      before.selected.registry.unique before.selected.registry.keys,nodes,port 39]
    rfl
  have allocation := before.budget.keeps (port 39) (port 76) startCounts
  have freshBefore : MatchingFreshCutOuter part forest advanced.dual.node (a.nr 39) := by
    rw [nodes,port 39]
    exact before.fresh
  have archiveBytes : ∀ addr, matchingExpansionArchiveCell k a addr → final.nm addr = a.nm addr :=
    readyFrame.archiveAfterCache (t := t) storage footprint
  let dual : MatchingSearchDualMemory opened after final :=
    ⟨nextDual.val.dimension,nextDual.val.separated,nextDual.val.reps,nextDual.val.roles,nextDual.val.effective,
      nextDual.val.node,nextDual.val.nodeNonzero,nextDual.val.nodeInjective,nextDual.val.cutValues,nextDual.val.top⟩
  have finalIds : dual.node = advanced.dual.node := nextDual.property.trans nodeIds
  obtain ⟨registry,⟨liveCycles⟩⟩ := cycles.registryAfterOpening (t := final) selectedBase exhausted int
    storage order allocation searching (fun r h => finalPort r (by simp at h; simp [matchingExpansionWrittenRegisters]; omega)
      (by simp at h; omega)) archiveBytes external dual finalIds
  have finalOrder := order.afterExpansion storage allocation searching (t := final)
    (fun r h => finalPort r (by simp at h; simp [matchingExpansionWrittenRegisters]; omega) (by simp at h; omega)) archiveBytes
  obtain ⟨transition,budget,fresh⟩ := selectedBase.ramBudget exhausted int external geom.children entrance
    portSet advanced.dual advanced.registry freshBefore allocation readyDual.dimension readyDual.roles owners
    (finalPort 39) (finalPort 76) dual registry finalIds
  let charge := 1+(freshExpansionOriginals ready (ready.nr 55)).length
  have freshSize : (freshExpansionOriginals ready (ready.nr 55)).length = (matchingExpansionFreshSources k ready).length := by
    rw [matchingExpansionFreshSources_values readyDual.dimension,List.length_map]
  have newTop : CompactTopMatching opened :=
    top.openZeroCut event.top event.present exhausted (e.ports.toExpansionChildren int external)
  have unmatched := e.ports.exposedRoots event.top event.present exhausted int external advanced.search
    event.parent e.base geom.children entrance baseBlock baseFixed selectedBase.inner portSet
  have inactive := e.ports.inactiveAfter event.top event.present exhausted int external
    (source := event.parent) geom.children entrance baseFixed baseBlock portSet advanced.links.inactive
  obtain ⟨link, witnesses, search⟩ := persistent.exactSearch newTop unmatched inactive
  have finalWitness : MatchingForestOriginalWitnesses opened after final := fun h => witnesses h
  have finalPrimal : CompactMatchingPrimalDualMemory next original final :=
    ⟨afterPrimal.dimension,afterPrimal.oddMap,afterPrimal.mateAbove,afterPrimal.mate,
      fun r large => (snapshotPort r (by omega)).trans (afterPrimal.saved r large),afterPrimal.natural,afterPrimal.real⟩
  have finalReads := newReads.keeps (t := final) ⟨fun _ _ => rfl,fun _ _ _ _ => rfl⟩
    (fun r h => snapshotPort r (by simp [matchingRefreshTableRegisters] at h; omega))
  have finalRows : MatchingSearchRows opened after before.positive (matchingTopCutAt opened) final :=
    ⟨finalReads.layout,rows.count,rows.ids,rows.slacks,rows.rates,rows.valid,rows.least⟩
  have finalPairs : MatchingSearchOuterBuckets final opened.representative (fun v => alternatingRoleCode (after.role v))
      cost (effectiveVertexPotential next.cuts next.potential next.cutDual) :=
    ⟨newPairs.valid,newPairs.least,newPairs.inactive⟩
  let post : MatchingActiveStage opened after before.positive (matchingTopCutAt opened) original i final :=
    ⟨finalPrimal,newTop,int.eraseZeroCut event.present exhausted, search,finalWitness,
      link.advance rfl (fun _ => rfl),dual,registry,fresh,finalRows,finalPairs,finalReads,budget,
      restored.zero,((finalPort 9).trans (port 9)).trans before.one⟩
  let prepared : MatchingPreparedStage cost original i final :=
    ⟨next,opened,after,before.positive,before.count,post,liveCycles,finalStorage,finalOrder⟩
  have small : ticks+coreTicks+cacheTicks ≤ 425*k*charge := by
    have limit := expansionHandlerCost_le_charge (fresh := (matchingExpansionFreshSources k ready).length) before.positive
    change _ ≤ 425*k*(1+(freshExpansionOriginals ready (ready.nr 55)).length)
    rw [freshSize]
    omega
  have overhead := Nat.le_mul_of_pos_right 32 (by dsimp [charge]; omega : 0 < charge)
  have bound := Nat.mul_le_mul_right charge (by omega : 425*k+32 ≤ 1024*(k+1))
  rw [Nat.add_mul] at bound
  refine ⟨result,_,charge,full,live,outputPort 33,⟨prepared⟩,?_,by omega⟩
  rw [← startCounts]
  exact transition

set_option maxRecDepth 16384 in
/-- The executable dispatcher opens its selected exhausted cut and returns
the prepared selector state, paying for all stages of the real arm. -/
theorem MatchingDispatchState.expand {k i : ℕ} {cost : Fin k → Fin k → ℝ}
    {original s : ArithmeticState} (before : MatchingDispatchState cost original i s)
    (searching : i < k/2) (symmetric : ∀ u v, cost u v = cost v u)
    (entry : s.pc = 0) (running : s.halted = false) (active : s.nr 33 ≠ 0)
    (expand : matchingEventClass s = 2) :
    ∃ next ticks charge, BlockRuns weightedBlossomEventHandler ticks s next ∧
      next.halted = false ∧ next.nr 33 ≠ 0 ∧
      Nonempty (MatchingPreparedStage cost original i (matchingStageSnapshot next)) ∧
      MatchingStageTransition (matchingLoopCounts k i s) charge (matchingLoopCounts k i (matchingStageSnapshot next)) ∧
      ticks ≤ 1024*(k+1)*charge := by
  obtain ⟨middle,classTicks,classify,classBound,midLive,tag,zero,one,two,ends,id,natural,real,rr,ports,_⟩ :=
    before.selected.dispatchDirect entry running before.one (Or.inr expand)
  let a := {middle with pc := 0}
  have port (r : ℕ) (used : r = 9 ∨ r = 20 ∨ r = 21 ∨ (30 ≤ r ∧ r ≤ 34) ∨
      (39 ≤ r ∧ r ≤ 90) ∨ 100 ≤ r := by decide) : a.nr r = s.nr r := ports r used
  have bytes : a.nm = s.nm := natural
  have winner : a.nr 1 = s.nr 1 := id
  let picked := before.reframe (t := a) bytes real rr winner (fun r h => port r (by omega))
  have words : matchingOriginalGrowthEvent a = matchingOriginalGrowthEvent s := by
    simp only [matchingOriginalGrowthEvent, winner, port 54, bytes]
  have aExpand : matchingEventClass a = 2 := by
    simpa only [matchingEventClass,matchingEventIsCut,matchingEventLeftRep,matchingEventRightRep,
      words,port 51,port 55,port 57,bytes] using! expand
  obtain ⟨t,ticks,charge,arm,live,on,prepared,transition,armBound⟩ :=
    picked.expandArm searching symmetric rfl midLive aExpand (ends.trans words.symm)
  have aTag : a.nr 35 = 2 := tag.trans expand
  have armByTag : BlockRuns (match a.nr 35 with
      | 0 => matchingGrowHandlerWithWitnesses
      | 1 => matchingContractionHandlerBlock
      | 2 => matchingExpandHandlerBlock
      | _ => matchingAugmentationHandlerBlock) ticks a t := by
    rw [aTag]
    exact arm
  obtain ⟨dispatchTicks,dispatchBound,dispatched⟩ :=
    dispatchMatchingActionBlock_spec (s := a) (t := t) rfl midLive live zero one two (by omega) armByTag
  have counts : matchingStageCountsFromRAM k a (a.nr 39) = matchingStageCountsFromRAM k s (s.nr 39) := by
    rw [matchingStageCountsFromRAM_eq picked.selected.dual picked.positive _
          picked.selected.registry.trees picked.selected.registry.unique picked.selected.registry.keys,
        matchingStageCountsFromRAM_eq before.selected.dual before.positive _
          before.selected.registry.trees before.selected.registry.unique before.selected.registry.keys,
        port 39]
    rfl
  refine ⟨_,classTicks+dispatchTicks,charge,classify.append dispatched,live,?_,prepared,?_,by omega⟩
  · exact fun off => active ((on.trans (port 33)).symm.trans off)
  · change MatchingStageTransition (matchingStageCountsFromRAM k s (s.nr 39)) charge
      (matchingStageCountsFromRAM k (matchingStageSnapshot t) ((matchingStageSnapshot t).nr 39))
    rw [← counts]
    exact transition


end VehicleRoutingSurvey.Routing
end RppSource_MatchingDispatchExpansion

open VehicleRoutingSurvey.Routing SupplyChainTheory in
theorem solution : (fun {P : Prop} (_ : P) => P) (@VehicleRoutingSurvey.Routing.MatchingDispatchState.expand) :=
  @VehicleRoutingSurvey.Routing.MatchingDispatchState.expand
