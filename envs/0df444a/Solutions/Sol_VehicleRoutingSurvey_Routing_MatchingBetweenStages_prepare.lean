-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.MatchingBetweenStages.prepare
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T16:01:01.079208+00:00
-- url     : https://prove2.me/submissions/179318a3-00b3-4444-8b65-36149fe3c02f

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces

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







@[simp] theorem naturalDestination_relocate (offset : ℕ) (ins : ArithmeticInstruction) :
    naturalDestination (relocateInstruction offset ins) = naturalDestination ins := by
  cases ins <;> rfl

theorem forall_naturalDestination_append (p : ℕ → Prop) (a b : List ArithmeticInstruction) :
    (∀ ins ∈ appendBlock a b, p (naturalDestination ins)) ↔
      (∀ ins ∈ a, p (naturalDestination ins)) ∧ ∀ ins ∈ b, p (naturalDestination ins) := by
  simp only [appendBlock, List.forall_mem_append, List.forall_mem_map, naturalDestination_relocate]

























end VehicleRoutingSurvey.Routing
end RppSource_WeightedReadDeltaRAM

/-! matching/MatchingStageControl.lean -/
section RppSource_MatchingStageControl
namespace VehicleRoutingSurvey.Routing



structure MatchingStageControls (s t : ArithmeticState) : Prop where
  limit : t.nr 31 = 6 * s.nr 55 + 1
  tick : t.nr 32 = 0
  active : t.nr 33 = 1
  one : t.nr 34 = 1
  winner : t.nr 1 = 0
  selectorOne : t.nr 9 = 1
  identifierBase : t.nr 3 = s.nr 58
  slackBase : t.nr 4 = s.nr 59
  rateBase : t.nr 5 = s.nr 60
  count : t.nr 8 = s.nr 61
  cumulativeDelta : t.rr 15 = 0
  natural : t.nm = s.nm
  real : t.rm = s.rm
  fixed : ∀ r, r ∉ [0, 1, 3, 4, 5, 8, 9, 29, 31, 32, 33, 34] → t.nr r = s.nr r

theorem resetMatchingStageControlBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns resetMatchingStageControlBlock 15 s t ∧ t.halted = false ∧ MatchingStageControls s t := by
  let t := (arithmeticStep resetMatchingStageControlBlock)^[15] s
  have ready : t.halted = false := by
    simp [t, resetMatchingStageControlBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = resetMatchingStageControlBlock.length := by
    simp [t, resetMatchingStageControlBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_⟩
  constructor
  case fixed =>
    intro r away
    apply arithmeticRun_keeps_register _ s 15
    simp [resetMatchingStageControlBlock, naturalDestination] at away ⊢
    omega
  all_goals
    simp [t, resetMatchingStageControlBlock, arithmeticStep, entry, running, Function.iterate_succ_apply'] <;> omega






end VehicleRoutingSurvey.Routing
end RppSource_MatchingStageControl

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

/-! matching/WeightedForestDispatch.lean -/
section RppSource_WeightedForestDispatch
namespace VehicleRoutingSurvey.Routing













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









theorem CompactMatchingPartition.dualLabel_block {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (positive : 0 < k) (v : Fin k) :
    part.dualLabel forest positive (part.blocks.block v) = (forest.role (part.representative v)).dualDirection := by
  rw [CompactMatchingPartition.dualLabel, part.representativeOf_block]






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

theorem forall_naturalDestination_branch (p : ℕ → Prop) (x y : ℕ) (left right : List ArithmeticInstruction) :
    (∀ ins ∈ branchOnAtMost x y left right, p (naturalDestination ins)) ↔
      p 0 ∧ (∀ ins ∈ left, p (naturalDestination ins)) ∧ ∀ ins ∈ right, p (naturalDestination ins) := by
  simp only [branchOnAtMost, List.forall_mem_append, List.forall_mem_map, naturalDestination_relocate]
  simp [naturalDestination, and_assoc, and_left_comm, and_comm]

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



theorem refreshSelectedOuterVertex_no_write {r : ℕ}
    (away : r ∉ [0, 6, 10, 11, 16, 17, 18, 19, 25]) :
    ∀ i ∈ refreshSelectedOuterVertex, naturalDestination i ≠ r :=
  naturalDestination_ne_of_list [0, 6, 10, 11, 16, 17, 18, 19, 25] (by decide) away

































end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowCacheRAM

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

/-! matching/MatchingForestReset.lean -/
section RppSource_MatchingForestReset
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing





private def forestResetRoleCode (s : ArithmeticState) : ℕ :=
  let v := s.nr 71
  if s.nm (s.nr 57 + v) = v ∧ s.nr 55 ≤ s.nm (s.nr 50 + v) then 1 else 0

private def matchingForestResetMemory (s : ArithmeticState) : ℕ → ℕ :=
  let v := s.nr 71
  Function.update (Function.update (Function.update s.nm (s.nr 51 + v) (forestResetRoleCode s))
    (s.nr 52 + v) (s.nr 55)) (s.nr 53 + v) 0

private theorem resetMatchingForestCell_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t steps, steps ≤ 16 ∧ BlockRuns resetMatchingForestCell steps s t ∧ t.halted = false ∧
      t.nm = matchingForestResetMemory s ∧ t.rm = s.rm ∧
      ∀ r, r ∉ [0, 12, 13, 14, 15, 17] → t.nr r = s.nr r := by
  let v := s.nr 71
  let rep := s.nm (s.nr 57 + v)
  let mate := s.nm (s.nr 50 + v)
  have build (steps : ℕ) (bound : steps ≤ 16)
      (ready : ((arithmeticStep resetMatchingForestCell)^[steps] s).halted = false)
      (exit : ((arithmeticStep resetMatchingForestCell)^[steps] s).pc = resetMatchingForestCell.length)
      (natural : ((arithmeticStep resetMatchingForestCell)^[steps] s).nm = matchingForestResetMemory s)
      (real : ((arithmeticStep resetMatchingForestCell)^[steps] s).rm = s.rm) :
      ∃ t ticks, ticks ≤ 16 ∧ BlockRuns resetMatchingForestCell ticks s t ∧ t.halted = false ∧
        t.nm = matchingForestResetMemory s ∧ t.rm = s.rm ∧
        ∀ r, r ∉ [0, 12, 13, 14, 15, 17] → t.nr r = s.nr r := by
    refine ⟨_, steps, bound, BlockRuns.of_running_exit rfl ready exit, ready, natural, real, ?_⟩
    intro r safe
    apply arithmeticRun_keeps_register _ s steps
    simp [resetMatchingForestCell, naturalDestination] at safe ⊢
    omega
  rcases lt_trichotomy rep v with below | equal | above
  · apply build 14 (by decide)
    all_goals simp [resetMatchingForestCell, arithmeticStep, entry, running, Function.iterate_succ_apply',
      matchingForestResetMemory, forestResetRoleCode, v, rep, below.le, (not_le.mpr below), below.ne]
  · by_cases free : s.nr 55 ≤ mate
    · apply build 16 le_rfl
      all_goals simp [resetMatchingForestCell, arithmeticStep, entry, running, Function.iterate_succ_apply',
        matchingForestResetMemory, forestResetRoleCode, v, rep, mate, equal, free]
    · apply build 15 (by decide)
      all_goals simp [resetMatchingForestCell, arithmeticStep, entry, running, Function.iterate_succ_apply',
        matchingForestResetMemory, forestResetRoleCode, v, rep, mate, equal, free]
  · apply build 13 (by decide)
    all_goals simp [resetMatchingForestCell, arithmeticStep, entry, running, Function.iterate_succ_apply',
      matchingForestResetMemory, forestResetRoleCode, v, rep, (not_le.mpr above), above.ne']

private structure MatchingForestResetProgress {k : ℕ} (active : Finset (Fin k))
    (mate : Fin k → Option (Fin k)) (original : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 71 = i
  regs : ∀ r, r ∉ [0, 12, 13, 14, 15, 17, 71] → s.nr r = original.nr r
  roles : ∀ v : Fin k, v.val < i → s.nm (original.nr 51 + v.val) =
    if v ∈ active ∧ mate v = none then 1 else 0
  parents : ∀ j < i, s.nm (original.nr 51 + k + j) = k
  depths : ∀ j < i, s.nm (original.nr 51 + k + k + j) = 0
  natural : ∀ a, a < original.nr 51 ∨ original.nr 51 + 3 * k ≤ a → s.nm a = original.nm a
  real : s.rm = original.rm

set_option maxHeartbeats 650000 in
/-- Erase the old forest and give each unmatched top-level representative its own root.
The matching, representatives, metric, and routing memory remain available. -/
theorem resetMatchingForestBlock_correct {k : ℕ} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 34 = 1) (dimension : s.nr 55 = k)
    (parentBase : s.nr 52 = s.nr 51 + k) (depthBase : s.nr 53 = s.nr 51 + k + k)
    (mateBefore : s.nr 50 + k ≤ s.nr 51) (repAfter : s.nr 51 + 3 * k ≤ s.nr 57)
    {active : Finset (Fin k)} {mate : Fin k → Option (Fin k)} {representative : Fin k → Fin k}
    (activeAt : ∀ v, v ∈ active ↔ representative v = v)
    (mates : ∀ v : Fin k, s.nm (s.nr 50 + v.val) = (mate v).elim k Fin.val)
    (reps : ∀ v : Fin k, s.nm (s.nr 57 + v.val) = (representative v).val) :
    ∃ t steps, steps ≤ 19 * k + 2 ∧ BlockRuns resetMatchingForestBlock steps s t ∧ t.halted = false ∧
      AlternatingForestMemory (resetAlternatingForest active mate) (s.nr 51) t.nm ∧
      (∀ r, r ∉ [0, 12, 13, 14, 15, 17, 71] → t.nr r = s.nr r) ∧
      (∀ a, a < s.nr 51 ∨ s.nr 51 + 3 * k ≤ a → t.nm a = s.nm a) ∧ t.rm = s.rm := by
  let inv := MatchingForestResetProgress active mate s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 71 0} := by
    refine ⟨rfl, running, by simp, ?_, by simp, by simp, by simp, fun _ _ => rfl, rfl⟩
    intro r safe
    have different : r ≠ 71 := fun equal => safe (by simp [equal])
    simp [different]
  have iterate (i : ℕ) (hi : i < k) (m : ArithmeticState) (hm : inv i m) :
      ∃ t steps, steps ≤ 16 ∧ BlockRuns resetMatchingForestCell steps m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 71 (t.nr 71 + t.nr 34)} := by
    have fixed (r : ℕ) (safe : r ∉ [0, 12, 13, 14, 15, 17, 71] := by decide) := hm.regs r safe
    let v : Fin k := ⟨i, hi⟩
    have atMate : m.nm (m.nr 50 + i) = (mate v).elim k Fin.val := by
      rw [fixed 50, hm.natural _ (Or.inl (by omega))]
      exact mates v
    have atRep : m.nm (m.nr 57 + i) = (representative v).val := by
      rw [fixed 57, hm.natural _ (Or.inr (by omega))]
      exact reps v
    have root : (representative v).val = i ↔ v ∈ active :=
      ⟨fun equal => (activeAt v).mpr (Fin.ext equal), fun h => congrArg Fin.val ((activeAt v).mp h)⟩
    have role : forestResetRoleCode m = if v ∈ active ∧ mate v = none then 1 else 0 := by
      cases hmMate : mate v with
      | none => simp [forestResetRoleCode, hm.index, atRep, atMate, root, hmMate, fixed 55, dimension]
      | some peer => simp [forestResetRoleCode, hm.index, atRep, atMate, root, hmMate, fixed 55, dimension,
          Nat.not_le.mpr peer.isLt]
    obtain ⟨t, steps, budget, run, live, memory, real, regs⟩ := resetMatchingForestCell_correct hm.entry hm.running
    have naturalMemory : t.nm = Function.update
        (Function.update (Function.update m.nm (s.nr 51 + i) (if v ∈ active ∧ mate v = none then 1 else 0))
          (s.nr 51 + k + i) k) (s.nr 51 + k + k + i) 0 := by
      simpa [matchingForestResetMemory, role, hm.index, fixed 51, fixed 52, fixed 53, fixed 55,
        parentBase, depthBase, dimension] using memory
    refine ⟨t, steps, budget, run, live, ?_⟩
    constructor
    · rfl
    · exact live
    · simp [regs 71 (by decide), regs 34 (by decide), hm.index, fixed 34, one]
    · intro r safe
      have different : r ≠ 71 := fun equal => safe (by simp [equal])
      have untouched : r ∉ [0, 12, 13, 14, 15, 17] := fun h => safe (List.mem_append_left [71] h)
      simpa [different] using (regs r untouched).trans (fixed r safe)
    · intro w hw
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hw) with earlier | current
      · simp (disch := omega) [naturalMemory, Function.update_apply, hm.roles w earlier]
      · have wEq : w = v := Fin.ext current
        subst w
        simp (disch := omega) [naturalMemory, Function.update_apply, v]
    · intro j hj
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with earlier | rfl
      · simp (disch := omega) [naturalMemory, Function.update_apply, hm.parents j earlier]
      · simp (disch := omega) [naturalMemory, Function.update_apply]
    · intro j hj
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with earlier | rfl
      · simp (disch := omega) [naturalMemory, Function.update_apply, hm.depths j earlier]
      · simp [naturalMemory]
    · intro a outside
      simp (disch := omega) [naturalMemory, Function.update_apply, hm.natural a outside]
    · exact real.trans hm.real
  obtain ⟨last, steps, done, cost, run⟩ := countedLoopFromZero_bounded 34 71 55 k 16
    resetMatchingForestCell inv entry running initial
    (fun _ _ h => ⟨h.entry, h.running, h.index, (h.regs 55 (by decide)).trans dimension⟩) iterate
  refine ⟨_, steps, by omega, run, done.running, ?_, done.regs, done.natural, done.real⟩
  intro v
  have role := done.roles v v.isLt
  have parent := done.parents v.val v.isLt
  have depth := done.depths v.val v.isLt
  change last.nm (s.nr 51 + v.val) = _ ∧ last.nm (s.nr 51 + k + v.val) = _ ∧ _
  by_cases root : v ∈ active ∧ mate v = none <;>
    simp [resetAlternatingForest, root, role, parent, depth, relocateState] <;> exact ⟨rfl, rfl⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingForestReset

/-! matching/MatchingClearCandidates.lean -/
section RppSource_MatchingClearCandidates
namespace VehicleRoutingSurvey.Routing





private structure MatchingClearCandidatesInvariant (original : ArithmeticState) (i : ℕ)
    (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 71 = i
  regs : ∀ r, r ≠ 0 → r ≠ 2 → r ≠ 71 → s.nr r = original.nr r
  real : s.rm = original.rm
  slots : ∀ a, s.nm a = if original.nr 58 ≤ a ∧ a < original.nr 58 + i then 0 else original.nm a

theorem clearMatchingCandidatesBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 34 = 1) :
    ∃ t, BlockRuns clearMatchingCandidatesBlock (6 * s.nr 61 + 2) s t ∧ t.halted = false ∧
      (∀ r, r ≠ 0 → r ≠ 2 → r ≠ 71 → t.nr r = s.nr r) ∧ t.rm = s.rm ∧
      ∀ a, t.nm a = if s.nr 58 ≤ a ∧ a < s.nr 58 + s.nr 61 then 0 else s.nm a := by
  let inv := MatchingClearCandidatesInvariant s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 71 0} := by
    refine ⟨rfl, running, by simp, ?_, rfl, ?_⟩
    · intro r _ _ avoid
      simp [avoid]
    · intro a
      simp only [Nat.add_zero, if_neg (show ¬ (s.nr 58 ≤ a ∧ a < s.nr 58) by omega)]
  have iterate (i : ℕ) (_ : i < s.nr 61) (m : ArithmeticState) (hm : inv i m) :
      ∃ t, BlockRuns clearMatchingCandidateCell 3 m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 71 (t.nr 71 + t.nr 34)} := by
    let address := s.nr 58 + i
    let t := {m with
      pc := 3
      nr := Function.update (Function.update m.nr 0 0) 2 address
      nm := Function.update m.nm address 0}
    have table := hm.regs 58 (by decide) (by decide) (by decide)
    have increment := (hm.regs 34 (by decide) (by decide) (by decide)).trans one
    have run : BlockRuns clearMatchingCandidateCell 3 m t := by
      refine BlockRuns.of_running_exit ?_ (show t.halted = false from hm.running) rfl
      simp [t, address, clearMatchingCandidateCell, arithmeticStep, hm.entry, hm.running,
        hm.index, table, Function.iterate_succ_apply']
    refine ⟨t, run, hm.running, rfl, hm.running, by simp [t, hm.index, increment], ?_, hm.real, ?_⟩
    · intro r notAddr notZero notIndex
      simp [t, notAddr, notZero, notIndex, hm.regs r notAddr notZero notIndex]
    · intro a
      change Function.update m.nm address 0 a =
        if s.nr 58 ≤ a ∧ a < s.nr 58 + (i + 1) then 0 else s.nm a
      by_cases changed : a = address
      · rw [changed, Function.update_self, if_pos (by dsimp [address]; omega)]
      · rw [Function.update_of_ne changed, hm.slots]
        have same : (s.nr 58 ≤ a ∧ a < s.nr 58 + i) ↔
            (s.nr 58 ≤ a ∧ a < s.nr 58 + (i + 1)) := by dsimp [address] at changed; omega
        simp only [same]
  obtain ⟨last, done, run⟩ := countedLoopFromZero_correct 34 71 61 (s.nr 61) 3
    clearMatchingCandidateCell inv entry running initial
    (fun _ _ h => ⟨h.entry, h.running, h.index, h.regs 61 (by decide) (by decide) (by decide)⟩) iterate
  have steps : 6 * s.nr 61 + 2 = 1 + (s.nr 61 * (3 + 3) + 1) := by omega
  let final := relocateState 1 {last with pc := (countedLoop 34 71 61 clearMatchingCandidateCell).length}
  refine ⟨final, ?_, done.running, done.regs, done.real, done.slots⟩
  simpa only [clearMatchingCandidatesBlock, steps] using run


end VehicleRoutingSurvey.Routing
end RppSource_MatchingClearCandidates

/-! matching/MatchingPairClear.lean -/
section RppSource_MatchingPairClear
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing



private theorem measureMatchingMatrixBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 34 = 1)
    (offsets : ∀ u < s.nr 55, s.nm (s.nr 21 + u) = s.nr 55 * u) :
    ∃ t steps, steps ≤ 7 ∧ BlockRuns measureMatchingMatrixBlock steps s t ∧ t.halted = false ∧
      t.nr 73 = s.nr 55 * s.nr 55 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      ∀ r, r ∉ [0, 71, 73] → t.nr r = s.nr r := by
  have build (steps : ℕ) (bound : steps ≤ 7)
      (ready : ((arithmeticStep measureMatchingMatrixBlock)^[steps] s).halted = false)
      (exit : ((arithmeticStep measureMatchingMatrixBlock)^[steps] s).pc = measureMatchingMatrixBlock.length)
      (size : ((arithmeticStep measureMatchingMatrixBlock)^[steps] s).nr 73 = s.nr 55 * s.nr 55)
      (natural : ((arithmeticStep measureMatchingMatrixBlock)^[steps] s).nm = s.nm)
      (real : ((arithmeticStep measureMatchingMatrixBlock)^[steps] s).rm = s.rm) :
      ∃ t steps, steps ≤ 7 ∧ BlockRuns measureMatchingMatrixBlock steps s t ∧ t.halted = false ∧
        t.nr 73 = s.nr 55 * s.nr 55 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
        ∀ r, r ∉ [0, 71, 73] → t.nr r = s.nr r := by
    refine ⟨_, steps, bound, BlockRuns.of_running_exit rfl ready exit, ready, size, natural, real, ?_⟩
    intro r safe
    apply arithmeticRun_keeps_register _ s steps
    simp [measureMatchingMatrixBlock, naturalDestination] at safe ⊢
    omega
  by_cases empty : s.nr 55 = 0
  · apply build 3 (by decide)
    all_goals simp [measureMatchingMatrixBlock, arithmeticStep, entry, running, empty,
      Function.iterate_succ_apply']
  · have positive := Nat.pos_of_ne_zero empty
    have index : s.nr 55 - 1 < s.nr 55 := by omega
    have last := offsets _ index
    have square : s.nr 55 * (s.nr 55 - 1) + s.nr 55 = s.nr 55 * s.nr 55 := by
      rw [← Nat.mul_succ, show (s.nr 55 - 1).succ = s.nr 55 by omega]
    apply build 7 le_rfl
    all_goals simp [measureMatchingMatrixBlock, arithmeticStep, entry, running, one, last, square,
      not_le.mpr positive, Function.iterate_succ_apply']







abbrev matchingPairSentinelAddress (base cells address : ℕ) : Prop :=
  base ≤ address ∧ address < base + 2 * cells ∧ (address - base) % 2 = 0

private structure PairClearProgress (original : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 72 = i
  fixed : ∀ r, r ≠ 71 → r ≠ 72 → s.nr r = original.nr r
  real : s.rm = original.rm
  slots : ∀ a, s.nm a = if matchingPairSentinelAddress (original.nr 65) i a
    then original.nr 55 else original.nm a

private theorem clearMatchingPairSlots_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 34 = 1) :
    ∃ t, BlockRuns clearMatchingPairSlots (6 * s.nr 73 + 2) s t ∧ t.halted = false ∧
      (∀ r, r ≠ 71 → r ≠ 72 → t.nr r = s.nr r) ∧ t.rm = s.rm ∧
      ∀ a, t.nm a = if matchingPairSentinelAddress (s.nr 65) (s.nr 73) a then s.nr 55 else s.nm a := by
  let inv := PairClearProgress s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 72 0} := by
    refine ⟨rfl, running, by simp, ?_, rfl, ?_⟩
    · intro r _ avoid
      simp [avoid]
    · intro a
      rw [if_neg]
      unfold matchingPairSentinelAddress
      omega
  have iterate (i : ℕ) (_ : i < s.nr 73) (m : ArithmeticState) (hm : inv i m) :
      ∃ t, BlockRuns clearMatchingPairSlot 3 m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 72 (t.nr 72 + t.nr 34)} := by
    let address := s.nr 65 + 2 * i
    let t := {m with
      pc := 3
      nr := Function.update m.nr 71 address
      nm := Function.update m.nm address (s.nr 55)}
    have table := hm.fixed 65 (by decide) (by decide)
    have k := hm.fixed 55 (by decide) (by decide)
    have step := (hm.fixed 34 (by decide) (by decide)).trans one
    have executed : BlockRuns clearMatchingPairSlot 3 m t := by
      refine BlockRuns.of_running_exit ?_ (show t.halted = false from hm.running) rfl
      simp [t, address, clearMatchingPairSlot, arithmeticStep, hm.entry, hm.running, hm.index, table, k,
        Nat.two_mul, Function.iterate_succ_apply', Function.update_idem]
    refine ⟨t, executed, hm.running, rfl, hm.running, by simp [t, hm.index, step], ?_, hm.real, ?_⟩
    · intro r notAddr notIndex
      simp [t, notAddr, notIndex, hm.fixed r notAddr notIndex]
    · intro a
      change Function.update m.nm address (s.nr 55) a =
        if matchingPairSentinelAddress (s.nr 65) (i + 1) a then s.nr 55 else s.nm a
      by_cases target : a = address
      · rw [target, Function.update_self, if_pos]
        unfold matchingPairSentinelAddress
        dsimp [address]
        omega
      · have same : matchingPairSentinelAddress (s.nr 65) i a ↔
            matchingPairSentinelAddress (s.nr 65) (i + 1) a := by
          unfold matchingPairSentinelAddress
          dsimp [address] at target
          omega
        simp only [Function.update_of_ne target, hm.slots, same]
  obtain ⟨last, done, ran⟩ := countedLoopFromZero_correct 34 72 73 (s.nr 73) 3 clearMatchingPairSlot
    inv entry running initial
    (fun _ _ h => ⟨h.entry, h.running, h.index, h.fixed 73 (by decide) (by decide)⟩) iterate
  let t := relocateState 1 {last with pc := (countedLoop 34 72 73 clearMatchingPairSlot).length}
  have steps : 6 * s.nr 73 + 2 = 1 + (s.nr 73 * (3 + 3) + 1) := by omega
  exact ⟨t, steps.symm ▸ ran, done.running, done.fixed, done.real, done.slots⟩

/-- Invalidate all pair buckets before rebuilding the cache for a new search. The pass costs
at most six instructions per bucket plus a fixed setup and leaves the prior arrays intact. -/
theorem clearMatchingPairCacheBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 34 = 1)
    (offsets : ∀ u < s.nr 55, s.nm (s.nr 21 + u) = s.nr 55 * u) :
    ∃ t steps, steps ≤ 6 * (s.nr 55 * s.nr 55) + 9 ∧
      BlockRuns clearMatchingPairCacheBlock steps s t ∧ t.halted = false ∧
      (∀ r, r ∉ [0, 71, 72, 73] → t.nr r = s.nr r) ∧ t.rm = s.rm ∧
      ∀ a, t.nm a = if matchingPairSentinelAddress (s.nr 65) (s.nr 55 * s.nr 55) a
        then s.nr 55 else s.nm a := by
  obtain ⟨a, front, budget, measured, live, size, natural, real, fixed⟩ :=
    measureMatchingMatrixBlock_correct entry running one offsets
  let ready := {a with pc := 0}
  obtain ⟨b, cleared, done, keeps, bReal, cells⟩ := clearMatchingPairSlots_correct (s := ready) rfl live
    ((fixed 34 (by decide)).trans one)
  refine ⟨_, front + (6 * ready.nr 73 + 2), ?_, measured.append cleared, done, ?_, bReal.trans real, ?_⟩
  · have size' : ready.nr 73 = s.nr 55 * s.nr 55 := size
    rw [size']
    omega
  · intro r safe
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at safe
    obtain ⟨h0, h71, h72, h73⟩ := safe
    exact (keeps r h71 h72).trans (fixed r (by simp [h0, h71, h73]))
  · intro address
    simpa only [relocateState, ready, size, fixed 65 (by decide), fixed 55 (by decide), natural] using cells address


end VehicleRoutingSurvey.Routing
end RppSource_MatchingPairClear

/-! matching/MatchingWarmSeed.lean -/
section RppSource_MatchingWarmSeed
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096

namespace VehicleRoutingSurvey.Routing













theorem refreshWarmCacheSource_fixed {s t : ArithmeticState} {steps : ℕ}
    (run : BlockRuns refreshWarmCacheSource steps s t) (r : ℕ)
    (fixed : r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 25, 26]) : t.nr r = s.nr r := by
  rw [← run.run]
  apply arithmeticRun_keeps_register _ s steps
  have away : r ∉ [0, 6, 10, 11, 16, 17, 18, 19, 25] := by
    simp at fixed ⊢
    omega
  apply (forall_naturalDestination_append (· ≠ r) _ _).2
  constructor
  · apply naturalDestination_ne_of_list [6, 15, 19, 26] (by decide)
    simp at fixed ⊢
    omega
  · apply (forall_naturalDestination_branch (· ≠ r) _ _ _ _).2
    exact ⟨fun equal => fixed (by simp [← equal]), by simp, refreshSelectedOuterVertex_no_write away⟩

private theorem refreshWarmCacheSource_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (dictAfter : s.nr 58 ≤ s.nr 54) (pairAfter : s.nr 58 ≤ s.nr 65)
    (rateAfter : s.nr 59 ≤ s.nr 60) (keyAfter : s.nr 59 ≤ s.nr 66) :
    ∃ t steps, steps ≤ 98 * s.nr 55 + 8 ∧ BlockRuns refreshWarmCacheSource steps s t ∧
      t.halted = false ∧ (∀ a < s.nr 58, t.nm a = s.nm a) ∧ ∀ a < s.nr 59, t.rm a = s.rm a := by
  let u := s.nr 24 + s.nr 14
  let rep := s.nm (s.nr 57 + u)
  let p := (arithmeticStep readWarmCacheSource)^[5] s
  have live : p.halted = false := by
    simp [p, readWarmCacheSource, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : p.pc = readWarmCacheSource.length := by
    simp [p, readWarmCacheSource, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have read : BlockRuns readWarmCacheSource 5 s p := BlockRuns.of_running_exit rfl live exit
  let ready := {p with pc := 0}
  have unchanged : ready.nm = s.nm := by
    simp [ready, p, readWarmCacheSource, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have real : ready.rm = s.rm := by
    simp [ready, p, readWarmCacheSource, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have fixed (r : ℕ) (safe : r ∉ [0, 6, 15, 19, 26] := by decide) : ready.nr r = s.nr r := by
    change p.nr r = s.nr r
    apply arithmeticRun_keeps_register _ s 5
    simp [readWarmCacheSource, naturalDestination] at safe ⊢
    omega
  by_cases dormant : ready.nr 19 ≤ ready.nr 14
  · have empty : BlockRuns [] 0 ready ready :=
      ⟨fun i h => (Nat.not_lt_zero i h).elim, by simp, rfl⟩
    have finished := branchOnAtMost_left 19 14 [] refreshSelectedOuterVertex
      (s := ready) rfl live dormant empty live
    exact ⟨_, 5 + (1 + 0 + 1), by omega, read.append finished, live,
      fun addr _ => congrFun unchanged addr, fun addr _ => congrFun real addr⟩
  · obtain ⟨q, ticks, budget, scan, qLive, holds, keptReal⟩ := refreshSelectedOuterVertex_spec ready rfl live
      ((fixed 9).trans one) (by rw [fixed 58, fixed 54]; exact dictAfter)
      (by rw [fixed 58, fixed 65]; exact pairAfter)
    have finished := branchOnAtMost_right 19 14 [] refreshSelectedOuterVertex (s := ready) rfl live
      (lt_of_not_ge dormant) scan qLive
    rw [fixed 55] at budget
    have upper : ticks ≤ 98 * s.nr 55 + 2 := by simpa [Nat.mul_comm 98] using budget
    refine ⟨_, 5 + (1 + ticks), by omega, read.append finished, qLive, ?_, ?_⟩
    · intro addr before
      exact (holds addr ((fixed 58).symm ▸ before)).trans (congrFun unchanged addr)
    · intro addr before
      exact (keptReal addr ((fixed 59).symm ▸ before)
        (by rw [fixed 59, fixed 60]; exact rateAfter)
        (by rw [fixed 59, fixed 66]; exact keyAfter)).trans (congrFun real addr)

private structure WarmMatchingCacheProgress (original : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 24 = i
  regs : ∀ r, r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 26] → s.nr r = original.nr r
  natural : ∀ addr < original.nr 58, s.nm addr = original.nm addr
  real : ∀ addr < original.nr 59, s.rm addr = original.rm addr

private theorem sweepWarmMatchingCache_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (dictAfter : s.nr 58 ≤ s.nr 54) (pairAfter : s.nr 58 ≤ s.nr 65)
    (rateAfter : s.nr 59 ≤ s.nr 60) (keyAfter : s.nr 59 ≤ s.nr 66) :
    ∃ t steps, steps ≤ s.nr 55 * (98 * s.nr 55 + 11) + 2 ∧
      BlockRuns sweepWarmMatchingCache steps s t ∧ t.halted = false ∧
      (∀ r, r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 26] → t.nr r = s.nr r) ∧
      (∀ a < s.nr 58, t.nm a = s.nm a) ∧ ∀ a < s.nr 59, t.rm a = s.rm a := by
  let k := s.nr 55
  let inv := WarmMatchingCacheProgress s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 24 0} := by
    refine ⟨rfl, running, by simp, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    intro r safe
    have notIndex : r ≠ 24 := fun equal => safe (by simp [equal])
    simp [notIndex]
  have iterate (i : ℕ) (_ : i < k) (m : ArithmeticState) (hm : inv i m) :
      ∃ t steps, steps ≤ 98 * k + 8 ∧ BlockRuns refreshWarmCacheSource steps m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)} := by
    have preserved (r : ℕ) (safe : r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 26] := by decide) :=
      hm.regs r safe
    have oneAt : m.nr 9 = 1 := (preserved 9).trans one
    obtain ⟨t, steps, budget, run, live, natural, real⟩ := refreshWarmCacheSource_correct hm.entry hm.running oneAt
      (by rw [preserved 58, preserved 54]; exact dictAfter)
      (by rw [preserved 58, preserved 65]; exact pairAfter)
      (by rw [preserved 59, preserved 60]; exact rateAfter)
      (by rw [preserved 59, preserved 66]; exact keyAfter)
    have fixed := refreshWarmCacheSource_fixed run
    rw [preserved 55] at budget
    refine ⟨t, steps, budget, run, live, rfl, live, ?_, ?_, ?_, ?_⟩
    · simp [fixed 24 (by decide), hm.index, fixed 9 (by decide), oneAt]
    · intro r safe
      have notIndex : r ≠ 24 := fun equal => safe (by simp [equal])
      have before : r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 25, 26] := by simp at safe ⊢; omega
      simpa [notIndex] using (fixed r before).trans (preserved r safe)
    · intro addr before
      exact (natural addr ((preserved 58).symm ▸ before)).trans (hm.natural addr before)
    · intro addr before
      exact (real addr ((preserved 59).symm ▸ before)).trans (hm.real addr before)
  obtain ⟨last, steps, checked, budget, ran⟩ := countedLoopFromZero_bounded 9 24 55 k (98 * k + 8)
    refreshWarmCacheSource inv entry running initial
    (fun _ _ h => ⟨h.entry, h.running, h.index, h.regs 55 (by decide)⟩) iterate
  refine ⟨_, steps, ?_, ran, checked.running, checked.regs, checked.natural, checked.real⟩
  change steps ≤ 1 + (k * (98 * k + 8 + 3) + 1) at budget
  change steps ≤ k * (98 * k + 11) + 2
  rw [show 98 * k + 8 + 3 = 98 * k + 11 by omega] at budget
  omega

theorem rebuildMatchingActiveCacheBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (dictAfter : s.nr 58 ≤ s.nr 54) (pairAfter : s.nr 58 ≤ s.nr 65)
    (rateAfter : s.nr 59 ≤ s.nr 60) (keyAfter : s.nr 59 ≤ s.nr 66) :
    ∃ t steps, steps ≤ s.nr 55 * (98 * s.nr 55 + 11) + 3 ∧
      BlockRuns rebuildMatchingActiveCacheBlock steps s t ∧ t.halted = false ∧
      (∀ r, r ∉ [0, 6, 10, 11, 14, 15, 16, 17, 18, 19, 24, 25, 26] → t.nr r = s.nr r) ∧
      (∀ a < s.nr 58, t.nm a = s.nm a) ∧ ∀ a < s.nr 59, t.rm a = s.rm a := by
  let after := {s with pc := 0, nr := Function.update s.nr 14 0}
  obtain ⟨t, steps, bound, sweep, live, kept, natural, real⟩ := sweepWarmMatchingCache_correct (s := after) rfl running
    (by simpa [after] using one) (by simpa [after] using dictAfter) (by simpa [after] using pairAfter)
    (by simpa [after] using rateAfter) (by simpa [after] using keyAfter)
  refine ⟨_, 1 + steps, ?_, (zeroRegister_runs 14 s entry running).append sweep, live, ?_, ?_, ?_⟩
  · simp [after] at bound
    omega
  · intro r safe
    change t.nr r = s.nr r
    have notZero : r ≠ 14 := fun equal => safe (by simp [equal])
    have unaffected : r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 26] := by simp at safe ⊢; omega
    simpa [after, notZero] using kept r unaffected
  · change ∀ a < s.nr 58, t.nm a = s.nm a
    simpa [after] using natural
  · change ∀ a < s.nr 59, t.rm a = s.rm a
    simpa [after] using real


end VehicleRoutingSurvey.Routing
end RppSource_MatchingWarmSeed

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

/-! matching/MatchingWarmPreparation.lean -/
section RppSource_MatchingWarmPreparation
namespace VehicleRoutingSurvey.Routing



/-- Exact forest and cleared cache at the start of the warm scan. -/
structure MatchingWarmCleared {k : ℕ} (s t : ArithmeticState) (active : Finset (Fin k))
    (mate : Fin k → Option (Fin k)) : Prop where
  controls : t.nr 31 = 6*k+1 ∧ t.nr 32 = 0 ∧ t.nr 33 = 1 ∧ t.nr 34 = 1 ∧
    t.nr 1 = 0 ∧ t.nr 9 = 1 ∧ t.nr 8 = 3*k ∧ t.nr 3 = s.nr 58 ∧
    t.nr 4 = s.nr 59 ∧ t.nr 5 = s.nr 60
  fixed : ∀ r, r ∉ [0, 1, 2, 3, 4, 5, 8, 9, 12, 13, 14, 15, 17, 29, 31, 32, 33, 34, 71, 72, 73] →
    t.nr r = s.nr r
  forest : AlternatingForestMemory (resetAlternatingForest active mate) (s.nr 51) t.nm
  zeroClock : t.rr 15 = 0
  real : t.rm = s.rm
  natural : ∀ a, (a < s.nr 51 ∨ s.nr 51 + 3*k ≤ a) →
    ¬ (s.nr 58 ≤ a ∧ a < s.nr 58 + s.nr 61) →
    ¬ matchingPairSentinelAddress (s.nr 65) (k*k) a → t.nm a = s.nm a
  emptyId : s.nr 58 + s.nr 61 ≤ s.nr 65 → ∀ i < s.nr 61, t.nm (s.nr 58 + i) = 0
  emptyPair : ∀ i < k*k, t.nm (s.nr 65 + (i+i)) = k

set_option maxHeartbeats 700000 in
/-- Run stage controls, reset forest labels, and invalidate all candidate rows and pair buckets. -/
theorem warmMatchingPreparationPrefixBlock_runs {k : ℕ} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (layout : MatchingWarmLayout s k)
    (offsets : ∀ i < k, s.nm (s.nr 21 + i) = k * i)
    {active : Finset (Fin k)} {mate : Fin k → Option (Fin k)} {representative : Fin k → Fin k}
    (activeAt : ∀ v, v ∈ active ↔ representative v = v)
    (mates : ∀ v : Fin k, s.nm (s.nr 50 + v.val) = (mate v).elim k Fin.val)
    (reps : ∀ v : Fin k, s.nm (s.nr 57 + v.val) = (representative v).val) :
    ∃ t steps, steps ≤ 6*(k*k) + 37*k + 28 ∧
      BlockRuns warmMatchingPreparationPrefixBlock steps s t ∧ t.halted = false ∧
      MatchingWarmCleared s t active mate := by
  obtain ⟨a, setup, aLive, aFrame⟩ := resetMatchingStageControlBlock_correct entry running
  let aInput := {a with pc := 0}
  have aReg (r : ℕ) (safe : r ∉ [0, 1, 3, 4, 5, 8, 9, 29, 31, 32, 33, 34] := by decide) :
      aInput.nr r = s.nr r := aFrame.fixed r safe
  obtain ⟨b, resetSteps, resetBudget, reset, bLive, forest, bFixed, bNat, bReal⟩ :=
    resetMatchingForestBlock_correct (s := aInput) rfl aLive aFrame.one ((aReg 55).trans layout.size)
      (by rw [aReg 52, aReg 51]; exact layout.parents)
      (by rw [aReg 53, aReg 51]; exact layout.depths)
      (by rw [aReg 50, aReg 51]; exact layout.matesBefore)
      (by rw [aReg 51, aReg 57]; exact layout.representativesAfter) activeAt
      (fun v => by change a.nm _ = _; rw [aReg 50, aFrame.natural]; exact mates v)
      (fun v => by change a.nm _ = _; rw [aReg 57, aFrame.natural]; exact reps v)
  let preForest := appendBlock resetMatchingStageControlBlock resetMatchingForestBlock
  let bInput := {relocateState resetMatchingStageControlBlock.length b with pc := 0}
  have bReg (r : ℕ) (safe : r ∉ [0, 12, 13, 14, 15, 17, 71] := by decide) : bInput.nr r = aInput.nr r :=
    bFixed r safe
  have keptMates (address : ℕ) (low : address < s.nr 50 + k) : bInput.nm address = s.nm address := by
    have earlier : address < aInput.nr 51 := by rw [aReg 51]; have := layout.matesBefore; omega
    exact (bNat address (Or.inl earlier)).trans (congrFun aFrame.natural address)
  obtain ⟨c, cleared, cLive, cFixed, cReal, cMemory⟩ := clearMatchingCandidatesBlock_correct
    (s := bInput) rfl bLive ((bReg 34).trans aFrame.one)
  let prePair := appendBlock preForest clearMatchingCandidatesBlock
  let cInput := {relocateState preForest.length c with pc := 0}
  have cReg (r : ℕ) (h0 : r ≠ 0 := by decide) (h2 : r ≠ 2 := by decide) (h71 : r ≠ 71 := by decide) :
      cInput.nr r = bInput.nr r := cFixed r h0 h2 h71
  have idsBase : bInput.nr 58 = s.nr 58 := (bReg 58).trans (aReg 58)
  have idsEnd : s.nr 51 + 3 * k ≤ s.nr 58 := layout.representativesAfter.trans
    (Nat.le_trans (Nat.le_add_right _ _) layout.candidatesAfter)
  have cNatural (address : ℕ) (earlier : address < s.nr 58) : cInput.nm address = bInput.nm address := by
    change c.nm address = _
    rw [cMemory, idsBase, if_neg (fun h => (not_le.mpr earlier) h.1)]
  have cSize : cInput.nr 55 = k := (cReg 55).trans ((bReg 55).trans ((aReg 55).trans layout.size))
  have cRows (i : ℕ) (hi : i < cInput.nr 55) : cInput.nm (cInput.nr 21 + i) = cInput.nr 55 * i := by
    rw [cSize] at hi
    rw [cReg 21, bReg 21, aReg 21, cSize, cNatural _ (by
      have := layout.offsetsBefore
      have := layout.matesBefore
      omega), keptMates _ (by have := layout.offsetsBefore; omega)]
    exact offsets i hi
  have cOne : cInput.nr 34 = 1 := (cReg 34).trans ((bReg 34).trans aFrame.one)
  obtain ⟨d, pairSteps, pairBudget, pair, dLive, dFixed, dReal, dMemory⟩ :=
    clearMatchingPairCacheBlock_correct (s := cInput) rfl cLive cOne cRows
  let dInput := {relocateState prePair.length d with pc := 0}
  have dReg (r : ℕ) (safe : r ∉ [0, 71, 72, 73] := by decide) : dInput.nr r = cInput.nr r := dFixed r safe
  have dNatural (address : ℕ) (earlier : address < s.nr 58) : dInput.nm address = cInput.nm address := by
    change d.nm address = _
    have pairBase : cInput.nr 65 = s.nr 65 := (cReg 65).trans ((bReg 65).trans (aReg 65))
    rw [dMemory, if_neg (fun h => (not_le.mpr (earlier.trans_le layout.pairsAfter)) (pairBase ▸ h.1))]
  have dOne : dInput.nr 9 = 1 := (dReg 9).trans ((cReg 9).trans ((bReg 9).trans aFrame.selectorOne))
  have dFromA (r : ℕ) (sd : r ∉ [0, 71, 72, 73] := by decide) (h0 : r ≠ 0 := by decide)
      (h2 : r ≠ 2 := by decide) (h71 : r ≠ 71 := by decide)
      (sb : r ∉ [0, 12, 13, 14, 15, 17, 71] := by decide) : dInput.nr r = aInput.nr r :=
    (dReg r sd).trans ((cReg r h0 h2 h71).trans (bReg r sb))
  have aPair := (cReg 65).trans ((bReg 65).trans (aReg 65))
  have pairs (addr : ℕ) : dInput.nm addr = if matchingPairSentinelAddress (s.nr 65) (k*k) addr
      then k else cInput.nm addr := by
    change d.nm addr = _
    rw [dMemory, aPair, cSize]
  have clearedIds (addr : ℕ) : cInput.nm addr =
      if s.nr 58 ≤ addr ∧ addr < s.nr 58 + s.nr 61 then 0 else bInput.nm addr := by
    change c.nm addr = _
    rw [cMemory, idsBase, bReg 61, aReg 61]
  have prefixRun : BlockRuns warmMatchingPreparationPrefixBlock
      (15 + resetSteps + (6*bInput.nr 61+2) + pairSteps) s (relocateState prePair.length d) :=
    ((setup.append reset).append cleared).append pair
  have rowCount : bInput.nr 61 = 3*k := (bReg 61).trans ((aReg 61).trans layout.candidates)
  rw [cSize] at pairBudget
  refine ⟨_, _, ?_, prefixRun, dLive, ?_⟩
  · rw [rowCount]
    omega
  · constructor
    · exact ⟨(dFromA 31).trans (layout.size ▸ aFrame.limit), (dFromA 32).trans aFrame.tick,
        (dFromA 33).trans aFrame.active, (dFromA 34).trans aFrame.one, (dFromA 1).trans aFrame.winner,
        dOne, (dFromA 8).trans (aFrame.count.trans layout.candidates),
        (dFromA 3).trans aFrame.identifierBase, (dFromA 4).trans aFrame.slackBase,
        (dFromA 5).trans aFrame.rateBase⟩
    · intro r safe
      exact (dFromA r (by simp at safe ⊢; omega) (by simp at safe; omega) (by simp at safe; omega)
        (by simp at safe; omega) (by simp at safe ⊢; omega)).trans (aReg r (by simp at safe ⊢; omega))
    · intro v
      have ordinary (addr : ℕ) (low : addr < s.nr 58) : dInput.nm addr = bInput.nm addr :=
        (dNatural addr low).trans (cNatural addr low)
      obtain ⟨role, parent, depth⟩ := forest v
      rw [aReg 51] at role parent depth
      have inside := v.isLt
      exact ⟨(ordinary _ (by omega)).trans role, (ordinary _ (by omega)).trans parent,
        (ordinary _ (by omega)).trans depth⟩
    · have bTime := reset.keeps_cache_real (r := 15) (by decide)
      have cTime := cleared.keeps_cache_real (r := 15) (by decide)
      have dTime := pair.keeps_cache_real (r := 15) (by decide)
      exact dTime.trans (cTime.trans (bTime.trans aFrame.cumulativeDelta))
    · exact dReal.trans (cReal.trans (bReal.trans aFrame.real))
    · intro addr forestAway idAway pairAway
      change dInput.nm addr = _
      have safe : addr < aInput.nr 51 ∨ aInput.nr 51 + 3*k ≤ addr := by rwa [aReg 51]
      rw [pairs, if_neg pairAway, clearedIds, if_neg idAway]
      exact (bNat addr safe).trans (congrFun aFrame.natural addr)
    · intro separated i hi
      change dInput.nm (s.nr 58 + i) = 0
      have outside : ¬ matchingPairSentinelAddress (s.nr 65) (k*k) (s.nr 58 + i) :=
        fun h => by have lo := h.1; omega
      rw [pairs, if_neg outside, clearedIds, if_pos (by omega)]
    · intro i hi
      change dInput.nm _ = _
      have here : matchingPairSentinelAddress (s.nr 65) (k*k) (s.nr 65 + (i+i)) :=
        ⟨by omega, by omega, by omega⟩
      rw [pairs, if_pos here]

set_option maxHeartbeats 700000 in
/-- Execute the warm start with a quadratic instruction bound and an exact forest reset.
The persistent pointers, mate table, and routing input prefixes remain in place. -/
theorem warmMatchingPreparationBlock_runs {k : ℕ} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (layout : MatchingWarmLayout s k)
    (offsets : ∀ i < k, s.nm (s.nr 21 + i) = k * i)
    {active : Finset (Fin k)} {mate : Fin k → Option (Fin k)} {representative : Fin k → Fin k}
    (activeAt : ∀ v, v ∈ active ↔ representative v = v)
    (mates : ∀ v : Fin k, s.nm (s.nr 50 + v.val) = (mate v).elim k Fin.val)
    (reps : ∀ v : Fin k, s.nm (s.nr 57 + v.val) = (representative v).val) :
    ∃ t steps, steps ≤ 104 * k * k + 48 * k + 31 ∧
      BlockRuns warmMatchingPreparationBlock steps s t ∧ t.halted = false ∧
      MatchingWarmLayout t k ∧
      t.nr 31 = 6 * k + 1 ∧ t.nr 32 = 0 ∧ t.nr 33 = 1 ∧ t.nr 34 = 1 ∧
      t.nr 1 = 0 ∧ t.nr 9 = 1 ∧ t.nr 8 = 3 * k ∧
      t.nr 3 = t.nr 58 ∧ t.nr 4 = t.nr 59 ∧ t.nr 5 = t.nr 60 ∧
      AlternatingForestMemory (resetAlternatingForest active mate) (s.nr 51) t.nm ∧
      (∀ a < s.nr 50 + k, t.nm a = s.nm a) ∧
      (∀ a < s.nr 59, t.rm a = s.rm a) ∧
      ∀ r, 50 ≤ r → (r < 71 ∨ 73 < r) → t.nr r = s.nr r := by
  obtain ⟨d, preTicks, preBudget, pre, dLive, ready⟩ :=
    warmMatchingPreparationPrefixBlock_runs entry running layout offsets activeAt mates reps
  let start := {d with pc := 0}
  have before (r : ℕ) (safe : r ∉ [0, 1, 2, 3, 4, 5, 8, 9, 12, 13, 14, 15, 17, 29, 31, 32, 33, 34, 71, 72, 73] := by decide) :
      start.nr r = s.nr r := ready.fixed r safe
  obtain ⟨l, clock, activePort, unit, winner, one, count, id, slack, rate⟩ := ready.controls
  obtain ⟨e, scanSteps, scanBudget, scan, eLive, eFixed, eNat, eReal⟩ :=
    rebuildMatchingActiveCacheBlock_correct (s := start) rfl dLive one
      (by rw [before 58, before 54]; exact layout.dictionaryAfter)
      (by rw [before 58, before 65]; exact layout.pairsAfter)
      (by rw [before 59, before 60]; exact layout.ratesAfter)
      (by rw [before 59, before 66]; exact layout.keysAfter)
  let t := relocateState warmMatchingPreparationPrefixBlock.length e
  have after (r : ℕ) (safe : r ∉ [0, 6, 10, 11, 14, 15, 16, 17, 18, 19, 24, 25, 26] := by decide) :
      t.nr r = start.nr r := eFixed r safe
  have keep (r : ℕ)
      (sa : r ∉ [0, 6, 10, 11, 14, 15, 16, 17, 18, 19, 24, 25, 26] := by decide)
      (sb : r ∉ [0, 1, 2, 3, 4, 5, 8, 9, 12, 13, 14, 15, 17, 29, 31, 32, 33, 34, 71, 72, 73] := by decide) :
      t.nr r = s.nr r := (after r sa).trans (before r sb)
  have natural (addr : ℕ) (low : addr < s.nr 58) : t.nm addr = d.nm addr :=
    eNat addr ((before 58).symm ▸ low)
  have forestEnd : s.nr 51 + 3*k ≤ s.nr 58 := by
    have a := layout.representativesAfter
    have b := layout.candidatesAfter
    omega
  rw [before 55, layout.size] at scanBudget
  refine ⟨t, preTicks + scanSteps, ?_, pre.append scan, eLive, ?_, ?_⟩
  · calc
      _ ≤ (6*(k*k) + 37*k + 28) + (k*(98*k+11)+3) := Nat.add_le_add preBudget scanBudget
      _ = _ := by ring
  · exact ⟨(keep 55).trans layout.size, (keep 61).trans layout.candidates,
      by rw [keep 52, keep 51]; exact layout.parents, by rw [keep 53, keep 51]; exact layout.depths,
      by rw [keep 50, keep 51]; exact layout.matesBefore, by rw [keep 51, keep 57]; exact layout.representativesAfter,
      by rw [keep 57, keep 58]; exact layout.candidatesAfter, by rw [keep 58, keep 54]; exact layout.dictionaryAfter,
      by rw [keep 58, keep 65]; exact layout.pairsAfter, by rw [keep 59, keep 60]; exact layout.ratesAfter,
      by rw [keep 59, keep 66]; exact layout.keysAfter, by rw [keep 21, keep 50]; exact layout.offsetsBefore⟩
  · refine ⟨(after 31).trans l, (after 32).trans clock, (after 33).trans activePort, (after 34).trans unit,
      (after 1).trans winner, (after 9).trans one, (after 8).trans count, (after 3).trans (id.trans (keep 58).symm),
      (after 4).trans (slack.trans (keep 59).symm), (after 5).trans (rate.trans (keep 60).symm), ?_, ?_, ?_, ?_⟩
    · intro v
      have inside := v.isLt
      obtain ⟨role, parent, depth⟩ := ready.forest v
      exact ⟨(natural _ (by omega)).trans role, (natural _ (by omega)).trans parent, (natural _ (by omega)).trans depth⟩
    · intro addr early
      have forestBefore : addr < s.nr 51 := by have h := layout.matesBefore; omega
      have cacheBefore : addr < s.nr 58 := by omega
      exact (natural addr cacheBefore).trans (ready.natural addr (Or.inl forestBefore)
        (fun h => (not_le.mpr cacheBefore) h.1)
        (fun h => (not_le.mpr (cacheBefore.trans_le layout.pairsAfter)) h.1))
    · intro addr early
      exact (eReal addr ((before 59).symm ▸ early)).trans (congrFun ready.real addr)
    · intro r high safe
      exact keep r (by simp; omega) (by simp; omega)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingWarmPreparation

/-! matching/MatchingWarmPrimal.lean -/
section RppSource_MatchingWarmPrimal
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory





theorem CompactMatchingPrimalDualMemory.partialMate_word {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {original s : ArithmeticState}
    (before : CompactMatchingPrimalDualMemory state original s) (v : Fin k) :
    s.nm (s.nr 50 + v.val) = (state.partialMate v).elim k Fin.val := by
  by_cases h : v ∈ state.covered <;> simp [before.mate, CompactMatchingPrimalDual.partialMate, h]





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

/-! matching/BlossomCreditBounds.lean -/
section RppSource_BlossomCreditBounds
namespace VehicleRoutingSurvey.Routing

variable {α : Type*} [DecidableEq α]

private theorem laminarCard_le_of_fuel (fuel : ℕ) (vertices : Finset α)
    (family : Finset (Finset α)) (within : vertices.card < fuel)
    (contained : ∀ A ∈ family, A ⊆ vertices) (nontrivial : ∀ A ∈ family, 1 < A.card)
    (laminar : ∀ A ∈ family, ∀ B ∈ family, Disjoint A B ∨ A ⊆ B ∨ B ⊆ A) :
    family.card ≤ vertices.card := by
  induction fuel generalizing vertices family with
  | zero => omega
  | succ fuel ih =>
    by_cases present : family.Nonempty
    · obtain ⟨A, inFamily, least⟩ := Finset.exists_min_image family Finset.card present
      obtain ⟨x, xIn, y, yIn, distinct⟩ := Finset.one_lt_card.mp (nontrivial A inFamily)
      let other := family.erase A
      let reduced := other.image (fun B => B.erase x)
      have classifies (B : Finset α) (hB : B ∈ other) : Disjoint A B ∨ A ⊂ B := by
        obtain ⟨different, member⟩ := Finset.mem_erase.mp hB
        rcases laminar A inFamily B member with apart | larger | smaller
        · exact Or.inl apart
        · exact Or.inr (Finset.ssubset_iff_subset_ne.mpr ⟨larger, different.symm⟩)
        · exact (different (Finset.eq_of_subset_of_card_le smaller (least B member))).elim
      have sameIn (B : Finset α) (hB : B ∈ other) : x ∈ B ↔ y ∈ B := by
        rcases classifies B hB with apart | larger
        · have notX := Finset.disjoint_left.mp apart xIn
          have notY := Finset.disjoint_left.mp apart yIn
          simp [notX, notY]
        · have includes := (Finset.ssubset_iff_subset_ne.mp larger).1
          simp [includes xIn, includes yIn]
      have injective : Set.InjOn (fun B : Finset α => B.erase x) other := by
        intro B hB C hC equal
        change B.erase x = C.erase x at equal
        have sameMem (v : α) (different : v ≠ x) : v ∈ B ↔ v ∈ C := by
          constructor
          · intro member
            have erased : v ∈ B.erase x := Finset.mem_erase.mpr ⟨different, member⟩
            exact Finset.mem_of_mem_erase (equal ▸ erased)
          · intro member
            have erased : v ∈ C.erase x := Finset.mem_erase.mpr ⟨different, member⟩
            exact Finset.mem_of_mem_erase (equal.symm ▸ erased)
        ext v
        by_cases atX : v = x
        · subst v
          rw [sameIn B hB, sameIn C hC]
          exact sameMem y distinct.symm
        · exact sameMem v atX
      have smallerSets (B : Finset α) (hB : B ∈ reduced) : B ⊆ vertices.erase x := by
        obtain ⟨old, oldMem, rfl⟩ := Finset.mem_image.mp hB
        exact Finset.erase_subset_erase x (contained old (Finset.mem_of_mem_erase oldMem))
      have stillNontrivial (B : Finset α) (hB : B ∈ reduced) : 1 < B.card := by
        obtain ⟨old, oldMem, rfl⟩ := Finset.mem_image.mp hB
        rcases classifies old oldMem with apart | larger
        · rw [Finset.erase_eq_of_notMem (Finset.disjoint_left.mp apart xIn)]
          exact nontrivial old (Finset.mem_of_mem_erase oldMem)
        · have xInOld := (Finset.ssubset_iff_subset_ne.mp larger).1 xIn
          have more := Finset.card_lt_card larger
          have still := Finset.card_erase_add_one xInOld
          have enough := nontrivial A inFamily
          omega
      have stillLaminar : ∀ B ∈ reduced, ∀ C ∈ reduced, Disjoint B C ∨ B ⊆ C ∨ C ⊆ B := by
        intro B hB C hC
        obtain ⟨oldB, inB, rfl⟩ := Finset.mem_image.mp hB
        obtain ⟨oldC, inC, rfl⟩ := Finset.mem_image.mp hC
        rcases laminar oldB (Finset.mem_of_mem_erase inB) oldC (Finset.mem_of_mem_erase inC) with
          apart | larger | smaller
        · exact Or.inl (apart.mono (Finset.erase_subset x oldB) (Finset.erase_subset x oldC))
        · exact Or.inr (Or.inl (Finset.erase_subset_erase x larger))
        · exact Or.inr (Or.inr (Finset.erase_subset_erase x smaller))
      have removesVertex : (vertices.erase x).card + 1 = vertices.card :=
        Finset.card_erase_add_one (contained A inFamily xIn)
      have enoughFuel : (vertices.erase x).card < fuel := by omega
      have smallerBound := ih (vertices.erase x) reduced enoughFuel smallerSets stillNontrivial stillLaminar
      have distinctImage : reduced.card = other.card := Finset.card_image_of_injOn injective
      have removesSet : other.card + 1 = family.card := Finset.card_erase_add_one inFamily
      omega
    · have empty := Finset.not_nonempty_iff_eq_empty.mp present
      simp [empty]

/-- A laminar family of nonsingleton nonempty subsets of the vertex set
has at most as many members as vertices. -/
theorem laminarBlossomFamily_card_le (vertices : Finset α) (family : Finset (Finset α))
    (contained : ∀ A ∈ family, A ⊆ vertices) (nontrivial : ∀ A ∈ family, 1 < A.card)
    (laminar : ∀ A ∈ family, ∀ B ∈ family, Disjoint A B ∨ A ⊆ B ∨ B ⊆ A) :
    family.card ≤ vertices.card :=
  laminarCard_le_of_fuel (vertices.card + 1) vertices family (Nat.lt_succ_self _)
    contained nontrivial laminar

theorem blossomFamily_card_le_dimension {k : ℕ} {cuts : Finset (Finset (Fin k))}
    (nontrivial : ∀ A ∈ cuts, 1 < A.card)
    (laminar : ∀ A ∈ cuts, ∀ B ∈ cuts, Disjoint A B ∨ A ⊆ B ∨ B ⊆ A) : cuts.card ≤ k := by
  simpa using laminarBlossomFamily_card_le Finset.univ cuts
    (fun _ _ => Finset.subset_univ _) nontrivial laminar

/-- Count original vertices that are still nonouter, inherited blossoms,
and distinct outer blocks of the current partition. -/
def matchingPartitionCounts {k : ℕ} {vertices : Finset (Fin k)}
    {cuts : Finset (Finset (Fin k))} (blocks : TopLevelMatchingBlocks vertices cuts)
    (outer : Finset (Fin k) → Prop) [DecidablePred outer] (inherited : Finset (Finset (Fin k))) :
    MatchingStageCounts :=
  ⟨(vertices.filter (fun v => ¬outer (blocks.block v))).card, inherited.card,
    ((vertices.image blocks.block).filter outer).card⟩

theorem matchingPartitionCounts_vertices_le {k : ℕ} {vertices : Finset (Fin k)}
    {cuts : Finset (Finset (Fin k))} (blocks : TopLevelMatchingBlocks vertices cuts)
    (outer : Finset (Fin k) → Prop) [DecidablePred outer] (inherited : Finset (Finset (Fin k))) :
    (matchingPartitionCounts blocks outer inherited).nonouterVertices +
      (matchingPartitionCounts blocks outer inherited).outerBlocks ≤ vertices.card := by
  dsimp only [matchingPartitionCounts]
  rw [Finset.filter_image]
  have count := Finset.card_filter_add_card_filter_not (s := vertices) (fun v => outer (blocks.block v))
  have image : ((vertices.filter (fun v => outer (blocks.block v))).image blocks.block).card ≤
      (vertices.filter (fun v => outer (blocks.block v))).card := Finset.card_image_le
  omega

theorem matchingPartitionCounts_credit_le {k : ℕ} {vertices : Finset (Fin k)}
    {cuts inherited : Finset (Finset (Fin k))} (blocks : TopLevelMatchingBlocks vertices cuts)
    (outer : Finset (Fin k) → Prop) [DecidablePred outer] (inheritedCuts : inherited ⊆ cuts)
    (nontrivial : ∀ A ∈ cuts, 1 < A.card)
    (laminar : ∀ A ∈ cuts, ∀ B ∈ cuts, Disjoint A B ∨ A ⊆ B ∨ B ⊆ A) :
    (matchingPartitionCounts blocks outer inherited).credit ≤ 6 * k := by
  let counts := matchingPartitionCounts blocks outer inherited
  have verticesBound : vertices.card ≤ k := by simpa using (Finset.card_le_univ vertices)
  have blocksBound : counts.nonouterVertices + counts.outerBlocks ≤ k :=
    (matchingPartitionCounts_vertices_le blocks outer inherited).trans verticesBound
  have inheritedBound : counts.inheritedBlossoms ≤ k :=
    (Finset.card_le_card inheritedCuts).trans (blossomFamily_card_le_dimension nontrivial laminar)
  change counts.credit ≤ 6 * k
  rw [MatchingStageCounts.credit]
  omega



end VehicleRoutingSurvey.Routing
end RppSource_BlossomCreditBounds

/-! matching/MatchingSearchWitnesses.lean -/
section RppSource_MatchingSearchWitnesses
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory









theorem resetAlternatingForest_has_no_parent_witnesses {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (s : ArithmeticState) :
    MatchingForestOriginalWitnesses part (resetAlternatingForest part.activeRepresentatives state.partialMate) s := by
  intro child parent link
  by_cases root : child ∈ part.activeRepresentatives ∧ state.partialMate child = none <;>
    simp [resetAlternatingForest, root, AlternatingForestRole.parent] at link


end VehicleRoutingSurvey.Routing
end RppSource_MatchingSearchWitnesses

/-! matching/MatchingCacheInsertion.lean -/
section RppSource_MatchingCacheInsertion
namespace VehicleRoutingSurvey.Routing



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

/-! matching/MatchingRegistryBudget.lean -/
section RppSource_MatchingRegistryBudget
namespace VehicleRoutingSurvey.Routing



theorem MatchingRegistryBudget.start {k stage : ℕ} {s : ArithmeticState} {counts : MatchingStageCounts}
    (copied : s.nr 39 = s.nr 76) (between : s.nr 76 ≤ 6 * k * stage + 1) (credit : counts.credit ≤ 6 * k) :
    MatchingRegistryBudget k stage s counts := by
  refine ⟨copied.trans_le between, ?_, copied.le⟩
  omega

theorem MatchingRegistryBudget.keeps {k stage : ℕ} {s t : ArithmeticState} {before after : MatchingStageCounts}
    (budget : MatchingRegistryBudget k stage s before) (cutoff : t.nr 39 = s.nr 39)
    (cursor : t.nr 76 = s.nr 76) (counts : after = before) : MatchingRegistryBudget k stage t after := by
  refine ⟨cutoff.trans_le budget.cutoff, ?_, cutoff.trans_le (budget.cutoff_le_cursor.trans_eq cursor.symm)⟩
  rw [cutoff,cursor,counts]
  exact budget.allowance








end VehicleRoutingSurvey.Routing
end RppSource_MatchingRegistryBudget

/-! matching/MatchingRegistryView.lean -/
section RppSource_MatchingRegistryView
namespace VehicleRoutingSurvey.Routing



theorem MatchingRegistryView.credit_le {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState} {dual : MatchingSearchDualMemory part forest s}
    (registry : MatchingRegistryView dual) (positive : 0 < k) (initialNode : ℕ) :
    (matchingStageCountsFromRAM k s initialNode).credit ≤ 6 * k := by
  rw [matchingStageCountsFromRAM_eq dual positive initialNode registry.trees registry.unique registry.keys]
  exact matchingPartitionCounts_credit_le part.blocks (part.outerBlock forest positive) (Finset.filter_subset _ _)
    registry.nontrivial registry.laminar

theorem MatchingRegistryView.starts_budget {k stage : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState} {dual : MatchingSearchDualMemory part forest s}
    (registry : MatchingRegistryView dual) (positive : 0 < k)
    (copied : s.nr 39 = s.nr 76) (cursor : s.nr 76 ≤ 6 * k * stage + 1) :
    MatchingRegistryBudget k stage s (matchingStageCountsFromRAM k s (s.nr 39)) :=
  MatchingRegistryBudget.start copied cursor (registry.credit_le positive (s.nr 39))

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

def MatchingLiveCycleMemory.aboveFloor {k floor : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {node : Finset (Fin k) → ℕ} {B : Finset (Fin k)}
    {e : MatchingLiveCycle state node B} {s t : ArithmeticState} (memory : MatchingLiveCycleMemory e s)
    (order : MatchingCycleRecordOrder s) (starts : floor ≤ s.nr 77) (sizes : floor ≤ s.nr 78)
    (rows : floor ≤ matchingRebaseScratchEnd s)
    (bounds : ∀ n ∈ node B :: e.tree.registryIds, 0 < n ∧ n < s.nr 76)
    (ports : ∀ r ∈ ([55,77,78,79,80] : List ℕ), t.nr r = s.nr r)
    (natural : ∀ a ≥ floor, t.nm a = s.nm a) : MatchingLiveCycleMemory e t := by
  have fixed (r : ℕ) (used : r ∈ ([55,77,78,79,80] : List ℕ) := by decide) := ports r used
  let root := MatchingMemberTree.blossom 0 (node B) e.tree .nil
  have words : root.readable s.nm (s.nr 77) (s.nr 78) (fun a => floor ≤ a) := by
    apply root.readableAbove order starts sizes rows
    simpa [root, MatchingMemberTree.registryIds] using bounds
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
  have range := bounds (node B) (by simp)
  have rowFloor := rows.trans (order.bounded (node B) range.1 range.2).1
  have start : matchingCycleRecordStart t (node B) = matchingCycleRecordStart s (node B) := by
    rw [matchingCycleRecordStart,fixed 77]; exact natural _ (by omega)
  refine ⟨members, ⟨?_, ?_⟩⟩
  · rw [fixed 78, natural _ (by omega)]; exact memory.rows.length
  · intro i
    let addr := matchingCycleRecordStart s (node B) + 4*i.val
    have safe : floor ≤ addr := by dsimp [addr]; omega
    have cell : matchingCycleChildAt t.nm addr = matchingCycleChildAt s.nm addr := by
      simp only [matchingCycleChildAt, natural addr safe, natural (addr+1) (by omega), natural (addr+2) (by omega),
        natural (addr+3) (by omega)]
    simpa only [start, show matchingCycleChildAt t.nm (matchingCycleRecordStart s (node B) + 4*i.val) = _ from cell]
      using memory.rows.records i


end VehicleRoutingSurvey.Routing
end RppSource_MatchingLiveCycleHighFrame

/-! matching/MatchingForestLinkMemory.lean -/
section RppSource_MatchingForestLinkMemory
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



theorem MatchingForestLinkMemory.reset {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (s : ArithmeticState) :
    MatchingForestLinkMemory part (resetAlternatingForest part.activeRepresentatives state.partialMate) s := by
  constructor
  · intro v away
    have absent : v ∉ part.activeRepresentatives := fun h => away ((part.mem_activeRepresentatives v).mp h)
    simp [resetAlternatingForest, absent]
  · intro child parent role
    by_cases root : child ∈ part.activeRepresentatives ∧ state.partialMate child = none <;>
      simp [resetAlternatingForest, root] at role

theorem MatchingForestLinkMemory.advance {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state next : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {nextPart : CompactMatchingPartition next} {forest : AlternatingForestState (Fin k)} {s t : ArithmeticState}
    (links : MatchingForestLinkMemory part forest s) (reps : nextPart.representative = part.representative)
    (words : ∀ v : Fin k, matchingForestWitnessAt t.nm (t.nr 90) v.val =
      matchingForestWitnessAt s.nm (s.nr 90) v.val) : MatchingForestLinkMemory nextPart forest t := by
  exact ⟨fun v away => links.inactive v (reps ▸ away), fun {child _} role => (words child).trans (links.matched role)⟩




end VehicleRoutingSurvey.Routing
end RppSource_MatchingForestLinkMemory

/-! matching/MatchingWarmCacheMeaning.lean -/
section RppSource_MatchingWarmCacheMeaning
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The mathematical candidates scanned for a selector row during warm preparation. -/
noncomputable def warmCandidateInputs {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (row : ℕ) : List (DualSlack (MatchingDualEvent k)) :=
  ((List.finRange k).filter fun u => decide (role (rep u) = 1)).flatMap fun u =>
    (List.finRange k).filterMap fun v => outerRefreshRowInput rep role cost effective u v row

private theorem warmCandidateInputs_mem {k : ℕ} {rep : Fin k → Fin k} {role : Fin k → ℕ}
    {cost : Fin k → Fin k → ℝ} {effective : Fin k → ℝ} {row : ℕ} {d : DualSlack (MatchingDualEvent k)} :
    d ∈ warmCandidateInputs rep role cost effective row ↔
      ∃ u v : Fin k, role (rep u) = 1 ∧ outerRefreshRowInput rep role cost effective u v row = some d := by
  simp only [warmCandidateInputs, List.mem_flatMap, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq, List.mem_filterMap]
  constructor
  · rintro ⟨u, outer, v, found⟩
    exact ⟨u, v, outer, found⟩
  · rintro ⟨u, v, outer, found⟩
    exact ⟨u, outer, v, found⟩

/-- A cache built from the exact warm scan covers each full dual slacks group.
All cuts start with rate zero, since warm preparation has no inner labels. -/
theorem warmCandidateInputs_membership {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (positive : 0 < k)
    (symmetric : ∀ a b, cost a b = cost b a)
    (nested : ∀ S ∈ state.cuts, ∀ a ∈ S, ∀ b ∈ S, part.blocks.block a = part.blocks.block b)
    (group : MatchingCandidateGroup k) (d : DualSlack (MatchingDualEvent k)) :
    let forest := resetAlternatingForest part.activeRepresentatives state.partialMate
    let rep := part.representativeOf positive
    let label := part.dualLabel forest positive
    let constraints := matchingDualSlacks cost (compactMatchingEdges k) state.cuts state.potential
      (forestVertexDirection part.blocks label) state.cutDual (forestCutDirection part.blocks label)
    d ∈ warmCandidateInputs part.representative (fun v => alternatingRoleCode (forest.role v)) cost
      (effectiveVertexPotential state.cuts state.potential state.cutDual) group.slot ↔
      d ∈ constraints ∧ group.admits part.blocks forest rep d := by
  intro forest rep label constraints
  let effective := effectiveVertexPotential state.cuts state.potential state.cutDual
  let edge := matchingEdgeSlack cost state.cuts state.potential (forestVertexDirection part.blocks label)
    state.cutDual (forestCutDirection part.blocks label)
  have plain (v : Fin k) : forest.role v = .outer none ∨ forest.role v = .unlabelled := by
    by_cases root : v ∈ part.activeRepresentatives ∧ state.partialMate v = none
    · exact Or.inl (by simp [forest, resetAlternatingForest, root])
    · exact Or.inr (by simp [forest, resetAlternatingForest, root])
  have repRead (v : Fin k) : rep (part.blocks.block v) = part.representative v := part.representativeOf_block positive v
  have value {u v : Fin k} (separate : part.blocks.block u ≠ part.blocks.block v) :
      edge s(u, v) = ⟨.edge s(u, v), cost u v - effective u - effective v,
        (forest.role (part.representative u)).dualDirection + (forest.role (part.representative v)).dualDirection⟩ := by
    have distinct : u ≠ v := fun eq => separate (congrArg part.blocks.block eq)
    dsimp [edge, matchingEdgeSlack]
    have labelAt (w : Fin k) : label (part.blocks.block w) = (forest.role (part.representative w)).dualDirection :=
      part.dualLabel_block forest positive w
    rw [edgeCost_eq_of_symmetric cost symmetric, external_edge_dual_eq_effectivePotential part.blocks nested _ _ separate,
      forest_edge_slope part.blocks label (Finset.mem_univ u) (Finset.mem_univ v) distinct, if_neg separate,
      labelAt u, labelAt v]
    congr 1
    dsimp only [effective]
    ring
  have full {u v : Fin k} (separate : part.blocks.block u ≠ part.blocks.block v) : edge s(u, v) ∈ constraints :=
    List.mem_append_left _ (List.mem_map_of_mem (mem_compactMatchingEdges_mk (fun eq => separate (congrArg part.blocks.block eq))))
  have cutNoRate (B : Finset (Fin k)) : (matchingCutSlack state.cutDual (forestCutDirection part.blocks label) B).rate ≠ 1 := by
    intro one
    have neg : forestCutDirection part.blocks label B < 0 := by
      change -forestCutDirection part.blocks label B = 1 at one
      linarith only [one]
    obtain ⟨_, p, bad⟩ := (forestCutDirection_negative_iff part.blocks (fun S => forest.role (rep S)) B).mp neg
    rcases plain (rep B) with normal | idle
    · simp [normal] at bad
    · simp [idle] at bad
  rw [warmCandidateInputs_mem]
  constructor
  · rintro ⟨u, v, active, encoded⟩
    have uOuter : forest.role (part.representative u) = .outer none := by
      rcases plain (part.representative u) with outer | dormant
      · exact outer
      · simp [dormant, alternatingRoleCode] at active
    have separated : part.representative u ≠ part.representative v := by
      intro same
      simp [outerRefreshRowInput, same] at encoded
    have different := fun same => separated (part.same_block.mpr same)
    have encoded' : outerNeighborRowCandidate u v (part.representative u) (part.representative v)
        (alternatingRoleCode (forest.role (part.representative v))) (cost u v - effective u - effective v) group.slot = some d := by
      simpa only [outerRefreshRowInput, if_neg separated] using encoded
    rcases plain (part.representative v) with vOuter | vIdle
    · have read := value different
      rw [uOuter, vOuter] at read
      norm_num [AlternatingForestRole.dualDirection] at read
      cases group with
      | outer i =>
        have hit : i.val = (part.representative u).val ∨ i.val = (part.representative v).val := by
          by_contra missing
          simp [outerNeighborRowCandidate, vOuter, alternatingRoleCode, MatchingCandidateGroup.slot, missing] at encoded'
        have deq : d = edge s(u, v) := by
          rw [read]
          exact (Option.some.inj (by simpa [outerNeighborRowCandidate, vOuter, alternatingRoleCode,
            MatchingCandidateGroup.slot, hit] using encoded')).symm
        subst d
        refine ⟨full different, ?_⟩
        have speed : (edge s(u, v)).rate = 2 := congrArg DualSlack.rate read
        rcases hit with left | right
        · exact ⟨speed, u, v, rfl, (repRead u).trans (Fin.ext left.symm)⟩
        · exact ⟨speed, v, u, congrArg MatchingDualEvent.edge Sym2.eq_swap, (repRead v).trans (Fin.ext right.symm)⟩
      | incoming i | cut i =>
        have far (a : Fin k) : (MatchingCandidateGroup.incoming i).slot ≠ a.val ∧
            (MatchingCandidateGroup.cut i).slot ≠ a.val := by
          have inside := a.isLt
          simp only [MatchingCandidateGroup.slot]
          omega
        simp [outerNeighborRowCandidate, vOuter, alternatingRoleCode, far] at encoded'
    · have read := value different
      rw [uOuter, vIdle] at read
      norm_num [AlternatingForestRole.dualDirection] at read
      cases group with
      | incoming i =>
        have hit : i = v := by
          by_contra missing
          have address : k + i.val ≠ k + v.val := fun eq => missing (Fin.ext (Nat.add_left_cancel eq))
          simp [outerNeighborRowCandidate, vIdle, alternatingRoleCode, MatchingCandidateGroup.slot, address] at encoded'
          exact missing (Fin.ext encoded'.1)
        subst i
        have deq : d = edge s(u, v) := by
          rw [read]
          exact (Option.some.inj (by simpa [outerNeighborRowCandidate, vIdle, alternatingRoleCode,
            MatchingCandidateGroup.slot] using encoded')).symm
        subst d
        refine ⟨full different, ?_⟩
        refine ⟨?_, u, rfl, different, ⟨none, (congrArg forest.role (repRead u)).trans uOuter⟩,
          Or.inl ((congrArg forest.role (repRead v)).trans vIdle)⟩
        rw [read, repRead, vIdle]
        rfl
      | outer i | cut i =>
        have far : (MatchingCandidateGroup.outer i).slot ≠ k + v.val ∧
            (MatchingCandidateGroup.cut i).slot ≠ k + v.val := by
          have left := i.isLt
          have right := v.isLt
          simp only [MatchingCandidateGroup.slot]
          omega
        simp [outerNeighborRowCandidate, vIdle, alternatingRoleCode, far] at encoded'
  · rintro ⟨present, admitted⟩
    change d ∈ (compactMatchingEdges k).map edge ++ state.cuts.toList.map
      (matchingCutSlack state.cutDual (forestCutDirection part.blocks label)) at present
    rcases List.mem_append.mp present with inEdges | inCuts
    · obtain ⟨e, legal, rfl⟩ := List.mem_map.mp inEdges
      cases group with
      | outer i =>
        obtain ⟨speed, u, v, same, source⟩ := admitted
        change MatchingDualEvent.edge e = .edge s(u, v) at same
        obtain rfl := MatchingDualEvent.edge.inj same
        have distinct : u ≠ v := fun eq => (mem_compactMatchingEdges_iff.mp legal) (Sym2.mk_isDiag_iff.mpr eq)
        have different : part.blocks.block u ≠ part.blocks.block v := by
          intro same
          change oddCutDualEdgeValue state.cuts (forestVertexDirection part.blocks label)
            (forestCutDirection part.blocks label) s(u, v) = 2 at speed
          rw [forest_edge_slope part.blocks label (Finset.mem_univ u) (Finset.mem_univ v) distinct, if_pos same] at speed
          norm_num at speed
        have extracted := value different
        have roles : forest.role (part.representative u) = .outer none ∧
            forest.role (part.representative v) = .outer none := by
          rw [extracted] at speed
          rcases plain (part.representative u) with up | up <;> rcases plain (part.representative v) with vp | vp <;>
            first | exact ⟨up, vp⟩ | norm_num [up, vp, AlternatingForestRole.dualDirection] at speed
        have apart : part.representative u ≠ part.representative v := fun eq => different (part.same_block.mp eq)
        have slot : i.val = (part.representative u).val := congrArg Fin.val (source.symm.trans (repRead u))
        refine ⟨u, v, by simp [roles.1, alternatingRoleCode], ?_⟩
        rw [extracted]
        simp [outerRefreshRowInput, apart, outerNeighborRowCandidate, MatchingCandidateGroup.slot,
          slot, roles.1, roles.2, alternatingRoleCode, AlternatingForestRole.dualDirection, effective] <;> norm_num
      | incoming v =>
        obtain ⟨_, u, same, different, ⟨p, uOuter⟩, vIdle | ⟨q, inner⟩⟩ := admitted
        · change MatchingDualEvent.edge e = .edge s(u, v) at same
          obtain rfl := MatchingDualEvent.edge.inj same
          rw [repRead] at uOuter vIdle
          have apart : part.representative u ≠ part.representative v := fun eq => different (part.same_block.mp eq)
          refine ⟨u, v, by simp [uOuter, alternatingRoleCode], ?_⟩
          rw [value different]
          simp [outerRefreshRowInput, apart, outerNeighborRowCandidate, MatchingCandidateGroup.slot,
            uOuter, vIdle, alternatingRoleCode, AlternatingForestRole.dualDirection, effective]
        · rcases plain (rep (part.blocks.block v)) with regular | idle
          · simp [regular] at inner
          · simp [idle] at inner
      | cut i =>
        obtain ⟨_, B, wrong, _⟩ := admitted
        cases wrong
    · obtain ⟨B, _, rfl⟩ := List.mem_map.mp inCuts
      cases group with
      | outer i =>
        obtain ⟨_, u, v, wrong, _⟩ := admitted
        cases wrong
      | incoming v =>
        obtain ⟨_, u, wrong, _⟩ := admitted
        cases wrong
      | cut i => exact (cutNoRate B admitted.1).elim

/-- After clearing and scanning the warm rows, each stored value is a minimum over
the mathematical constraint group consumed by the selector. -/
theorem warmCandidateInputs_least {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (positive : 0 < k)
    (symmetric : ∀ a b, cost a b = cost b a)
    (nested : ∀ S ∈ state.cuts, ∀ a ∈ S, ∀ b ∈ S, part.blocks.block a = part.blocks.block b)
    (group : MatchingCandidateGroup k) :
    let forest := resetAlternatingForest part.activeRepresentatives state.partialMate
    let rep := part.representativeOf positive
    let label := part.dualLabel forest positive
    let constraints := matchingDualSlacks cost (compactMatchingEdges k) state.cuts state.potential
      (forestVertexDirection part.blocks label) state.cutDual (forestCutDirection part.blocks label)
    let entries := warmCandidateInputs part.representative (fun v => alternatingRoleCode (forest.role v)) cost
      (effectiveVertexPotential state.cuts state.potential state.cutDual) group.slot
    LeastSlackEntry (constraints.filter fun d => @decide _ (Classical.propDecidable (group.admits part.blocks forest rep d)))
      (insertSlackCandidates entries none) := by
  classical
  intro forest rep label constraints entries
  have empty : LeastSlackEntry ([] : List (DualSlack (MatchingDualEvent k))) none := by
    constructor <;> simp
  have scanned := empty.insert_many entries
  have membership (d : DualSlack (MatchingDualEvent k)) : d ∈ entries.reverse ++ [] ↔
      d ∈ constraints.filter (fun d => @decide _ (Classical.propDecidable (group.admits part.blocks forest rep d))) := by
    rw [List.append_nil, List.mem_reverse, List.mem_filter, decide_eq_true_eq]
    exact warmCandidateInputs_membership part positive symmetric nested group d
  exact ⟨fun found => (membership _).mp (scanned.sound found),
    fun x found => scanned.covers x ((membership x).mpr found)⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingWarmCacheMeaning

/-! matching/MatchingWarmCacheRows.lean -/
section RppSource_MatchingWarmCacheRows
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

noncomputable def warmSourceRowInputs {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (row : ℕ) (u : Fin k) :
    List (DualSlack (MatchingDualEvent k)) :=
  if role (rep u) = 0 then [] else (List.finRange k).filterMap (fun v => outerRefreshRowInput rep role cost effective u v row)

noncomputable def warmSourcePairInputs {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (time : ℝ) (slot : ℕ) (u : Fin k) :
    List (DualSlack (MatchingDualEvent k)) :=
  if role (rep u) = 0 then [] else (List.finRange k).filterMap (fun v => outerRefreshPairInput rep role cost effective time u v slot)

theorem refreshWarmCacheSource_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} {rep : Fin k → Fin k} {role : Fin k → ℕ}
    {cost : Fin k → Fin k → ℝ} {effective : Fin k → ℝ} {u : Fin k}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (input : MatchingRefreshInput s rep role cost effective) (source : s.nr 24 = u.val)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k*k, MatchingPairBucketValid k s i) :
    ∃ t steps, steps ≤ 98*k + 8 ∧ BlockRuns refreshWarmCacheSource steps s t ∧ t.halted = false ∧
      t.rr 15 = s.rr 15 ∧ MatchingRefreshInput t rep role cost effective ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧
        readMatchingCandidate cutAt t i = insertSlackCandidates (warmSourceRowInputs rep role cost effective i u)
          (readMatchingCandidate cutAt s i)) ∧
      (∀ i < k*k, MatchingPairBucketValid k t i ∧
        readMatchingPairBucket (k := k) t i = insertSlackCandidates (warmSourcePairInputs rep role cost effective (s.rr 15) i u)
          (readMatchingPairBucket (k := k) s i)) := by
  let words := Function.update (Function.update (Function.update s.nr 15 u.val) 6 (s.nr 51 + (rep u).val)) 26 (rep u).val
  let loaded := {s with pc := 5, nr := Function.update words 19 (role (rep u))}
  have load : BlockRuns readWarmCacheSource 5 s loaded := by
    apply BlockRuns.of_running_exit
    · simp [words, loaded, readWarmCacheSource, arithmeticStep, entry, running, zero, source, input.representatives u,
        input.roles (rep u), Function.iterate_succ_apply', Function.update_idem, Function.update_comm]
    · exact running
    · rfl
  let a := {loaded with pc := 0}
  have keep (r : ℕ) (away : r ∉ [6, 15, 19, 26] := by decide) : a.nr r = s.nr r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at away
    obtain ⟨r6, r15, r19, r26⟩ := away
    simp [a, loaded, words, r6, r15, r19, r26]
  have label : a.nr 19 = role (rep u) := by simp [a, loaded, words]
  have origin : a.nr 15 = u.val := by simp [a, loaded, words]
  have representative : a.nr 26 = (rep u).val := by simp [a, loaded, words]
  have aZero : a.nr 14 = 0 := (keep 14).trans zero
  have aOne : a.nr 9 = 1 := (keep 9).trans one
  have aInput : MatchingRefreshInput a rep role cost effective := input.keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    (fun r listed => keep r (by simp [matchingRefreshTableRegisters] at listed; simp; omega))
  have aRows (i : ℕ) (hi : i < a.nr 61) : MatchingCandidateRowValid cutAt a i := by
    have before : i < s.nr 61 := by rwa [keep 61] at hi
    simpa only [MatchingCandidateRowValid, decodeMatchingDictionaryEvent, keep 54, keep 58,
      show a.nm = s.nm from rfl] using rows i before
  have aBuckets (i : ℕ) (hi : i < k*k) : MatchingPairBucketValid k a i := by
    simpa only [MatchingPairBucketValid, keep 65, show a.nm = s.nm from rfl] using buckets i hi
  have rowRead (i : ℕ) : readMatchingCandidate cutAt a i = readMatchingCandidate cutAt s i := by
    simp only [readMatchingCandidate, decodeMatchingDictionaryEvent, keep 54, keep 58, keep 59, keep 60,
      show a.nm = s.nm from rfl, show a.rm = s.rm from rfl]
  have pairRead (i : ℕ) : readMatchingPairBucket (k := k) a i = readMatchingPairBucket (k := k) s i := by
    simp only [readMatchingPairBucket, keep 65, keep 66, show a.nm = s.nm from rfl, show a.rm = s.rm from rfl]
  by_cases inactive : role (rep u) = 0
  · have skipped : BlockRuns [] 0 a a := BlockRuns.of_running_exit rfl running rfl
    have route := branchOnAtMost_left 19 14 [] refreshSelectedOuterVertex (s := a) rfl running
      (by rw [label, aZero, inactive]) skipped running
    have run : BlockRuns refreshWarmCacheSource 7 s _ := load.append route
    refine ⟨_, _, by omega, run, running, rfl, ?_, ?_, ?_⟩
    · exact aInput.keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
    · intro i hi
      have inside : i < a.nr 61 := by rwa [keep 61]
      change MatchingCandidateRowValid cutAt a i ∧ readMatchingCandidate cutAt a i = _
      exact ⟨aRows i inside, by simp [warmSourceRowInputs, inactive, rowRead, insertSlackCandidates]⟩
    · intro i hi
      change MatchingPairBucketValid k a i ∧ readMatchingPairBucket (k := k) a i = _
      exact ⟨aBuckets i hi, by simp [warmSourcePairInputs, inactive, pairRead, insertSlackCandidates]⟩
  · obtain ⟨t, ticks, bound, refreshed, live, _, time, newInput, newRows, newPairs⟩ :=
      refreshSelectedOuterVertex_rows cutAt (s := a) rfl running aOne aZero aInput origin representative aRows aBuckets
    have goes : a.nr 14 < a.nr 19 := by rw [label, aZero]; omega
    have route := branchOnAtMost_right 19 14 [] refreshSelectedOuterVertex (s := a) rfl running goes refreshed live
    have run : BlockRuns refreshWarmCacheSource (5 + (1 + ticks)) s _ := load.append route
    refine ⟨_, _, by omega, run, live, time, ?_, ?_, ?_⟩
    · exact newInput.keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
    · intro row hi
      have inside : row < a.nr 61 := by rwa [keep 61]
      change MatchingCandidateRowValid cutAt t row ∧ readMatchingCandidate cutAt t row = _
      simpa only [warmSourceRowInputs, if_neg inactive, rowRead] using newRows row inside
    · intro slot hi
      change MatchingPairBucketValid k t slot ∧ readMatchingPairBucket (k := k) t slot = _
      simpa only [warmSourcePairInputs, if_neg inactive, pairRead, show a.rr 15 = s.rr 15 from rfl] using newPairs slot hi

private theorem warmCachePrefix_succ {k : ℕ} {Event : Type*}
    (inputs : Fin k → List (DualSlack Event)) (old : Option (DualSlack Event)) (i : ℕ) (hi : i < k) :
    insertSlackCandidates (((List.finRange k).take (i+1)).flatMap inputs) old =
      insertSlackCandidates (inputs ⟨i, hi⟩) (insertSlackCandidates (((List.finRange k).take i).flatMap inputs) old) := by
  have within : i < (List.finRange k).length := by simpa using hi
  rw [List.take_succ_eq_append_getElem within, List.getElem_finRange, List.flatMap_append]
  simp [insertSlackCandidates, List.foldl_append]

private theorem warmCache_unchanged {k : ℕ} (cutAt : Fin k → Finset (Fin k)) {m t : ArithmeticState}
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

private structure WarmCacheRowsProgress {k : ℕ} (cutAt : Fin k → Finset (Fin k)) (s : ArithmeticState)
    (rep : Fin k → Fin k) (role : Fin k → ℕ) (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ)
    (seen : ℕ) (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  running : m.halted = false
  index : m.nr 24 = seen
  fixed : ∀ r, r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 26] → m.nr r = s.nr r
  time : m.rr 15 = s.rr 15
  input : MatchingRefreshInput m rep role cost effective
  rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt m i ∧
    readMatchingCandidate cutAt m i = insertSlackCandidates (((List.finRange k).take seen).flatMap
      (warmSourceRowInputs rep role cost effective i)) (readMatchingCandidate cutAt s i)
  buckets : ∀ i < k*k, MatchingPairBucketValid k m i ∧
    readMatchingPairBucket (k := k) m i = insertSlackCandidates (((List.finRange k).take seen).flatMap
      (warmSourcePairInputs rep role cost effective (s.rr 15) i)) (readMatchingPairBucket (k := k) s i)

private theorem sweepWarmMatchingCache_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} {rep : Fin k → Fin k} {role : Fin k → ℕ}
    {cost : Fin k → Fin k → ℝ} {effective : Fin k → ℝ}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (input : MatchingRefreshInput s rep role cost effective)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k*k, MatchingPairBucketValid k s i) :
    ∃ t steps, steps ≤ k * (98*k + 11) + 2 ∧ BlockRuns sweepWarmMatchingCache steps s t ∧ t.halted = false ∧
      t.rr 15 = s.rr 15 ∧ MatchingRefreshInput t rep role cost effective ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i =
        insertSlackCandidates ((List.finRange k).flatMap (warmSourceRowInputs rep role cost effective i))
          (readMatchingCandidate cutAt s i)) ∧
      (∀ i < k*k, MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i =
        insertSlackCandidates ((List.finRange k).flatMap (warmSourcePairInputs rep role cost effective (s.rr 15) i))
          (readMatchingPairBucket (k := k) s i)) := by
  let inv := WarmCacheRowsProgress cutAt s rep role cost effective
  let seeded := {s with pc := 0, nr := Function.update s.nr 24 0}
  have seedKeep (r : ℕ) (away : r ≠ 24) : seeded.nr r = s.nr r := Function.update_of_ne away _ _
  have seedPorts (r : ℕ) (listed : r ∈ matchingRefreshTableRegisters) : seeded.nr r = s.nr r :=
    seedKeep r (by simp [matchingRefreshTableRegisters] at listed; omega)
  have seedInput := input.keeps (t := seeded) ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ seedPorts
  have seedCache := warmCache_unchanged cutAt (m := s) (t := seeded) rfl rfl seedPorts
  have initial : inv 0 seeded := by
    refine ⟨rfl, running, by simp [seeded], ?_, rfl, seedInput, ?_, ?_⟩
    · intro r safe
      apply seedKeep
      simp at safe
      omega
    · intro i hi
      refine ⟨(seedCache.1 i).1.symm ▸ rows i hi, ?_⟩
      simpa only [List.take_zero, List.flatMap_nil, insertSlackCandidates, List.foldl_nil] using (seedCache.1 i).2
    · intro i hi
      refine ⟨(seedCache.2 i).1.symm ▸ buckets i hi, ?_⟩
      simpa only [List.take_zero, List.flatMap_nil, insertSlackCandidates, List.foldl_nil] using (seedCache.2 i).2
  have next (i : ℕ) (hi : i < k) (m : ArithmeticState) (h : inv i m) :
      ∃ t steps, steps ≤ 98*k + 8 ∧ BlockRuns refreshWarmCacheSource steps m t ∧ t.halted = false ∧
        inv (i+1) {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)} := by
    have unit : m.nr 9 = 1 := (h.fixed 9 (by decide)).trans one
    have origin : m.nr 14 = 0 := (h.fixed 14 (by decide)).trans zero
    have rowAt (j : ℕ) (valid : j < m.nr 61) : MatchingCandidateRowValid cutAt m j :=
      (h.rows j (by rwa [h.fixed 61 (by decide)] at valid)).1
    obtain ⟨t, steps, bound, run, live, clock, tables, newRows, newBuckets⟩ :=
      refreshWarmCacheSource_rows cutAt (u := ⟨i, hi⟩) h.entry h.running unit origin h.input h.index
        rowAt (fun j valid => (h.buckets j valid).1)
    have keep := refreshWarmCacheSource_fixed run
    let advanced := {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)}
    have advKeep (r : ℕ) (away : r ≠ 24) : advanced.nr r = t.nr r := Function.update_of_ne away _ _
    have advPorts (r : ℕ) (listed : r ∈ matchingRefreshTableRegisters) : advanced.nr r = t.nr r :=
      advKeep r (by simp [matchingRefreshTableRegisters] at listed; omega)
    have advCache := warmCache_unchanged cutAt (m := t) (t := advanced) rfl rfl advPorts
    refine ⟨t, steps, bound, run, live, rfl, live, ?_, ?_, clock.trans h.time,
      tables.keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ advPorts, ?_, ?_⟩
    · simp [keep 24 (by decide), keep 9 (by decide), unit, h.index]
    · intro r safe
      have noIndex : r ≠ 24 := by simp at safe; omega
      have unchanged : r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 25, 26] := by simp at safe ⊢; omega
      exact (advKeep r noIndex).trans ((keep r unchanged).trans (h.fixed r safe))
    · intro j inside
      have prior : j < m.nr 61 := by rwa [h.fixed 61 (by decide)]
      change MatchingCandidateRowValid cutAt advanced j ∧ readMatchingCandidate cutAt advanced j = _
      rw [(advCache.1 j).1, (advCache.1 j).2]
      exact ⟨(newRows j prior).1, by
        rw [(newRows j prior).2, (h.rows j inside).2, warmCachePrefix_succ _ _ i hi]⟩
    · intro j inside
      change MatchingPairBucketValid k advanced j ∧ readMatchingPairBucket (k := k) advanced j = _
      rw [(advCache.2 j).1, (advCache.2 j).2]
      exact ⟨(newBuckets j inside).1, by
        rw [(newBuckets j inside).2, (h.buckets j inside).2, h.time, warmCachePrefix_succ _ _ i hi]⟩
  obtain ⟨t, steps, done, budget, run⟩ := countedLoopFromZero_bounded 9 24 55 k (98*k+8)
    refreshWarmCacheSource inv (s := s) entry running initial
    (fun _ _ h => ⟨h.entry, h.running, h.index, h.input.layout.dimension⟩) next
  have all : (List.finRange k).take k = List.finRange k := List.take_of_length_le (by simp)
  refine ⟨_, steps, ?_, run, done.running, done.time, ?_, ?_, ?_⟩
  · rw [show 98*k + 8 + 3 = 98*k + 11 by omega] at budget
    omega
  · exact done.input.keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
  · intro i hi
    change MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i = _
    simpa only [all] using done.rows i hi
  · intro i hi
    change MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i = _
    simpa only [all] using done.buckets i hi

theorem rebuildMatchingActiveCacheBlock_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} {rep : Fin k → Fin k} {role : Fin k → ℕ}
    {cost : Fin k → Fin k → ℝ} {effective : Fin k → ℝ}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (input : MatchingRefreshInput s rep role cost effective)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k*k, MatchingPairBucketValid k s i) :
    ∃ t steps, steps ≤ k * (98*k + 11) + 3 ∧ BlockRuns rebuildMatchingActiveCacheBlock steps s t ∧ t.halted = false ∧
      t.rr 15 = s.rr 15 ∧ MatchingRefreshInput t rep role cost effective ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i =
        insertSlackCandidates ((List.finRange k).flatMap (warmSourceRowInputs rep role cost effective i))
          (readMatchingCandidate cutAt s i)) ∧
      (∀ i < k*k, MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i =
        insertSlackCandidates ((List.finRange k).flatMap (warmSourcePairInputs rep role cost effective (s.rr 15) i))
          (readMatchingPairBucket (k := k) s i)) := by
  let seeded := {s with pc := 0, nr := Function.update s.nr 14 0}
  have keep (r : ℕ) (away : r ≠ 14 := by decide) : seeded.nr r = s.nr r := Function.update_of_ne away _ _
  have ports (r : ℕ) (listed : r ∈ matchingRefreshTableRegisters) : seeded.nr r = s.nr r :=
    keep r (by simp [matchingRefreshTableRegisters] at listed; omega)
  have cache := warmCache_unchanged cutAt (m := s) (t := seeded) rfl rfl ports
  obtain ⟨t, steps, bound, sweep, live, time, tables, newRows, newBuckets⟩ := sweepWarmMatchingCache_rows cutAt
    (s := seeded) rfl running ((keep 9).trans one) (by simp [seeded])
    (input.keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ ports)
    (fun i hi => (cache.1 i).1.symm ▸ rows i (by rwa [keep 61] at hi))
    (fun i hi => (cache.2 i).1.symm ▸ buckets i hi)
  refine ⟨_, 1+steps, by omega, (zeroRegister_runs 14 s entry running).append sweep, live, time, ?_, ?_, ?_⟩
  · exact tables.keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
  · intro i hi
    have inside : i < seeded.nr 61 := by rwa [keep 61]
    change MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i = _
    simpa only [(cache.1 i).2] using newRows i inside
  · intro i hi
    change MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i = _
    simpa only [(cache.2 i).2, show seeded.rr 15 = s.rr 15 from rfl] using newBuckets i hi

end VehicleRoutingSurvey.Routing
end RppSource_MatchingWarmCacheRows

/-! matching/MatchingWarmCacheRebuild.lean -/
section RppSource_MatchingWarmCacheRebuild
namespace VehicleRoutingSurvey.Routing

set_option maxHeartbeats 700000

theorem MatchingWarmCleared.refreshInput {k : ℕ} {s t : ArithmeticState}
    {active : Finset (Fin k)} {mate : Fin k → Option (Fin k)} {rep : Fin k → Fin k}
    {oldRole : Fin k → ℕ} {cost : Fin k → Fin k → ℝ} {effective : Fin k → ℝ}
    (cleared : MatchingWarmCleared s t active mate) (warm : MatchingWarmLayout s k)
    (input : MatchingRefreshInput s rep oldRole cost effective) :
    MatchingRefreshInput t rep (fun v => alternatingRoleCode ((resetAlternatingForest active mate).role v)) cost effective := by
  have port (r : ℕ) (safe : r ∉ [0, 1, 2, 3, 4, 5, 8, 9, 12, 13, 14, 15, 17, 29, 31, 32, 33, 34, 71, 72, 73] := by decide) :=
    cleared.fixed r safe
  have layout : MatchingCacheLayout k t := by
    refine ⟨(port 55).trans input.layout.dimension, (port 61).trans input.layout.rows, ?_, ?_, ?_, ?_⟩
    · rw [port 58, port 61, port 54]; exact input.layout.idsBefore
    · rw [port 54, port 61, port 65]; exact input.layout.recordsBefore
    · rw [port 59, port 61, port 60]; exact input.layout.slacksBefore
    · rw [port 60, port 61, port 66]; exact input.layout.ratesBefore
  have ordinary (addr : ℕ) (outside : addr < s.nr 51 ∨ s.nr 51 + 3*k ≤ addr) (before : addr < s.nr 58) :
      t.nm addr = s.nm addr := cleared.natural addr outside (fun h => (not_le.mpr before) h.1)
    (fun h => (not_le.mpr (before.trans_le warm.pairsAfter)) h.1)
  refine ⟨layout, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [port 21, port 58]; exact input.offsetsBefore
  · rw [port 57, port 58]; exact input.representativesBefore
  · rw [port 51, port 58]; exact input.rolesBefore
  · rw [port 20, port 59]; exact input.metricBefore
  · rw [port 62, port 59]; exact input.effectiveBefore
  · intro j
    have hi := j.isLt
    have low : s.nr 21 + j.val < s.nr 51 := by
      have left := warm.offsetsBefore
      have right := warm.matesBefore
      omega
    rw [port 21, ordinary _ (Or.inl low) (by have limit := input.offsetsBefore; omega)]
    exact input.offsets j
  · intro j
    have hi := j.isLt
    have high : s.nr 51 + 3*k ≤ s.nr 57 + j.val := by
      have fromForest := warm.representativesAfter
      omega
    rw [port 57, ordinary _ (Or.inr high) (by have limit := input.representativesBefore; omega)]
    exact input.representatives j
  · intro j
    rw [port 51]
    exact (cleared.forest j).1
  · intro i j
    rw [port 20, cleared.real]
    exact input.metric i j
  · intro j
    rw [port 62, cleared.real]
    exact input.potentials j

/-- The actual warm preparation rebuilds the complete row and pair caches from
the new forest. Prior row and bucket data do not affect either result. -/
theorem warmMatchingPreparationBlock_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} {active : Finset (Fin k)} {mate : Fin k → Option (Fin k)}
    {rep : Fin k → Fin k} {oldRole : Fin k → ℕ} {cost : Fin k → Fin k → ℝ} {effective : Fin k → ℝ}
    (entry : s.pc = 0) (running : s.halted = false) (warm : MatchingWarmLayout s k)
    (input : MatchingRefreshInput s rep oldRole cost effective)
    (activeAt : ∀ v, v ∈ active ↔ rep v = v)
    (mates : ∀ v : Fin k, s.nm (s.nr 50 + v.val) = (mate v).elim k Fin.val) :
    let role := fun v => alternatingRoleCode ((resetAlternatingForest active mate).role v)
    ∃ t steps, steps ≤ 104*k*k + 48*k + 31 ∧
      BlockRuns warmMatchingPreparationBlock steps s t ∧ t.halted = false ∧ t.rr 15 = 0 ∧
      MatchingRefreshInput t rep role cost effective ∧
      (∀ i < 3*k, MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i =
        insertSlackCandidates ((List.finRange k).flatMap (warmSourceRowInputs rep role cost effective i)) none) ∧
      (∀ i < k*k, MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i =
        insertSlackCandidates ((List.finRange k).flatMap (warmSourcePairInputs rep role cost effective 0 i)) none) := by
  intro role
  have offsets (i : ℕ) (hi : i < k) : s.nm (s.nr 21 + i) = k*i := input.offsets ⟨i, hi⟩
  obtain ⟨d, frontSteps, frontBudget, front, dLive, cleared⟩ :=
    warmMatchingPreparationPrefixBlock_runs entry running warm offsets activeAt mates input.representatives
  let start := {d with pc := 0}
  have startInput : MatchingRefreshInput start rep role cost effective :=
    (cleared.refreshInput warm input).keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
  have startTime : start.rr 15 = 0 := cleared.zeroClock
  have one : start.nr 9 = 1 := cleared.controls.2.2.2.2.2.1
  have startRows (i : ℕ) (hi : i < start.nr 61) :
      MatchingCandidateRowValid cutAt start i ∧ readMatchingCandidate cutAt start i = none := by
    have sameBase : start.nr 58 = s.nr 58 := cleared.fixed 58 (by decide)
    have sameCount : start.nr 61 = s.nr 61 := cleared.fixed 61 (by decide)
    have beforePair : s.nr 58 + s.nr 61 ≤ s.nr 65 := by
      have ids := input.layout.idsBefore
      have dict := input.layout.recordsBefore
      omega
    have empty : start.nm (start.nr 58 + i) = 0 := by
      rw [sameBase]
      exact cleared.emptyId beforePair i (sameCount ▸ hi)
    simp [MatchingCandidateRowValid, readMatchingCandidate, empty, decodeMatchingDictionaryEvent]
  have startPairs (i : ℕ) (hi : i < k*k) :
      MatchingPairBucketValid k start i ∧ readMatchingPairBucket (k := k) start i = none := by
    have base : start.nr 65 = s.nr 65 := cleared.fixed 65 (by decide)
    have empty : start.nm (start.nr 65 + (i+i)) = k := by
      rw [base]
      exact cleared.emptyPair i hi
    simp [MatchingPairBucketValid, readMatchingPairBucket, empty]
  obtain ⟨e, scanSteps, scanBudget, scan, live, time, finalInput, rows, buckets⟩ :=
    rebuildMatchingActiveCacheBlock_rows cutAt (s := start) rfl dLive one startInput
      (fun i hi => (startRows i hi).1) (fun i hi => (startPairs i hi).1)
  let t := relocateState warmMatchingPreparationPrefixBlock.length e
  have fullBudget : frontSteps + scanSteps ≤ 104*k*k + 48*k + 31 := by
    calc
      _ ≤ (6*(k*k) + 37*k + 28) + (k*(98*k+11)+3) := Nat.add_le_add frontBudget scanBudget
      _ = _ := by ring
  refine ⟨t, frontSteps + scanSteps, fullBudget, front.append scan, live, time.trans startTime, ?_, ?_, ?_⟩
  · exact finalInput.keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
  · intro i hi
    change MatchingCandidateRowValid cutAt e i ∧ readMatchingCandidate cutAt e i = _
    have valid : i < start.nr 61 := by rw [startInput.layout.rows]; exact hi
    simpa only [(startRows i valid).2] using rows i valid
  · intro i hi
    change MatchingPairBucketValid k e i ∧ readMatchingPairBucket (k := k) e i = _
    simpa only [(startPairs i hi).2, startTime] using buckets i hi

end VehicleRoutingSurvey.Routing
end RppSource_MatchingWarmCacheRebuild

/-! matching/MatchingWarmCacheLink.lean -/
section RppSource_MatchingWarmCacheLink
namespace VehicleRoutingSurvey.Routing

theorem warmSourceRowInputs_eq_warmCandidateInputs {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (row : ℕ)
    (labels : ∀ v, role v = 0 ∨ role v = 1) :
    (List.finRange k).flatMap (warmSourceRowInputs rep role cost effective row) =
      warmCandidateInputs rep role cost effective row := by
  have fold (sources : List (Fin k)) : sources.flatMap (warmSourceRowInputs rep role cost effective row) =
      (sources.filter fun u => decide (role (rep u) = 1)).flatMap (fun u =>
        (List.finRange k).filterMap (fun v => outerRefreshRowInput rep role cost effective u v row)) := by
    induction sources with
    | nil => rfl
    | cons head rest ih =>
      rcases labels (rep head) with off | on
      · simp [warmSourceRowInputs, off, ih]
      · simp [warmSourceRowInputs, on, ih]
  exact fold (List.finRange k)

theorem resetAlternatingForest_roleCode_cases {k : ℕ} (active : Finset (Fin k))
    (mate : Fin k → Option (Fin k)) (v : Fin k) :
    let label := alternatingRoleCode ((resetAlternatingForest active mate).role v)
    label = 0 ∨ label = 1 := by
  by_cases root : v ∈ active ∧ mate v = none <;>
    simp [resetAlternatingForest, root, alternatingRoleCode]

/-- The physical selector rows entered by a warm start cover the full dual system by
the required matching candidate groups. -/
theorem warmMatchingRows_least {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (positive : 0 < k)
    (symmetric : ∀ a b, cost a b = cost b a)
    (nested : ∀ S ∈ state.cuts, ∀ a ∈ S, ∀ b ∈ S, part.blocks.block a = part.blocks.block b)
    (cutAt : Fin k → Finset (Fin k)) (t : ArithmeticState)
    (exactRows : let forest := resetAlternatingForest part.activeRepresentatives state.partialMate
      let role := fun v => alternatingRoleCode (forest.role v)
      let effective := effectiveVertexPotential state.cuts state.potential state.cutDual
      ∀ i < 3*k, readMatchingCandidate cutAt t i =
        insertSlackCandidates ((List.finRange k).flatMap (warmSourceRowInputs part.representative role cost effective i)) none) :
    let forest := resetAlternatingForest part.activeRepresentatives state.partialMate
    let rep := part.representativeOf positive
    let label := part.dualLabel forest positive
    let constraints := matchingDualSlacks cost (compactMatchingEdges k) state.cuts state.potential
      (forestVertexDirection part.blocks label) state.cutDual (forestCutDirection part.blocks label)
    ∀ group : MatchingCandidateGroup k,
      LeastSlackEntry (constraints.filter fun d => @decide _ (Classical.propDecidable (group.admits part.blocks forest rep d)))
        (readMatchingCandidate cutAt t group.slot) := by
  intro forest rep label constraints group
  rw [exactRows group.slot group.slot_lt]
  rw [warmSourceRowInputs_eq_warmCandidateInputs _ _ _ _ _
    (resetAlternatingForest_roleCode_cases part.activeRepresentatives state.partialMate)]
  exact warmCandidateInputs_least part positive symmetric nested group

end VehicleRoutingSurvey.Routing
end RppSource_MatchingWarmCacheLink

/-! matching/MatchingWarmCacheFootprint.lean -/
section RppSource_MatchingWarmCacheFootprint
namespace VehicleRoutingSurvey.Routing

set_option maxHeartbeats 700000
set_option maxRecDepth 4096

private theorem refreshWarmCacheSource_footprint {k : ℕ} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (layout : MatchingCacheLayout k s) (offsets : MatchingCacheOffsets k s) (reps : MatchingCacheRepresentatives k s)
    (source : s.nr 24 < k) :
    ∃ t steps, steps ≤ 98*k+8 ∧ BlockRuns refreshWarmCacheSource steps s t ∧ t.halted = false ∧
      MatchingCacheFootprint k s t := by
  let p := (arithmeticStep readWarmCacheSource)^[5] s
  have live : p.halted = false := by
    simp [p, readWarmCacheSource, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : p.pc = readWarmCacheSource.length := by
    simp [p, readWarmCacheSource, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have read : BlockRuns readWarmCacheSource 5 s p := BlockRuns.of_running_exit rfl live exit
  let ready := {p with pc := 0}
  have unchanged : ready.nm = s.nm := by
    simp [ready, p, readWarmCacheSource, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have real : ready.rm = s.rm := by
    simp [ready, p, readWarmCacheSource, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have initial : MatchingCacheFootprint k s ready := MatchingCacheFootprint.unchanged unchanged real
  have keep (r : ℕ) (safe : r ∉ [0, 6, 15, 19, 26] := by decide) : ready.nr r = s.nr r := by
    change p.nr r = s.nr r
    apply arithmeticRun_keeps_register _ s 5
    simp [readWarmCacheSource, naturalDestination] at safe ⊢
    omega
  by_cases dormant : ready.nr 19 ≤ ready.nr 14
  · have empty : BlockRuns [] 0 ready ready := BlockRuns.of_running_exit rfl live rfl
    have run := branchOnAtMost_left 19 14 [] refreshSelectedOuterVertex (s := ready) rfl live dormant empty live
    exact ⟨_, 7, by omega, read.append run, live, initial.natural, initial.real⟩
  · have rep : ready.nr 26 = s.nm (s.nr 57 + s.nr 24) := by
      simp [ready, p, readWarmCacheSource, arithmeticStep, entry, running, zero, Function.iterate_succ_apply']
    obtain ⟨t, steps, scan, done, cost, footprint⟩ := refreshSelectedOuterVertex_footprint (s := ready) rfl live
      ((keep 9).trans one) ((keep 14).trans zero) (layout.keeps (fun r hr => keep r (by simp; omega)))
      (offsets.keeps initial (keep 21) (keep 58)) (reps.keeps initial (keep 57) (keep 58)) (rep.symm ▸ reps.rep _ source)
    have run := branchOnAtMost_right 19 14 [] refreshSelectedOuterVertex (s := ready) rfl live (lt_of_not_ge dormant) scan done
    have frame := initial.chain footprint (fun r listed => keep r (by simp at listed ⊢; omega))
    exact ⟨_, 5+(1+steps), by omega, read.append run, done, frame.natural, frame.real⟩

private structure WarmFootprintProgress (k : ℕ) (s : ArithmeticState) (i : ℕ) (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  live : m.halted = false
  cursor : m.nr 24 = i
  fixed : ∀ r, r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 26] → m.nr r = s.nr r
  footprint : MatchingCacheFootprint k s m

private theorem sweepWarmMatchingCache_footprint {k : ℕ} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (layout : MatchingCacheLayout k s) (offsets : MatchingCacheOffsets k s) (reps : MatchingCacheRepresentatives k s) :
    ∃ t steps, BlockRuns sweepWarmMatchingCache steps s t ∧ t.halted = false ∧ MatchingCacheFootprint k s t := by
  let inv := WarmFootprintProgress k s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 24 0} := by
    refine ⟨rfl, running, by simp, ?_, MatchingCacheFootprint.unchanged rfl rfl⟩
    intro r safe
    exact Function.update_of_ne (by simp at safe; omega) _ _
  have next (i : ℕ) (hi : i < k) (m : ArithmeticState) (hm : inv i m) :
      ∃ t steps, steps ≤ 98*k+8 ∧ BlockRuns refreshWarmCacheSource steps m t ∧ t.halted = false ∧
        inv (i+1) {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24+t.nr 9)} := by
    have keep (r : ℕ) (safe : r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 26] := by decide) := hm.fixed r safe
    have unit := (keep 9).trans one
    obtain ⟨t, steps, budget, run, live, footprint⟩ := refreshWarmCacheSource_footprint hm.entry hm.live unit
      ((keep 14).trans zero) (layout.keeps (fun r hr => keep r (by simp; omega)))
      (offsets.keeps hm.footprint (keep 21) (keep 58)) (reps.keeps hm.footprint (keep 57) (keep 58)) (hm.cursor.symm ▸ hi)
    have frame := hm.footprint.chain footprint (fun r listed => keep r (by simp at listed ⊢; omega))
    have stable := refreshWarmCacheSource_fixed run
    refine ⟨t, steps, budget, run, live, rfl, live, ?_, ?_, frame.natural, frame.real⟩
    · simp [stable 24 (by decide), stable 9 (by decide), hm.cursor, unit]
    · intro r safe
      change Function.update t.nr 24 (t.nr 24+t.nr 9) r = s.nr r
      rw [Function.update_of_ne (by simp at safe; omega : r ≠ 24)]
      exact (stable r (by simp at safe ⊢; omega)).trans (keep r safe)
  obtain ⟨t, steps, done, _, run⟩ := countedLoopFromZero_bounded 9 24 55 k (98*k+8)
    refreshWarmCacheSource inv (s := s) entry running initial
    (fun _ _ h => ⟨h.entry, h.live, h.cursor, (h.fixed 55 (by decide)).trans layout.dimension⟩) next
  exact ⟨_, steps, run, done.live, done.footprint.natural, done.footprint.real⟩

theorem rebuildMatchingActiveCacheBlock_footprint {k : ℕ} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (layout : MatchingCacheLayout k s) (offsets : MatchingCacheOffsets k s) (reps : MatchingCacheRepresentatives k s) :
    ∃ t steps, BlockRuns rebuildMatchingActiveCacheBlock steps s t ∧ t.halted = false ∧ MatchingCacheFootprint k s t := by
  let ready := {s with pc := 0, nr := Function.update s.nr 14 0}
  have keep (r : ℕ) (safe : r ≠ 14 := by decide) : ready.nr r = s.nr r := Function.update_of_ne safe _ _
  have frame : MatchingCacheFootprint k s ready := MatchingCacheFootprint.unchanged rfl rfl
  obtain ⟨t, steps, run, done, footprint⟩ := sweepWarmMatchingCache_footprint (s := ready) rfl running
    ((keep 9).trans one) (by simp [ready]) (layout.keeps (fun r found => keep r (by omega)))
    (offsets.keeps frame (keep 21) (keep 58)) (reps.keeps frame (keep 57) (keep 58))
  have combined := frame.chain footprint (fun r listed => keep r (by simp at listed; omega))
  exact ⟨_, 1+steps, (zeroRegister_runs 14 s entry running).append run, done, combined.natural, combined.real⟩

/-- The warm preparation leaves the registry, witnesses, and real memory beyond
the cache intact, as well as the low real memory preceding the cache. -/
theorem warmMatchingPreparationBlock_highFrame {k : ℕ} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (layout : MatchingWarmLayout s k)
    (cache : MatchingCacheLayout k s) (offsets : ∀ i < k, s.nm (s.nr 21+i) = k*i)
    {active : Finset (Fin k)} {mate : Fin k → Option (Fin k)} {rep : Fin k → Fin k}
    (activeAt : ∀ v, v ∈ active ↔ rep v = v)
    (mates : ∀ v : Fin k, s.nm (s.nr 50+v.val) = (mate v).elim k Fin.val)
    (reps : ∀ v : Fin k, s.nm (s.nr 57+v.val) = (rep v).val) :
    ∃ t steps, BlockRuns warmMatchingPreparationBlock steps s t ∧ t.halted = false ∧
      (∀ a ≥ s.nr 65 + 2*(k*k), t.nm a = s.nm a) ∧
      ∀ a, (a < s.nr 59 ∨ s.nr 66 + k*k ≤ a) → t.rm a = s.rm a := by
  obtain ⟨d, frontSteps, _, front, dLive, cleared⟩ :=
    warmMatchingPreparationPrefixBlock_runs entry running layout offsets activeAt mates reps
  let start := {d with pc := 0}
  have port (r : ℕ) (safe : r ∉ [0, 1, 2, 3, 4, 5, 8, 9, 12, 13, 14, 15, 17, 29, 31, 32, 33, 34, 71, 72, 73] := by decide) :
      start.nr r = s.nr r := cleared.fixed r safe
  have one : start.nr 9 = 1 := cleared.controls.2.2.2.2.2.1
  have forestEnd : s.nr 51+3*k ≤ s.nr 58 := by
    have a := layout.representativesAfter
    have b := layout.candidatesAfter
    omega
  have ordinary (a : ℕ) (away : a < s.nr 51 ∨ s.nr 51+3*k ≤ a) (low : a < s.nr 58) :
      start.nm a = s.nm a := cleared.natural a away (fun h => (not_le.mpr low) h.1)
    (fun h => (not_le.mpr (low.trans_le layout.pairsAfter)) h.1)
  have startsCache : MatchingCacheLayout k start := by
    refine ⟨(port 55).trans cache.dimension, (port 61).trans cache.rows, ?_, ?_, ?_, ?_⟩
    · rw [port 58, port 61, port 54]; exact cache.idsBefore
    · rw [port 54, port 61, port 65]; exact cache.recordsBefore
    · rw [port 59, port 61, port 60]; exact cache.slacksBefore
    · rw [port 60, port 61, port 66]; exact cache.ratesBefore
  have startsOffset : MatchingCacheOffsets k start := by
    have low (i : ℕ) (hi : i < k) : s.nr 21+i < s.nr 51 := by
      have a := layout.offsetsBefore
      have b := layout.matesBefore
      omega
    constructor
    · intro i hi
      rw [port 21, port 58]
      have h := low i hi
      omega
    · intro i hi
      rw [port 21, ordinary _ (Or.inl (low i hi)) (by have h := low i hi; omega)]
      exact offsets i hi
  have startsReps : MatchingCacheRepresentatives k start := by
    have low (i : ℕ) (hi : i < k) : s.nr 57+i < s.nr 58 := by
      have a := layout.candidatesAfter
      omega
    constructor
    · intro i hi
      rw [port 57, port 58]
      exact low i hi
    · intro i hi
      rw [port 57, ordinary _ (Or.inr (by have h := layout.representativesAfter; omega)) (low i hi), reps ⟨i, hi⟩]
      exact (rep ⟨i, hi⟩).isLt
  obtain ⟨e, scanSteps, scan, live, frame⟩ := rebuildMatchingActiveCacheBlock_footprint (s := start)
    rfl dLive one startsCache startsOffset startsReps
  have idsEnd : s.nr 58 + s.nr 61 ≤ s.nr 65 := by
    have h := cache.idsBefore
    have a := cache.recordsBefore
    omega
  refine ⟨_, frontSteps+scanSteps, front.append scan, live, ?_, ?_⟩
  · intro a high
    change e.nm a = s.nm a
    exact (frame.natural a (Or.inr (by rwa [port 65]))).trans (cleared.natural a
      (Or.inr (by omega)) (fun h => by have stop := h.2; omega) (fun h => (not_lt.mpr high) h.2.1))
  · intro a safe
    change e.rm a = s.rm a
    exact (frame.real a (by rwa [port 59, port 66])).trans (congrFun cleared.real a)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingWarmCacheFootprint

/-! matching/MatchingWarmSearch.lean -/
section RppSource_MatchingWarmSearch
namespace VehicleRoutingSurvey.Routing

/-- Warm preparation enters a fully decoded search: the cache contains exactly
the mathematical per-group minima, the new roots have no parent witnesses, and
the original matching, live representative IDs, and cut duals are preserved. -/
theorem warmMatchingPreparationBlock_search {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {oldForest : AlternatingForestState (Fin k)} {original s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (positive : 0 < k)
    (primal : CompactMatchingPrimalDualMemory state original s) (top : CompactTopMatching part)
    (old : MatchingSearchDualMemory part oldForest s)
    (warm : MatchingWarmLayout s k) (realPrefix : original.nr 64 ≤ s.nr 59)
    (nodeAfter : s.nr 65 + 2 * (k * k) ≤ s.nr 74) (cutAfter : s.nr 66 + k * k ≤ s.nr 75)
    (symmetric : ∀ a b, cost a b = cost b a)
    (nested : ∀ S ∈ state.cuts, ∀ a ∈ S, ∀ b ∈ S, part.blocks.block a = part.blocks.block b)
    (cutAt : Fin k → Finset (Fin k))
    (reads : MatchingRefreshInput s part.representative (fun v => alternatingRoleCode (oldForest.role v)) cost
      (effectiveVertexPotential state.cuts state.potential state.cutDual)) :
    let forest := resetAlternatingForest part.activeRepresentatives state.partialMate
    ∃ t ticks, ticks ≤ 104 * k * k + 48 * k + 31 ∧ BlockRuns warmMatchingPreparationBlock ticks s t ∧
      t.halted = false ∧ t.nr 31 = 6 * k + 1 ∧ t.nr 32 = 0 ∧ t.nr 33 = 1 ∧ t.nr 34 = 1 ∧
      t.nr 1 = 0 ∧ t.nr 9 = 1 ∧ t.rr 15 = 0 ∧
      CompactMatchingPrimalDualMemory state original t ∧
      CompactMatchingSearchForest part forest state.partialMate part.tightBetween ∧
      MatchingForestOriginalWitnesses part forest t ∧ MatchingSearchRows part forest positive cutAt t ∧
      (∃ dual : MatchingSearchDualMemory part forest t, dual.node = old.node) ∧
      MatchingRefreshInput t part.representative (fun v => alternatingRoleCode (forest.role v)) cost
        (effectiveVertexPotential state.cuts state.potential state.cutDual) ∧
      ∀ i < k * k, MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i =
        insertSlackCandidates ((List.finRange k).flatMap (warmSourcePairInputs part.representative
          (fun v => alternatingRoleCode (forest.role v)) cost
          (effectiveVertexPotential state.cuts state.potential state.cutDual) 0 i)) none := by
  intro forest
  have offsets (i : ℕ) (within : i < k) : s.nm (s.nr 21 + i) = k * i := reads.offsets ⟨i, within⟩
  obtain ⟨t, ticks, budget, run, live, _, limit, zero, active, one, id, unit, count,
    idBase, slackBase, rateBase, forestMemory, lowNat, lowReal, fixed⟩ :=
    warmMatchingPreparationBlock_runs entry running warm offsets part.mem_activeRepresentatives primal.partialMate_word old.reps
  obtain ⟨u, uTicks, _, uRun, _, time, readsNow, rows, buckets⟩ :=
    warmMatchingPreparationBlock_rows cutAt entry running warm reads part.mem_activeRepresentatives primal.partialMate_word
  have same := (uRun.same_exit run).2
  subst u
  obtain ⟨m, mTicks, mRun, _, highNat, highReal⟩ :=
    warmMatchingPreparationBlock_highFrame entry running warm reads.layout offsets part.mem_activeRepresentatives
      primal.partialMate_word old.reps
  have same := (mRun.same_exit run).2
  subst m
  have stable (r : ℕ) (low : 50 ≤ r := by decide) (away : r < 71 ∨ 73 < r := by decide) : t.nr r = s.nr r := fixed r low away
  have primalNow : CompactMatchingPrimalDualMemory state original t := by
    refine ⟨readsNow.layout.dimension, (stable 56).trans primal.oddMap, (stable 50).symm ▸ primal.mateAbove, ?_, ?_, ?_, ?_⟩
    · intro v
      rw [stable 50, lowNat _ (Nat.add_lt_add_left v.isLt _)]
      exact primal.mate v
    · intro r high
      exact (stable r (by omega) (Or.inr (by omega))).trans (primal.saved r high)
    · intro a ha
      exact (lowNat _ (by have above := primal.mateAbove; omega)).trans (primal.natural a ha)
    · intro a ha
      exact (lowReal _ (ha.trans_le realPrefix)).trans (primal.real a ha)
  let current : MatchingSearchDualMemory part forest t := {
    dimension := readsNow.layout.dimension
    separated := by rw [stable 62, stable 75]; exact old.separated
    reps := readsNow.representatives
    roles := (stable 51).symm ▸ forestMemory
    effective := readsNow.potentials
    node := old.node
    nodeNonzero := old.nodeNonzero
    nodeInjective := old.nodeInjective
    cutValues B present := by
      rw [stable 75, highReal _ (Or.inr (by omega))]
      exact old.cutValues B present
    top v := by
      unfold blossomNodeAt
      rw [stable 74, highNat _ (by omega)]
      exact old.top v }
  have table : MatchingSearchRows part forest positive cutAt t := by
    refine ⟨readsNow.layout, count.trans readsNow.layout.rows.symm, idBase, slackBase, rateBase, ?_, ?_⟩
    · intro i within
      exact (rows i (readsNow.layout.rows ▸ within)).1
    · exact warmMatchingRows_least part positive symmetric nested cutAt t (fun i hi => (rows i hi).2)
  exact ⟨t, ticks, budget, run, live, limit, zero, active, one, id, unit, time, primalNow,
    top.resetForest.2, resetAlternatingForest_has_no_parent_witnesses part t, table, ⟨current, rfl⟩, readsNow, buckets⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingWarmSearch

/-! matching/MatchingStageCutoff.lean -/
section RppSource_MatchingStageCutoff
namespace VehicleRoutingSurvey.Routing





theorem recordMatchingStageCutoff_runs (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    let t := {s with pc := 2, nr := Function.update s.nr 39 (s.nr 76)}
    BlockRuns recordMatchingStageCutoff 2 s t := by
  dsimp only
  apply BlockRuns.of_running_exit
  · simp [recordMatchingStageCutoff, arithmeticStep, entry, running, Function.iterate_succ_apply', Function.update_idem]
  · exact running
  · rfl

theorem prepareWeightedMatchingStageBlock_from_warm {s t : ArithmeticState} {steps : ℕ}
    (warm : BlockRuns warmMatchingPreparationBlock steps s t) (running : t.halted = false) :
    let u := {t with pc := warmMatchingPreparationBlock.length + 2, nr := Function.update t.nr 39 (t.nr 76)}
    BlockRuns prepareWeightedMatchingStageBlock (steps + 2) s u := by
  intro u
  let start := {t with pc := 0}
  have stamp := recordMatchingStageCutoff_runs start rfl running
  exact warm.append stamp


end VehicleRoutingSurvey.Routing
end RppSource_MatchingStageCutoff

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







end VehicleRoutingSurvey.Routing
end RppSource_MatchingPairMeaning

/-! matching/MatchingWarmPairMeaning.lean -/
section RppSource_MatchingWarmPairMeaning
namespace VehicleRoutingSurvey.Routing

theorem warmSourcePairInputs_mem {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (time : ℝ)
    (symmetric : ∀ u v, cost u v = cost v u) (labels : ∀ v, role v = 0 ∨ role v = 1)
    {a b : Fin k} (distinct : a ≠ b) (aOuter : role a = 1) (bOuter : role b = 1)
    (d : DualSlack (MatchingDualEvent k)) :
    d ∈ (List.finRange k).flatMap (warmSourcePairInputs rep role cost effective time (k*a.val+b.val)) ↔
      d ∈ normalizedOuterPairEntries rep cost effective time a b := by
  simp only [List.mem_flatMap, List.mem_finRange, true_and, normalizedOuterPairEntries_mem]
  constructor
  · rintro ⟨u, present⟩
    have outer : role (rep u) = 1 := by
      rcases labels (rep u) with off | on
      · simp [warmSourcePairInputs, off] at present
      · exact on
    simp only [warmSourcePairInputs, outer, one_ne_zero, if_false, List.mem_filterMap, List.mem_finRange, true_and] at present
    obtain ⟨v, found⟩ := present
    obtain ⟨_, ⟨_, coords⟩, datum⟩ := (outerRefreshPairInput_some_iff rep role cost effective time u v a b d).mp found
    rcases coords with ⟨left,right⟩ | ⟨left,right⟩
    · exact ⟨u, v, left.symm, right.symm, datum⟩
    · exact ⟨v, u, left.symm, right.symm, (normalizedOuterEdge_swap symmetric effective time v u).trans datum⟩
  · rintro ⟨u, v, hu, hv, found⟩
    refine ⟨u, ?_⟩
    have source : role (rep u) = 1 := by rwa [hu]
    simp only [warmSourcePairInputs, source, one_ne_zero, if_false]
    refine List.mem_filterMap.mpr ⟨v, List.mem_finRange v, ?_⟩
    apply (outerRefreshPairInput_some_iff rep role cost effective time u v a b d).mpr
    exact ⟨by rwa [hu,hv], ⟨by rwa [hv], Or.inl ⟨hu.symm,hv.symm⟩⟩, found⟩

theorem warmSourcePairInputs_inactive {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (time : ℝ)
    (idem : ∀ v, rep (rep v) = rep v) (labels : ∀ v, role v = 0 ∨ role v = 1)
    (a b : Fin k) (inactive : role (rep a) ≠ 1 ∨ role (rep b) ≠ 1) :
    (List.finRange k).flatMap (warmSourcePairInputs rep role cost effective time (k*a.val+b.val)) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro d present
  obtain ⟨u, _, atSource⟩ := List.mem_flatMap.mp present
  rcases labels (rep u) with off | on
  · simp [warmSourcePairInputs, off] at atSource
  · simp only [warmSourcePairInputs, on, one_ne_zero, if_false, List.mem_filterMap, List.mem_finRange,
      true_and] at atSource
    obtain ⟨v, offered⟩ := atSource
    obtain ⟨_, ⟨target, coords⟩, _⟩ := (outerRefreshPairInput_some_iff rep role cost effective time u v a b d).mp offered
    rcases coords with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [idem, on, target] at inactive

theorem warmMatchingPairBucket_least {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (time : ℝ)
    (symmetric : ∀ u v, cost u v = cost v u) (labels : ∀ v, role v = 0 ∨ role v = 1)
    {a b : Fin k} (distinct : a ≠ b) (aOuter : role a = 1) (bOuter : role b = 1)
    {winner : Option (DualSlack (MatchingDualEvent k))}
    (actual : winner = insertSlackCandidates
      ((List.finRange k).flatMap (warmSourcePairInputs rep role cost effective time (k*a.val+b.val))) none) :
    LeastSlackEntry (normalizedOuterPairEntries rep cost effective time a b) winner := by
  let entries := (List.finRange k).flatMap (warmSourcePairInputs rep role cost effective time (k*a.val+b.val))
  have empty : LeastSlackEntry ([] : List (DualSlack (MatchingDualEvent k))) none := by constructor <;> simp
  have least := empty.insert_many entries
  have membership (d : DualSlack (MatchingDualEvent k)) : d ∈ entries.reverse ++ [] ↔
      d ∈ normalizedOuterPairEntries rep cost effective time a b := by
    rw [List.append_nil, List.mem_reverse]
    exact warmSourcePairInputs_mem rep role cost effective time symmetric labels distinct aOuter bOuter d
  rw [actual]
  exact ⟨fun found => (membership _).mp (least.sound found), fun x found => least.covers x ((membership _).mpr found)⟩

theorem warmMatchingPairBuckets {k : ℕ} {s : ArithmeticState} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (time : ℝ)
    (idem : ∀ v, rep (rep v) = rep v) (clock : s.rr 15 = time) (symmetric : ∀ u v, cost u v = cost v u) (labels : ∀ v, role v = 0 ∨ role v = 1)
    (sweep : ∀ i < k*k, MatchingPairBucketValid k s i ∧ readMatchingPairBucket (k := k) s i =
      insertSlackCandidates ((List.finRange k).flatMap (warmSourcePairInputs rep role cost effective time i)) none) :
    MatchingSearchOuterBuckets s rep role cost effective := by
  refine ⟨fun i hi => (sweep i hi).1, ?_, ?_⟩
  · intro a b distinct left right
    rw [clock]
    exact warmMatchingPairBucket_least rep role cost effective time symmetric labels distinct left right
      (sweep _ (matchingPairSlot_lt a b)).2
  · intro a b off
    rw [(sweep _ (matchingPairSlot_lt a b)).2, warmSourcePairInputs_inactive rep role cost effective time idem labels a b off]
    rfl

end VehicleRoutingSurvey.Routing
end RppSource_MatchingWarmPairMeaning

/-! matching/MatchingFreshCutOuter.lean -/
section RppSource_MatchingFreshCutOuter
namespace VehicleRoutingSurvey.Routing



theorem MatchingFreshCutOuter.start {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState} {dual : MatchingSearchDualMemory part forest s}
    (registry : MatchingRegistryView dual) (stamp : s.nr 39 = s.nr 76) :
    MatchingFreshCutOuter part forest dual.node (s.nr 39) :=
  fun B present fresh => ((Nat.not_le.mpr (registry.allocated B present)) (stamp ▸ fresh)).elim







end VehicleRoutingSurvey.Routing
end RppSource_MatchingFreshCutOuter

/-! matching/MatchingStageEntry.lean -/
section RppSource_MatchingStageEntry
namespace VehicleRoutingSurvey.Routing



/-- The actual preparation establishes the search invariant and the measured
allocation budget, including the two instructions recording the cutoff. -/
theorem prepareWeightedMatchingStageBlock_registered {k stage : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {oldForest : AlternatingForestState (Fin k)} {original s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (positive : 0 < k)
    (primal : CompactMatchingPrimalDualMemory state original s) (top : CompactTopMatching part)
    (internal : state.InternalCuts) (old : MatchingSearchDualMemory part oldForest s)
    (registry : MatchingRegistryView old) (cursorLimit : s.nr 76 ≤ 6 * k * stage + 1)
    (warm : MatchingWarmLayout s k) (realPrefix : original.nr 64 ≤ s.nr 59)
    (nodeAfter : s.nr 65 + 2 * (k * k) ≤ s.nr 74) (cutAfter : s.nr 66 + k * k ≤ s.nr 75)
    (symmetric : ∀ a b, cost a b = cost b a) (cutAt : Fin k → Finset (Fin k))
    (reads : MatchingRefreshInput s part.representative (fun v => alternatingRoleCode (oldForest.role v)) cost
      (effectiveVertexPotential state.cuts state.potential state.cutDual)) :
    let forest := resetAlternatingForest part.activeRepresentatives state.partialMate
    ∃ t ticks, ticks ≤ 104 * k * k + 48 * k + 33 ∧ BlockRuns prepareWeightedMatchingStageBlock ticks s t ∧
      t.halted = false ∧ t.nr 31 = 6 * k + 1 ∧ t.nr 32 = 0 ∧ t.nr 33 = 1 ∧ t.nr 34 = 1 ∧
      t.nr 39 = s.nr 76 ∧ t.rr 15 = 0 ∧
      (∃ active : MatchingActiveStage part forest positive cutAt original stage t,
        active.dual.node = old.node ∧ active.registry.trees.tree = registry.trees.tree) ∧
      (∀ r, 50 ≤ r → r < 71 ∨ 73 < r → t.nr r = s.nr r) ∧
      (∀ a ≥ s.nr 65+2*(k*k), t.nm a = s.nm a) ∧
      (matchingStageCountsFromRAM k t (t.nr 39)).credit ≤ 6 * k := by
  intro forest
  obtain ⟨t, ticks, budget, run, live, limit, zero, active, one, id, unit, clock, primalNow, search, witnesses,
    rows, ⟨dual, sameIds⟩, readsNow, buckets⟩ := warmMatchingPreparationBlock_search entry running positive primal top old
      warm realPrefix nodeAfter cutAfter symmetric registry.nested cutAt reads
  have offsets (i : ℕ) (within : i < k) : s.nm (s.nr 21 + i) = k * i := reads.offsets ⟨i, within⟩
  obtain ⟨m, mTicks, _, mRun, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, regs⟩ :=
    warmMatchingPreparationBlock_runs entry running warm offsets part.mem_activeRepresentatives primal.partialMate_word old.reps
  have same := (mRun.same_exit run).2
  subst m
  obtain ⟨z, zTicks, zRun, _, natural, _⟩ := warmMatchingPreparationBlock_highFrame entry running warm reads.layout
    offsets part.mem_activeRepresentatives primal.partialMate_word old.reps
  have same := (zRun.same_exit run).2
  subst z
  let u := {t with pc := warmMatchingPreparationBlock.length + 2, nr := Function.update t.nr 39 (t.nr 76)}
  have stamp : BlockRuns prepareWeightedMatchingStageBlock (ticks + 2) s u :=
    prepareWeightedMatchingStageBlock_from_warm run live
  have port (r : ℕ) (away : r ≠ 39 := by decide) : u.nr r = t.nr r := Function.update_of_ne away _ _
  have saved (r : ℕ) (hi : 50 ≤ r := by decide) (away : r < 71 ∨ 73 < r := by decide) : u.nr r = s.nr r :=
    (port r (by omega)).trans (regs r hi away)
  have mate : CompactMatchingPrimalDualMemory state original u := by
    refine ⟨primalNow.dimension, primalNow.oddMap, primalNow.mateAbove, primalNow.mate, ?_, primalNow.natural, primalNow.real⟩
    intro r high
    exact (port r (by omega)).trans (primalNow.saved r high)
  let current : MatchingSearchDualMemory part forest u :=
    ⟨dual.dimension, dual.separated, dual.reps, dual.roles, dual.effective, dual.node,
      dual.nodeNonzero, dual.nodeInjective, dual.cutValues, dual.top⟩
  let registered : MatchingRegistryView current := registry.transport sameIds (saved 77) (saved 78)
    (saved 76) (saved 65) (fun v => by rw [current.top, old.top, sameIds]) natural
  have tables (r : ℕ) (used : r ∈ matchingRefreshTableRegisters) : u.nr r = t.nr r :=
    port r (by simp [matchingRefreshTableRegisters] at used; omega)
  have inputNow : MatchingRefreshInput u part.representative (fun v => alternatingRoleCode (forest.role v)) cost
      (effectiveVertexPotential state.cuts state.potential state.cutDual) :=
    readsNow.keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ tables
  have currentRows : MatchingSearchRows part forest positive cutAt u :=
    ⟨inputNow.layout, rows.count, rows.ids, rows.slacks, rows.rates, rows.valid, rows.least⟩
  have stampOK : u.nr 39 = u.nr 76 := by simp [u]
  have bounded := registered.starts_budget positive stampOK ((saved 76).trans_le cursorLimit)
  have labels (v : Fin k) : alternatingRoleCode (forest.role v) = 0 ∨ alternatingRoleCode (forest.role v) = 1 := by
    by_cases root : v ∈ part.activeRepresentatives ∧ state.partialMate v = none <;>
      simp [forest, resetAlternatingForest, root, alternatingRoleCode]
  have pairs := warmMatchingPairBuckets (s := u) part.representative _ cost _ 0
    part.representative_idem (show u.rr 15 = 0 from clock) symmetric labels
    (show ∀ i < k*k, MatchingPairBucketValid k u i ∧ _ from buckets)
  exact ⟨u, ticks + 2, by omega, stamp, live, limit, zero, active, one, regs 76 (by decide) (by decide), clock,
    ⟨⟨mate, top, internal, search, witnesses, MatchingForestLinkMemory.reset part u, current, registered,
      MatchingFreshCutOuter.start registered stampOK, currentRows, pairs, inputNow, bounded, id, unit⟩, sameIds, rfl⟩,
    (fun r hi away => saved r hi away), natural,
    registered.credit_le positive (u.nr 39)⟩




end VehicleRoutingSurvey.Routing
end RppSource_MatchingStageEntry

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

/-! matching/MatchingStageFrame.lean -/
section RppSource_MatchingStageFrame
namespace VehicleRoutingSurvey.Routing

/-- The inner and outer counted loops can reset their private counters
without changing the decoded matching, search forest, cache, or stage credit. -/
def MatchingActiveStage.reframe {k stage : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {cutAt : Fin k → Finset (Fin k)}
    {original s t : ArithmeticState} (active : MatchingActiveStage part forest positive cutAt original stage s)
    (natural : t.nm = s.nm) (real : t.rm = s.rm) (clock : t.rr 15 = s.rr 15)
    (regs : ∀ r, r ≠ 30 → r ≠ 40 → t.nr r = s.nr r) :
    MatchingActiveStage part forest positive cutAt original stage t := by
  have fixed (r : ℕ) (a : r ≠ 30 := by decide) (b : r ≠ 40 := by decide) := regs r a b
  have tables (r : ℕ) (mem : r ∈ matchingRefreshTableRegisters) : t.nr r = s.nr r :=
    fixed r (by simp [matchingRefreshTableRegisters] at mem; omega) (by simp [matchingRefreshTableRegisters] at mem; omega)
  have sameRows := (matchingCacheReads_unchanged cutAt natural real tables).1
  have samePairs := (matchingCacheReads_unchanged cutAt natural real tables).2
  have primal := active.primal
  have mate : CompactMatchingPrimalDualMemory state original t := by
    refine ⟨(fixed 55).trans primal.dimension, (fixed 56).trans primal.oddMap, ?_, ?_, ?_, ?_, ?_⟩
    · rw [fixed 50]; exact primal.mateAbove
    · intro v
      rw [fixed 50, natural]
      exact primal.mate v
    · intro r hi
      exact (fixed r (by omega) (by omega)).trans (primal.saved r hi)
    · intro a ha
      exact (congrFun natural a).trans (primal.natural a ha)
    · intro a ha
      exact (congrFun real a).trans (primal.real a ha)
  have reads := active.reads.keeps (t := t)
    ⟨fun a _ => congrFun natural a, fun a _ _ _ => congrFun real a⟩ tables
  have sameNode (v : Fin k) : blossomNodeAt t v = blossomNodeAt s v := by
    simp only [blossomNodeAt, fixed 74, natural]
  let dual : MatchingSearchDualMemory part forest t := {
    dimension := reads.layout.dimension
    separated := by rw [fixed 62, fixed 75]; exact active.dual.separated
    reps := reads.representatives
    roles := by rw [natural, fixed 51]; exact active.dual.roles
    effective := reads.potentials
    node := active.dual.node
    nodeNonzero := active.dual.nodeNonzero
    nodeInjective := active.dual.nodeInjective
    cutValues B present := by rw [fixed 75, real]; exact active.dual.cutValues B present
    top v := (sameNode v).trans (active.dual.top v) }
  let registry : MatchingRegistryView dual := active.registry.transport rfl (fixed 77) (fixed 78) (fixed 76)
    (fixed 65) sameNode (fun a _ => congrFun natural a)
  have newCounts := matchingStageCountsFromRAM_eq dual positive (t.nr 39) registry.trees registry.unique registry.keys
  have oldCounts := matchingStageCountsFromRAM_eq active.dual positive (s.nr 39) active.registry.trees
    active.registry.unique active.registry.keys
  have countEq : matchingStageCountsFromRAM k t (t.nr 39) = matchingStageCountsFromRAM k s (s.nr 39) := by
    rw [newCounts, oldCounts, fixed 39]
  have rows := active.rows
  have nowRows : MatchingSearchRows part forest positive cutAt t := by
    refine ⟨reads.layout, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [fixed 8, fixed 61]; exact rows.count
    · rw [fixed 3, fixed 58]; exact rows.ids
    · rw [fixed 4, fixed 59]; exact rows.slacks
    · rw [fixed 5, fixed 60]; exact rows.rates
    · intro i hi
      rw [(sameRows i).1]
      exact rows.valid i (fixed 61 ▸ hi)
    · intro group
      rw [(sameRows group.slot).2]
      exact rows.least group
  have kept (v : Fin k) : matchingForestWitnessAt t.nm (t.nr 90) v.val = matchingForestWitnessAt s.nm (s.nr 90) v.val := by
    rw [natural, fixed 90]
  refine ⟨mate, active.top, active.internal, active.search, ?_, active.links.advance rfl kept, dual, registry,
    ?_, nowRows, ?_, reads, ?_, (fixed 1).trans active.winnerEmpty, (fixed 9).trans active.unit⟩
  · intro child parent link
    simpa only [natural, fixed 90] using active.witnesses link
  · rw [fixed 39]; exact active.freshCuts
  · refine ⟨fun i hi => (samePairs i).1.symm ▸ active.pairs.valid i hi, ?_, ?_⟩
    · intro a b different first last
      rw [clock, (samePairs _).2]
      exact active.pairs.least a b different first last
    · intro a b off
      exact (samePairs _).2.trans (active.pairs.inactive a b off)
  · exact active.budget.keeps (fixed 39) (fixed 76) countEq


end VehicleRoutingSurvey.Routing
end RppSource_MatchingStageFrame

/-! matching/MatchingPreparedStage.lean -/
section RppSource_MatchingPreparedStage
namespace VehicleRoutingSurvey.Routing



set_option maxRecDepth 16384 in
theorem MatchingBetweenStages.prepare {k i : ℕ} {cost : Fin k → Fin k → ℝ} {original s : ArithmeticState}
    (old : MatchingBetweenStages cost original i (matchingLoopSnapshot s)) (before : i < k/2)
    (input : CompactMateInput cost original) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t steps, steps ≤ 104*k*k+48*k+33 ∧ BlockRuns prepareWeightedMatchingStageBlock steps s t ∧
      t.halted = false ∧ t.nr 31 = 6*k+1 ∧ t.nr 32 = 0 ∧ t.nr 33 = 1 ∧ t.nr 34 = 1 ∧
      Nonempty (MatchingPreparedStage cost original i (matchingStageSnapshot t)) ∧
      (matchingStageCountsFromRAM k (matchingStageSnapshot t) ((matchingStageSnapshot t).nr 39)).credit ≤ 6*k := by
  let prior := old.reframe (t := s) rfl rfl (fun r _ away => (Function.update_of_ne away _ _).symm)
  let g := prior.graph
  let layout := prior.storage
  have pos : 0 < k := by omega
  let cut := matchingTopCutAt g.part
  have floor := layout.inputFloor
  have prefixBound := prior.reads.effectiveBefore
  obtain ⟨t, steps, limit, run, live, size, zero, on, one, cutoff, clock, ⟨active, ids, tree⟩, highRegs, high, _⟩ :=
    prepareWeightedMatchingStageBlock_registered entry running pos g.primal g.top g.internal prior.dual prior.registry
      prior.cursor layout.warm (by omega) layout.nodes.ge layout.cutDuals.ge input.symmetric cut prior.reads
  let u := matchingStageSnapshot t
  have snap (r : ℕ) (away : r ≠ 30 := by decide) : u.nr r = t.nr r := Function.update_of_ne away _ _
  let current := active.reframe (t := u) rfl rfl rfl (fun r away _ => snap r away)
  have fixed (r : ℕ) (hi : 50 ≤ r := by decide) (range : r < 71 ∨ 73 < r := by decide) : u.nr r = s.nr r :=
    (snap r (by omega)).trans (highRegs r hi range)
  have lowPort (r : ℕ) (key : r ∈ ([20,21] : List ℕ)) : u.nr r = s.nr r := by
    apply (snap r (by simp at key; omega)).trans
    rw [← run.run]
    apply arithmeticRun_keeps_register _ s steps
    have checked : prepareWeightedMatchingStageBlock.all (fun ins => decide (naturalDestination ins ∉ ([20,21] : List ℕ))) = true := by decide
    intro ins mem equal
    exact (of_decide_eq_true (List.all_eq_true.mp checked ins mem)) (equal ▸ key)
  have nextLayout : MatchingStageStorage k original u := layout.keeps (fun r mem => by
    by_cases low : r ∈ ([20,21] : List ℕ)
    · exact lowPort r low
    · exact fixed r (by simp [matchingFixedStorageRegisters] at mem; simp at low; omega)
        (by simp [matchingFixedStorageRegisters] at mem; omega))
  let bound := s.nr 65+2*(k*k)
  have header : bound ≤ s.nr 77 := by have a := layout.nodes; have b := layout.starts; dsimp [bound]; omega
  have length : bound ≤ s.nr 78 := by have a := layout.lengths; omega
  have records : bound ≤ matchingRebaseScratchEnd s := by
    have a := layout.traceLeft
    have b := layout.traceRight
    have c := layout.traceMarks
    have d := layout.witnesses
    have e := layout.records
    have f := layout.promotion
    have g := layout.mask
    have h := layout.memberMap
    have j := layout.memberStack
    unfold matchingRebaseScratchEnd
    omega
  have physical (B : Finset (Fin k)) (h : B ∈ g.state.cuts) : MatchingLiveCycleMemory (prior.cycles.entry B h) u := by
    apply MatchingLiveCycleMemory.aboveFloor (s := s) (t := u) (floor := bound)
      (e := prior.cycles.entry B h) (prior.cycles.memory B h) prior.order header length records _ _ high
    · intro n hn
      rcases List.mem_cons.mp hn with head | tail
      · rw [head]
        exact ⟨Nat.pos_of_ne_zero (prior.dual.nodeNonzero B h),prior.registry.allocated B h⟩
      · obtain ⟨C,hc,id⟩ := (prior.registry.keys n).mp (prior.cycles.ids B h n tail)
        rw [← id]
        exact ⟨Nat.pos_of_ne_zero (prior.dual.nodeNonzero C hc),prior.registry.allocated C hc⟩
    · intro r mem
      exact fixed r (by simp at mem; omega) (by simp at mem; omega)
  have retained : MatchingLiveCycles current.registry := prior.cycles.sameNodes current.registry
    ((show current.dual.node = active.dual.node from rfl).trans ids)
    ((show current.registry.trees.tree = active.registry.trees.tree from rfl).trans tree) physical
  have base (n : ℕ) : matchingCycleRecordStart u n = matchingCycleRecordStart s n := by
    rw [matchingCycleRecordStart, fixed 77]; exact high _ (by omega)
  have ends (n : ℕ) : matchingCycleRecordEnd u n = matchingCycleRecordEnd s n := by
    have kept : u.nm (s.nr 78+n) = s.nm (s.nr 78+n) := high _ (length.trans (Nat.le_add_right _ _))
    simp only [matchingCycleRecordEnd, base, fixed 78, kept]
  have order := prior.order.transport (t := u) (by simp [matchingRebaseScratchEnd,fixed 80,fixed 55])
    (fixed 76) (fixed 68) (fun n _ _ => base n) (fun n _ _ => ends n)
  exact ⟨t,steps,limit,run,live,size,zero,on,one,
    ⟨⟨g.state,g.part,_,pos,g.count,current,retained,nextLayout,order⟩⟩,
    current.registry.credit_le pos (u.nr 39)⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingPreparedStage

open VehicleRoutingSurvey.Routing SupplyChainTheory in
theorem solution : (fun {P : Prop} (_ : P) => P) (@VehicleRoutingSurvey.Routing.MatchingBetweenStages.prepare) :=
  @VehicleRoutingSurvey.Routing.MatchingBetweenStages.prepare
