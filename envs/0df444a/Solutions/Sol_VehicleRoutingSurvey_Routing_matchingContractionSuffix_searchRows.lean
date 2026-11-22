-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.matchingContractionSuffix_searchRows
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T16:00:33.826813+00:00
-- url     : https://prove2.me/submissions/2801841f-da5e-4cf0-aba7-4a3ab147fe3e

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces

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





































end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowCacheRAM

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

















end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractHandler

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

/-! matching/MatchingContractPublishRows.lean -/
section RppSource_MatchingContractPublishRows
namespace VehicleRoutingSurvey.Routing

theorem publishMinimumContractedBucket_empty (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (empty : s.nr 1 = 0) :
    ∃ t, BlockRuns publishMinimumContractedBucket 4 s t ∧ t.halted = false ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧ t.nr 14 = 0 ∧ t.nr 23 = 0 ∧
      ∀ r, r ≠ 14 → r ≠ 23 → t.nr r = s.nr r := by
  let seeded := {s with pc := 2, nr := Function.update (Function.update s.nr 23 0) 14 0}
  have seed : BlockRuns [.natConst 23 0, .natConst 14 0] 2 s seeded := by
    apply BlockRuns.of_running_exit
    · simp [seeded, arithmeticStep, entry, running, Function.iterate_succ_apply']
    · exact running
    · rfl
  let a := {seeded with pc := 0}
  have same : a.nr 1 = a.nr 23 := by simp [a, seeded, empty]
  have skip := branchOnUnequal_skip 1 23 (appendBlock readMinimumContractedBucket insertMatchingOuterEdgeBlock) a rfl running same
  refine ⟨_, seed.append skip, running, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · change a.nr 14 = 0
    simp [a, seeded]
  · change a.nr 23 = 0
    simp [a, seeded]
  · intro r no14 no23
    change a.nr r = _
    simp [a, seeded, Function.update_of_ne no14, Function.update_of_ne no23]

set_option maxRecDepth 4096 in
/-- Publish the witnessed old minimum in both new directed buckets and both
selector rows. The old key is reused exactly while its raw slack is recovered. -/
theorem publishMinimumContractedBucket_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} {u v src dst : Fin k} (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 9 = 1) (named : s.nr 1 ≠ 0) (layout : MatchingCacheLayout k s)
    (merged : s.nr 26 = src.val) (retained : s.nr 17 = dst.val) (distinct : src ≠ dst)
    (fromPort : s.nm (s.nr 65 + ((s.nr 1 - 1) + (s.nr 1 - 1))) = u.val)
    (toPort : s.nm (s.nr 65 + ((s.nr 1 - 1) + (s.nr 1 - 1)) + 1) = v.val)
    (offsets : ∀ x : Fin k, s.nm (s.nr 21 + x.val) = k * x.val)
    (offsetsBefore : s.nr 21 + k ≤ s.nr 58)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k * k, MatchingPairBucketValid k s i) :
    let raw : DualSlack (MatchingDualEvent k) := ⟨.edge s(u, v), s.rr 1 - (s.rr 15 + s.rr 15), 2⟩
    let keyed : DualSlack (MatchingDualEvent k) := ⟨.edge s(u, v), s.rr 1, 2⟩
    ∃ t ticks, ticks ≤ 85 ∧ BlockRuns publishMinimumContractedBucket ticks s t ∧ t.halted = false ∧
      MatchingCacheLayout k t ∧ (∀ r ≥ 24, t.nr r = s.nr r) ∧ t.rr 15 = s.rr 15 ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧
        readMatchingCandidate cutAt t i = if i = src.val ∨ i = dst.val then
          insertSlackCandidate raw (readMatchingCandidate cutAt s i) else readMatchingCandidate cutAt s i) ∧
      (∀ i < k * k, MatchingPairBucketValid k t i ∧
        readMatchingPairBucket (k := k) t i = if i = k * src.val + dst.val ∨ i = k * dst.val + src.val then
          insertSlackCandidate keyed (readMatchingPairBucket (k := k) s i) else readMatchingPairBucket (k := k) s i) := by
  intro raw keyed
  let seeded := {s with pc := 2, nr := Function.update (Function.update s.nr 23 0) 14 0}
  have seed : BlockRuns [.natConst 23 0, .natConst 14 0] 2 s seeded := by
    apply BlockRuns.of_running_exit
    · simp [seeded, arithmeticStep, entry, running, Function.iterate_succ_apply']
    · exact running
    · rfl
  let a := {seeded with pc := 0}
  have aFixed (r : ℕ) (away23 : r ≠ 23 := by decide) (away14 : r ≠ 14 := by decide) : a.nr r = s.nr r := by
    simp [a, seeded, Function.update_of_ne away23, Function.update_of_ne away14]
  have aOne : a.nr 9 = 1 := (aFixed 9).trans one
  have different : a.nr 1 ≠ a.nr 23 := by simpa [a, seeded] using named
  obtain ⟨read, fetch, readLive, readNat, readReal, decodedFirst, decodedSecond, readSlack, readTime, readFixed⟩ :=
    readMinimumContractedBucket_spec a rfl running aOne
  let b := {read with pc := 0}
  have unchanged (r : ℕ) (safe : r ∉ [0, 6, 15, 16, 18, 23, 14] := by decide) : b.nr r = s.nr r :=
    (readFixed r (by simp at safe ⊢; omega)).trans (aFixed r (by simp at safe; omega) (by simp at safe; omega))
  have bNat : b.nm = s.nm := readNat
  have bReal : b.rm = s.rm := readReal
  have bSlack : b.rr 0 = s.rr 1 - (s.rr 15 + s.rr 15) := readSlack
  have bTime : b.rr 15 = s.rr 15 := readTime
  have bZero : b.nr 14 = 0 := (readFixed 14 (by decide)).trans (by simp [a, seeded])
  have bLayout : MatchingCacheLayout k b := layout.keeps (fun r high => unchanged r (by simp; omega))
  have bFirst : b.nr 15 = u.val := by
    have rawPort := decodedFirst
    rw [aFixed 65, aFixed 1] at rawPort
    exact rawPort.trans fromPort
  have bSecond : b.nr 16 = v.val := by
    have rawPort := decodedSecond
    rw [aFixed 65, aFixed 1] at rawPort
    exact rawPort.trans toPort
  have bOffset (x : Fin k) : b.nm (b.nr 21 + x.val) = k * x.val := by
    rw [bNat, unchanged 21]
    exact offsets x
  have bRows (i : ℕ) (hi : i < b.nr 61) : MatchingCandidateRowValid cutAt b i := by
    have atStart : i < s.nr 61 := by rwa [unchanged 61] at hi
    simpa only [MatchingCandidateRowValid, decodeMatchingDictionaryEvent, bNat, unchanged 58, unchanged 54] using rows i atStart
  have bBuckets (i : ℕ) (hi : i < k * k) : MatchingPairBucketValid k b i := by
    simpa only [MatchingPairBucketValid, bNat, unchanged 65] using buckets i hi
  obtain ⟨t, ticks, bound, insert, live, endLayout, endFixed, time, endRows, endBuckets⟩ :=
    insertMatchingOuterEdgeBlock_rows cutAt (s := b) rfl readLive ((unchanged 9).trans one) bZero bLayout
      ((unchanged 26).trans merged) ((unchanged 17).trans retained) distinct bFirst bSecond bOffset
      (by rwa [unchanged 21, unchanged 58]) bRows bBuckets
  let body := appendBlock readMinimumContractedBucket insertMatchingOuterEdgeBlock
  have routed := branchOnUnequal_take 1 23 body (s := a) rfl running different (fetch.append insert)
  have ran : BlockRuns publishMinimumContractedBucket (2 + (2 + (8 + ticks))) s _ := seed.append routed
  have keyValue : b.rr 15 + b.rr 15 + b.rr 0 = s.rr 1 := by rw [bTime, bSlack]; ring
  refine ⟨_, _, by omega, ran, live, ?_, ?_, time.2.trans bTime, ?_, ?_⟩
  · constructor <;> first
      | exact endLayout.dimension | exact endLayout.rows | exact endLayout.idsBefore
      | exact endLayout.recordsBefore | exact endLayout.slacksBefore | exact endLayout.ratesBefore
  · intro r high
    exact (endFixed r (by omega) (by omega)).trans (unchanged r (by simp; omega))
  · intro i hi
    have inside : i < b.nr 61 := by rwa [unchanged 61]
    have candidate : readMatchingCandidate cutAt b i = readMatchingCandidate cutAt s i := by
      simp only [readMatchingCandidate, decodeMatchingDictionaryEvent, bNat, bReal, unchanged 54, unchanged 58,
        unchanged 59, unchanged 60]
    change MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i = _
    simpa only [candidate, bSlack, raw] using endRows i inside
  · intro i hi
    have bucket : readMatchingPairBucket (k := k) b i = readMatchingPairBucket (k := k) s i := by
      simp only [readMatchingPairBucket, bNat, bReal, unchanged 65, unchanged 66]
    change MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i = _
    simpa only [bucket, keyValue, keyed] using endBuckets i hi

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractPublishRows

/-! matching/MatchingContractCacheSemantics.lean -/
section RppSource_MatchingContractCacheSemantics
namespace VehicleRoutingSurvey.Routing

def readContractedBucketWinner {k : ℕ} (s : ArithmeticState) (code : ℕ) :
    Option (DualSlack (MatchingDualEvent k)) :=
  if code = 0 then none else readMatchingPairBucket s (code - 1)

private theorem decodeContractedBucket {k : ℕ} (s : ArithmeticState) (size : s.nr 55 = k) (i : ℕ)
    (valid : MatchingPairBucketValid k s (contractedBucketIndex s i)) :
    (contractedBucketCode s i = 0 ∧ readMatchingPairBucket (k := k) s (contractedBucketIndex s i) = none) ∨
    ∃ d : DualSlack (MatchingDualEvent k), contractedBucketCode s i = contractedBucketIndex s i + 1 ∧
      readMatchingPairBucket s (contractedBucketIndex s i) = some d ∧ d.slack = contractedBucketSlack s i := by
  let slot := contractedBucketIndex s i
  let address := s.nr 65 + (slot + slot)
  by_cases existsFirst : s.nm address < k
  · have existsSecond : s.nm (address + 1) < k := valid existsFirst
    let d : DualSlack (MatchingDualEvent k) :=
      ⟨.edge s(⟨s.nm address, existsFirst⟩, ⟨s.nm (address + 1), existsSecond⟩), contractedBucketSlack s i, 2⟩
    refine .inr ⟨d, ?_, ?_, rfl⟩
    · change (if s.nr 55 ≤ s.nm address then 0 else slot + 1) = slot + 1
      rw [size, if_neg (Nat.not_le.mpr existsFirst)]
    · change (if ha : s.nm address < k then
          if hb : s.nm (address + 1) < k then some (⟨.edge s(⟨s.nm address, ha⟩,
            ⟨s.nm (address + 1), hb⟩), contractedBucketSlack s i, 2⟩ : DualSlack (MatchingDualEvent k)) else none
          else none) = some d
      rw [dif_pos existsFirst, dif_pos existsSecond]
  · refine .inl ⟨?_, ?_⟩
    · change (if s.nr 55 ≤ s.nm address then 0 else slot + 1) = 0
      rw [size, if_pos (Nat.le_of_not_gt existsFirst)]
    · unfold readMatchingPairBucket
      exact dif_neg existsFirst

/-- The actual code-and-score characteristic of the minimum scan selects a least
stored bucket in the specified column. Caches use the common normalized score. -/
theorem ContractedBucketMinimum.leastDecoded {k : ℕ} {s : ArithmeticState} {seen code : ℕ} {score : ℝ}
    (minimum : ContractedBucketMinimum s seen code score) (size : s.nr 55 = k)
    (valid : ∀ j < seen, MatchingPairBucketValid k s (contractedBucketIndex s j)) :
    LeastSlackEntry ((List.range seen).filterMap (fun j => readMatchingPairBucket (k := k) s (contractedBucketIndex s j)))
      (readContractedBucketWinner (k := k) s code) := by
  rcases minimum with ⟨empty, allEmpty⟩ | ⟨i, hi, nonempty, identified, raw, wins⟩
  · have noWinner : readContractedBucketWinner (k := k) s code = none := by simp [readContractedBucketWinner, empty]
    constructor
    · rw [noWinner]
      simp
    · intro rival present
      obtain ⟨j, inRange, stored⟩ := List.mem_filterMap.mp present
      have inside := List.mem_range.mp inRange
      rcases decodeContractedBucket s size j (valid j inside) with ⟨_, vacant⟩ | ⟨_, positive, _, _⟩
      · rw [vacant] at stored
        contradiction
      · have impossible := (allEmpty j inside).symm.trans positive
        omega
  · rcases decodeContractedBucket s size i (valid i hi) with ⟨noCode, _⟩ | ⟨chosen, chosenCode, chosenRead, chosenScore⟩
    · exact (nonempty noCode).elim
    have step : code = contractedBucketIndex s i + 1 := identified.trans chosenCode
    have named : readContractedBucketWinner (k := k) s code = some chosen := by
      simp [readContractedBucketWinner, step, chosenRead]
    constructor
    · intro actual atWinner
      have same := Option.some.inj (named.symm.trans atWinner)
      subst actual
      exact List.mem_filterMap.mpr ⟨i, List.mem_range.mpr hi, chosenRead⟩
    · intro rival present
      obtain ⟨j, inRange, stored⟩ := List.mem_filterMap.mp present
      have inside := List.mem_range.mp inRange
      rcases decodeContractedBucket s size j (valid j inside) with ⟨_, vacant⟩ | ⟨other, otherCode, otherRead, otherScore⟩
      · rw [vacant] at stored
        contradiction
      · have same := Option.some.inj (otherRead.symm.trans stored)
        subst rival
        have positive : contractedBucketCode s j ≠ 0 := by rw [otherCode]; omega
        exact ⟨chosen, named, by rw [chosenScore, otherScore, ← raw]; exact wins j inside positive⟩

/-- A physical scan of the old bucket minima gives a least entry over the union
of all original edges covered by its absorbed outer rows. -/
theorem ContractedBucketMinimum.leastMerged {k : ℕ} {s : ArithmeticState} {seen code : ℕ} {score : ℝ}
    (minimum : ContractedBucketMinimum s seen code score) (size : s.nr 55 = k)
    (valid : ∀ j < seen, MatchingPairBucketValid k s (contractedBucketIndex s j))
    (full : ℕ → List (DualSlack (MatchingDualEvent k)))
    (old : ∀ i < seen, LeastSlackEntry (full i) (readMatchingPairBucket (k := k) s (contractedBucketIndex s i))) :
    LeastSlackEntry ((List.range seen).flatMap full) (readContractedBucketWinner (k := k) s code) := by
  have best := minimum.leastDecoded size valid
  constructor
  · intro chosen named
    obtain ⟨i, counted, represented⟩ := List.mem_filterMap.mp (best.sound named)
    exact List.mem_flatMap.mpr ⟨i, counted, (old i (List.mem_range.mp counted)).sound represented⟩
  · intro candidate included
    obtain ⟨i, counted, inside⟩ := List.mem_flatMap.mp included
    obtain ⟨oldBest, stored, close⟩ := (old i (List.mem_range.mp counted)).covers candidate inside
    obtain ⟨chosen, named, least⟩ := best.covers oldBest (List.mem_filterMap.mpr ⟨i, counted, stored⟩)
    exact ⟨chosen, named, least.trans close⟩

theorem ContractedBucketMinimum.winner_key {s : ArithmeticState} {seen code : ℕ} {score : ℝ}
    (minimum : ContractedBucketMinimum s seen code score) (nonempty : code ≠ 0) :
    score = s.rm (s.nr 66 + (code - 1)) := by
  rcases minimum with ⟨empty, _⟩ | ⟨i, _, chosen, atCode, exactScore, _⟩
  · exact (nonempty empty).elim
  let slot := contractedBucketIndex s i
  have present : ¬s.nr 55 ≤ s.nm (s.nr 65 + (slot + slot)) := by
    intro empty
    apply chosen
    change (if s.nr 55 ≤ s.nm (s.nr 65 + (slot + slot)) then 0 else slot + 1) = 0
    rw [if_pos empty]
  have selected : code = slot + 1 := by
    change code = (if s.nr 55 ≤ s.nm (s.nr 65 + (slot + slot)) then 0 else slot + 1) at atCode
    rwa [if_neg present] at atCode
  rw [selected, Nat.add_sub_cancel, exactScore] <;> rfl

theorem ContractedBucketMinimum.winner_ports {k : ℕ} {s : ArithmeticState} {seen code : ℕ} {score : ℝ}
    (minimum : ContractedBucketMinimum s seen code score) (size : s.nr 55 = k) (nonempty : code ≠ 0)
    (valid : ∀ j < seen, MatchingPairBucketValid k s (contractedBucketIndex s j)) :
    ∃ u v : Fin k,
      s.nm (s.nr 65 + ((code - 1) + (code - 1))) = u.val ∧
      s.nm (s.nr 65 + ((code - 1) + (code - 1)) + 1) = v.val ∧
      readContractedBucketWinner (k := k) s code = some ⟨.edge s(u, v), score, 2⟩ := by
  have key := minimum.winner_key nonempty
  rcases minimum with ⟨empty, _⟩ | ⟨i, hi, present, exactCode, _, _⟩
  · exact (nonempty empty).elim
  let slot := contractedBucketIndex s i
  let addr := s.nr 65 + (slot + slot)
  have first : s.nm addr < k := by
    by_contra h
    apply present
    change (if s.nr 55 ≤ s.nm addr then 0 else slot + 1) = 0
    rw [size, if_pos (Nat.le_of_not_gt h)]
  have second : s.nm (addr + 1) < k := valid i hi first
  have selected : code = slot + 1 := by
    change code = (if s.nr 55 ≤ s.nm addr then 0 else slot + 1) at exactCode
    rwa [size, if_neg (Nat.not_le.mpr first)] at exactCode
  have index : code - 1 = slot := by rw [selected, Nat.add_sub_cancel]
  refine ⟨⟨s.nm addr, first⟩, ⟨s.nm (addr + 1), second⟩, ?_, ?_, ?_⟩
  · rw [index] <;> rfl
  · rw [index] <;> rfl
  · rw [readContractedBucketWinner, if_neg nonempty, index, key, index]
    unfold readMatchingPairBucket
    exact (dif_pos first).trans (dif_pos second)

/-- Publishing a completed contraction column leaves every other old column
available for later scans. The reverse-direction update uses a surviving row,
which is outside the set of absorbed rows. -/
theorem contractionBucket_futureColumn_untouched {k : ℕ} (absorbed : Finset (Fin k))
    {merged oldRow completed pending : Fin k} (old : oldRow ∈ absorbed)
    (survives : completed ∉ absorbed) (different : completed ≠ pending) :
    k * oldRow.val + pending.val ≠ k * merged.val + completed.val ∧
    k * oldRow.val + pending.val ≠ k * completed.val + merged.val := by
  constructor
  · intro same
    exact different (Fin.ext ((denseMatrixOffset_eq_iff pending.isLt completed.isLt).mp same).2.symm)
  · intro same
    have eq : oldRow = completed := Fin.ext ((denseMatrixOffset_eq_iff pending.isLt merged.isLt).mp same).1
    exact survives (eq ▸ old)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractCacheSemantics

/-! matching/MatchingContractColumnRows.lean -/
section RppSource_MatchingContractColumnRows
namespace VehicleRoutingSurvey.Routing

def matchingContractionColumnInput (s : ArithmeticState) : ArithmeticState :=
  {s with pc := 0, nr := Function.update s.nr 17 (s.nr 24 + s.nr 23)}



set_option maxRecDepth 4096 in
/-- Scan the absorbed outer rows for one surviving block, then publish the
minimum. Both updates use that same stored winning edge, including ties. -/
theorem writeMergedBucketForOuter_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} {merged outside : Fin k} (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 9 = 1) (zero : s.nr 23 = 0) (layout : MatchingCacheLayout k s)
    (mergedAt : s.nr 26 = merged.val) (outsideAt : s.nr 24 = outside.val) (distinct : merged ≠ outside)
    (offsets : ∀ x : Fin k, s.nm (s.nr 21 + x.val) = k * x.val) (offsetsBefore : s.nr 21 + k ≤ s.nr 58)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k * k, MatchingPairBucketValid k s i)
    (oldRowValid : ∀ j < s.nr 87, s.nm (s.nr 86 + j) < k)
    (full : ℕ → List (DualSlack (MatchingDualEvent k)))
    (minima : ∀ j < s.nr 87, LeastSlackEntry (full j)
      (readMatchingPairBucket (k := k) s (contractedBucketIndex (matchingContractionColumnInput s) j))) :
    ∃ t ticks winner, ticks ≤ 22 * s.nr 87 + 89 ∧ BlockRuns writeMergedBucketForOuter ticks s t ∧ t.halted = false ∧
      MatchingCacheLayout k t ∧ (∀ r ≥ 24, t.nr r = s.nr r) ∧ t.rr 15 = s.rr 15 ∧
      LeastSlackEntry ((List.range (s.nr 87)).flatMap full) winner ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧
        readMatchingCandidate cutAt t i = if i = merged.val ∨ i = outside.val then
          addContractionWinner (fun d => {d with slack := d.slack - (s.rr 15 + s.rr 15)}) winner
            (readMatchingCandidate cutAt s i) else readMatchingCandidate cutAt s i) ∧
      (∀ i < k * k, MatchingPairBucketValid k t i ∧
        readMatchingPairBucket (k := k) t i = if i = k * merged.val + outside.val ∨ i = k * outside.val + merged.val then
          addContractionWinner id winner (readMatchingPairBucket (k := k) s i) else readMatchingPairBucket (k := k) s i) := by
  let a := matchingContractionColumnInput s
  let setup := {a with pc := 1}
  have load : BlockRuns [.natAdd 17 24 23] 1 s setup := by
    apply BlockRuns.of_running_exit
    · simp [a, setup, matchingContractionColumnInput, arithmeticStep, entry, running]
    · exact running
    · rfl
  have aKeep (r : ℕ) (away : r ≠ 17 := by decide) : a.nr r = s.nr r := by simp [a, matchingContractionColumnInput, away]
  have aColumn : a.nr 17 = outside.val := by simp [a, matchingContractionColumnInput, zero, outsideAt]
  have aOne : a.nr 9 = 1 := (aKeep 9).trans one
  have aSize : a.nr 55 = k := (aKeep 55).trans layout.dimension
  have aCount : a.nr 87 = s.nr 87 := aKeep 87
  obtain ⟨minimum, selectTicks, selectCost, choose, chosenLive, best, minNat, minReal⟩ :=
    minimumContractedBucket_spec a rfl running aOne
  let b := {minimum with pc := 0}
  have keeps (r : ℕ) (away : r ∉ [0, 1, 2, 6, 7, 10, 11] := by decide) : b.nr r = a.nr r := by
    change minimum.nr r = _
    rw [← choose.run]
    exact arithmeticRun_keeps_from_destination_list _ (by decide) away a selectTicks
  have fixed (r : ℕ) (safe : r ∉ [0, 1, 2, 6, 7, 10, 11, 17] := by decide) : b.nr r = s.nr r :=
    (keeps r (by simp at safe ⊢; omega)).trans (aKeep r (by simp at safe; omega))
  have bNat : b.nm = s.nm := minNat
  have bReal : b.rm = s.rm := minReal
  have bTime : b.rr 15 = s.rr 15 := choose.keeps_cache_real (by decide)
  have bLayout : MatchingCacheLayout k b := layout.keeps (fun r hr => fixed r (by simp; omega))
  have oldValid (j : ℕ) (hj : j < a.nr 87) : MatchingPairBucketValid k a (contractedBucketIndex a j) := by
    have inRows : j < s.nr 87 := aCount ▸ hj
    let r : Fin k := ⟨s.nm (s.nr 86 + j), oldRowValid j inRows⟩
    have addr : contractedBucketIndex a j = k * r.val + outside.val := by
      simp only [contractedBucketIndex, aKeep 21, aKeep 86, aColumn, show a.nm = s.nm from rfl]
      exact congrArg (· + outside.val) (offsets r)
    have used : contractedBucketIndex a j < k * k := by
      rw [addr]
      have space := Nat.mul_le_mul_left k (Nat.succ_le_of_lt r.isLt)
      rw [Nat.mul_succ] at space
      have upper := outside.isLt
      omega
    simpa only [MatchingPairBucketValid, aKeep 65, show a.nm = s.nm from rfl] using buckets _ used
  let winner := readContractedBucketWinner (k := k) a (b.nr 1)
  have oldMinimum : LeastSlackEntry ((List.range (s.nr 87)).flatMap full) winner := by
    have least := best.leastMerged aSize oldValid full (fun j hj => by
      have inRows : j < s.nr 87 := aCount ▸ hj
      exact minima j inRows)
    simpa only [aCount, winner] using least
  have bCandidate (i : ℕ) : readMatchingCandidate cutAt b i = readMatchingCandidate cutAt s i := by
    simp only [readMatchingCandidate, decodeMatchingDictionaryEvent, bNat, bReal, fixed 54, fixed 58, fixed 59, fixed 60]
  have bBucket (i : ℕ) : readMatchingPairBucket (k := k) b i = readMatchingPairBucket (k := k) s i := by
    simp only [readMatchingPairBucket, bNat, bReal, fixed 65, fixed 66]
  have bRows (i : ℕ) (hi : i < b.nr 61) : MatchingCandidateRowValid cutAt b i := by
    rw [fixed 61] at hi
    simpa only [MatchingCandidateRowValid, decodeMatchingDictionaryEvent, bNat, fixed 54, fixed 58] using rows i hi
  have bBuckets (i : ℕ) (hi : i < k*k) : MatchingPairBucketValid k b i := by
    simpa only [MatchingPairBucketValid, bNat, fixed 65] using buckets i hi
  rw [aCount] at selectCost
  by_cases absent : b.nr 1 = 0
  · obtain ⟨t, skipped, live, natSame, realSame, regsSame, _, _, kept⟩ :=
      publishMinimumContractedBucket_empty b rfl chosenLive absent
    have run : BlockRuns writeMergedBucketForOuter (1 + (selectTicks + 4)) s _ := load.append (choose.append skipped)
    have keepHigh (r : ℕ) (high : 24 ≤ r) : t.nr r = s.nr r :=
      (kept r (by omega) (by omega)).trans (fixed r (by simp; omega))
    have tLayout : MatchingCacheLayout k t := layout.keeps (fun r high => keepHigh r (by omega))
    have noWinner : winner = none := by simp [winner, readContractedBucketWinner, absent]
    refine ⟨_, _, winner, by omega, run, live, ?_, keepHigh, (congrFun regsSame 15).trans bTime, oldMinimum, ?_, ?_⟩
    · constructor <;> first
        | exact tLayout.dimension | exact tLayout.rows | exact tLayout.idsBefore
        | exact tLayout.recordsBefore | exact tLayout.slacksBefore | exact tLayout.ratesBefore
    · intro i hi
      change MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i = _
      have val : MatchingCandidateRowValid cutAt t i := by
        simpa only [MatchingCandidateRowValid, decodeMatchingDictionaryEvent, natSame, bNat, keepHigh 54 (by decide),
          keepHigh 58 (by decide)] using rows i hi
      refine ⟨val, ?_⟩
      by_cases updated : i = merged.val ∨ i = outside.val <;>
        simp [updated, noWinner, addContractionWinner, readMatchingCandidate, decodeMatchingDictionaryEvent,
          natSame, bNat, realSame, bReal, keepHigh 54 (by decide), keepHigh 58 (by decide),
          keepHigh 59 (by decide), keepHigh 60 (by decide)]
    · intro i hi
      change MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i = _
      have val : MatchingPairBucketValid k t i := by
        simpa only [MatchingPairBucketValid, natSame, bNat, keepHigh 65 (by decide)] using buckets i hi
      refine ⟨val, ?_⟩
      by_cases updated : i = k * merged.val + outside.val ∨ i = k * outside.val + merged.val <;>
        simp [updated, noWinner, addContractionWinner, readMatchingPairBucket, natSame, bNat, realSame, bReal,
          keepHigh 65 (by decide), keepHigh 66 (by decide)]
  · obtain ⟨u, v, first, second, typedWinner⟩ := best.winner_ports aSize absent oldValid
    have bFirst : b.nm (b.nr 65 + ((b.nr 1 - 1) + (b.nr 1 - 1))) = u.val := by
      simpa only [bNat, fixed 65, aKeep 65, show a.nm = s.nm from rfl, show b.nr 1 = minimum.nr 1 from rfl] using first
    have bSecond : b.nm (b.nr 65 + ((b.nr 1 - 1) + (b.nr 1 - 1)) + 1) = v.val := by
      simpa only [bNat, fixed 65, aKeep 65, show a.nm = s.nm from rfl, show b.nr 1 = minimum.nr 1 from rfl] using second
    have rawWinner : winner = some ⟨.edge s(u, v), b.rr 1, 2⟩ := typedWinner
    obtain ⟨t, ticks, bound, publish, live, tLayout, tFixed, time, candidates, pairs⟩ :=
      publishMinimumContractedBucket_rows cutAt (s := b) rfl chosenLive ((fixed 9).trans one) absent bLayout
        ((fixed 26).trans mergedAt) ((keeps 17).trans aColumn) distinct bFirst bSecond
        (by intro v; rw [bNat, fixed 21]; exact offsets v) (by rwa [fixed 21, fixed 58]) bRows bBuckets
    have run : BlockRuns writeMergedBucketForOuter (1 + (selectTicks + ticks)) s _ := load.append (choose.append publish)
    have keepHigh (r : ℕ) (high : 24 ≤ r) : t.nr r = s.nr r :=
      (tFixed r high).trans (fixed r (by simp; omega))
    refine ⟨_, _, winner, by omega, run, live, ?_, keepHigh, time.trans bTime, oldMinimum, ?_, ?_⟩
    · constructor <;> first
        | exact tLayout.dimension | exact tLayout.rows | exact tLayout.idsBefore
        | exact tLayout.recordsBefore | exact tLayout.slacksBefore | exact tLayout.ratesBefore
    · intro i hi
      have small : i < b.nr 61 := by rwa [fixed 61]
      change MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i = _
      simpa only [rawWinner, bTime, addContractionWinner, Option.map_some, Option.elim_some, bCandidate] using candidates i small
    · intro i hi
      change MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i = _
      simpa only [rawWinner, addContractionWinner, Option.map_some, Option.elim_some, id_eq, bBucket] using pairs i hi

/-- Repair one live outer column. Before the minimum scan the actual handler
checks the current label and skips the merged block's own column. -/
theorem repairMergedBucketForColumn_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} {merged outside : Fin k} (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 9 = 1) (zero : s.nr 23 = 0) (layout : MatchingCacheLayout k s)
    (mergedAt : s.nr 26 = merged.val) (outsideAt : s.nr 24 = outside.val) (distinct : merged ≠ outside)
    (outer : s.nm (s.nr 51 + outside.val) = 1)
    (offsets : ∀ x : Fin k, s.nm (s.nr 21 + x.val) = k * x.val) (offsetsBefore : s.nr 21 + k ≤ s.nr 58)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k * k, MatchingPairBucketValid k s i)
    (oldRowValid : ∀ j < s.nr 87, s.nm (s.nr 86 + j) < k)
    (full : ℕ → List (DualSlack (MatchingDualEvent k)))
    (minima : ∀ j < s.nr 87, LeastSlackEntry (full j)
      (readMatchingPairBucket (k := k) s (contractedBucketIndex (matchingContractionColumnInput s) j))) :
    ∃ t ticks winner, ticks ≤ 22 * s.nr 87 + 97 ∧ BlockRuns repairMergedBucketForColumn ticks s t ∧ t.halted = false ∧
      MatchingCacheLayout k t ∧ (∀ r ≥ 24, t.nr r = s.nr r) ∧ t.rr 15 = s.rr 15 ∧
      LeastSlackEntry ((List.range (s.nr 87)).flatMap full) winner ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧
        readMatchingCandidate cutAt t i = if i = merged.val ∨ i = outside.val then
          addContractionWinner (fun d => {d with slack := d.slack - (s.rr 15 + s.rr 15)}) winner
            (readMatchingCandidate cutAt s i) else readMatchingCandidate cutAt s i) ∧
      (∀ i < k * k, MatchingPairBucketValid k t i ∧
        readMatchingPairBucket (k := k) t i = if i = k * merged.val + outside.val ∨ i = k * outside.val + merged.val then
          addContractionWinner id winner (readMatchingPairBucket (k := k) s i) else readMatchingPairBucket (k := k) s i) := by
  let address := s.nr 51 + s.nr 24
  let loaded := {s with pc := 2, nr := Function.update (Function.update s.nr 6 address) 10 1}
  have read : BlockRuns readSurvivingForestRole 2 s loaded := by
    apply BlockRuns.of_running_exit
    · simp [loaded, address, readSurvivingForestRole, arithmeticStep, entry, running, outsideAt, outer,
        Function.iterate_succ_apply']
    · exact running
    · rfl
  let a := {loaded with pc := 0}
  have keeps (r : ℕ) (safe6 : r ≠ 6 := by decide) (safe10 : r ≠ 10 := by decide) : a.nr r = s.nr r := by
    simp [a, loaded, Function.update_of_ne safe6, Function.update_of_ne safe10]
  have aOne : a.nr 9 = 1 := (keeps 9).trans one
  have aRole : a.nr 10 = 1 := by simp [a, loaded]
  have aLayout : MatchingCacheLayout k a := layout.keeps (fun r high => keeps r (by omega) (by omega))
  have aRows (i : ℕ) (hi : i < a.nr 61) : MatchingCandidateRowValid cutAt a i := by
    have inside : i < s.nr 61 := by rwa [keeps 61] at hi
    simpa only [MatchingCandidateRowValid, decodeMatchingDictionaryEvent, keeps 54, keeps 58,
      show a.nm = s.nm from rfl] using rows i inside
  have aBuckets (i : ℕ) (hi : i < k*k) : MatchingPairBucketValid k a i := by
    simpa only [MatchingPairBucketValid, keeps 65, show a.nm = s.nm from rfl] using buckets i hi
  have aOld (j : ℕ) (hi : j < a.nr 87) : a.nm (a.nr 86 + j) < k := by
    rw [keeps 87] at hi
    simpa only [keeps 86, show a.nm = s.nm from rfl] using oldRowValid j hi
  have aMinima (j : ℕ) (hi : j < a.nr 87) : LeastSlackEntry (full j)
      (readMatchingPairBucket (k := k) a (contractedBucketIndex (matchingContractionColumnInput a) j)) := by
    rw [keeps 87] at hi
    have oldIndex : contractedBucketIndex (matchingContractionColumnInput a) j =
        contractedBucketIndex (matchingContractionColumnInput s) j := by
      simp [contractedBucketIndex, matchingContractionColumnInput, keeps 21, keeps 86, keeps 24, keeps 23,
        show a.nm = s.nm from rfl]
    simpa only [oldIndex, readMatchingPairBucket, keeps 65, keeps 66, show a.nm = s.nm from rfl,
      show a.rm = s.rm from rfl] using minima j hi
  obtain ⟨t, ticks, winner, bound, merge, live, after, afterHigh, clock, winnerMin, candidates, pairs⟩ :=
    writeMergedBucketForOuter_rows cutAt (s := a) rfl running aOne ((keeps 23).trans zero) aLayout
      ((keeps 26).trans mergedAt) ((keeps 24).trans outsideAt) distinct
      (by intro x; simpa only [keeps 21, show a.nm = s.nm from rfl] using offsets x)
      (by rwa [keeps 21, keeps 58]) aRows aBuckets aOld full aMinima
  have unequal : a.nr 24 ≠ a.nr 26 := by
    rw [keeps 24, keeps 26, outsideAt, mergedAt]
    exact fun same => distinct (Fin.ext same.symm)
  let routedCode := branchOnUnequal 24 26 writeMergedBucketForOuter
  let insideCode := branchOnAtMost 9 10 routedCode []
  have route := branchOnUnequal_take 24 26 writeMergedBucketForOuter (s := a) rfl running unequal merge
  have keptInner := branchOnAtMost_left 9 10 routedCode [] (s := a) rfl running (by simp [aOne, aRole]) route live
  have keptOuter := branchOnAtMost_left 10 9 insideCode [] (s := a) rfl running (by simp [aOne, aRole]) keptInner live
  have run : BlockRuns repairMergedBucketForColumn (2 + (1 + (1 + (2 + ticks) + 1) + 1)) s _ := read.append keptOuter
  rw [keeps 87] at bound winnerMin
  refine ⟨_, _, winner, by omega, run, live, ?_, ?_, clock, winnerMin, ?_, ?_⟩
  · constructor <;> first
      | exact after.dimension | exact after.rows | exact after.idsBefore
      | exact after.recordsBefore | exact after.slacksBefore | exact after.ratesBefore
  · intro r high
    exact (afterHigh r high).trans (keeps r (by omega) (by omega))
  · intro i hi
    have within : i < a.nr 61 := by rwa [keeps 61]
    have old : readMatchingCandidate cutAt a i = readMatchingCandidate cutAt s i := by
      simp only [readMatchingCandidate, decodeMatchingDictionaryEvent, keeps 54, keeps 58, keeps 59, keeps 60,
        show a.nm = s.nm from rfl, show a.rm = s.rm from rfl]
    change MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i = _
    simpa only [old, show a.rr = s.rr from rfl] using candidates i within
  · intro i hi
    have old : readMatchingPairBucket (k := k) a i = readMatchingPairBucket (k := k) s i := by
      simp only [readMatchingPairBucket, keeps 65, keeps 66, show a.nm = s.nm from rfl, show a.rm = s.rm from rfl]
    change MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i = _
    simpa only [old] using pairs i hi

theorem repairMergedBucketForColumn_skip (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 9 = 1) (skip : s.nm (s.nr 51 + s.nr 24) ≠ 1 ∨ s.nr 24 = s.nr 26) :
    ∃ t ticks, ticks ≤ 8 ∧ BlockRuns repairMergedBucketForColumn ticks s t ∧ t.halted = false ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧ ∀ r, r ≠ 6 → r ≠ 10 → t.nr r = s.nr r := by
  let address := s.nr 51 + s.nr 24
  let loaded := {s with pc := 2, nr := Function.update (Function.update s.nr 6 address) 10 (s.nm address)}
  have read : BlockRuns readSurvivingForestRole 2 s loaded := by
    apply BlockRuns.of_running_exit
    · simp [loaded, address, readSurvivingForestRole, arithmeticStep, entry, running, Function.iterate_succ_apply']
    · exact running
    · rfl
  let a := {loaded with pc := 0}
  have stays (r : ℕ) (first : r ≠ 6 := by decide) (second : r ≠ 10 := by decide) : a.nr r = s.nr r := by
    simp [a, loaded, Function.update_of_ne first, Function.update_of_ne second]
  have tag : a.nr 10 = s.nm address := by simp [a, loaded]
  have oneAt : a.nr 9 = 1 := (stays 9).trans one
  let guarded := branchOnUnequal 24 26 writeMergedBucketForOuter
  let inner := branchOnAtMost 9 10 guarded []
  have empty : BlockRuns [] 0 a a := BlockRuns.of_running_exit rfl running rfl
  rcases lt_trichotomy (a.nr 10) (a.nr 9) with lower | equal | higher
  · have internal := branchOnAtMost_right 9 10 guarded [] (s := a) rfl running lower empty running
    have route := branchOnAtMost_left 10 9 inner [] (s := a) rfl running lower.le internal running
    exact ⟨_, 5, by decide, read.append route, running, rfl, rfl, rfl, fun r h6 h10 => stays r h6 h10⟩
  · have trueRole : s.nm (s.nr 51 + s.nr 24) = 1 := tag.symm.trans (equal.trans oneAt)
    have same := skip.resolve_left (by simp [trueRole])
    have equalAt : a.nr 24 = a.nr 26 := by rwa [stays 24, stays 26]
    have routed := branchOnUnequal_skip 24 26 writeMergedBucketForOuter a rfl running equalAt
    have internal := branchOnAtMost_left 9 10 guarded [] (s := a) rfl running equal.ge routed running
    have route := branchOnAtMost_left 10 9 inner [] (s := a) rfl running equal.le internal running
    exact ⟨_, 8, le_rfl, read.append route, running, rfl, rfl, rfl, fun r h6 h10 => stays r h6 h10⟩
  · have route := branchOnAtMost_right 10 9 inner [] (s := a) rfl running higher empty running
    exact ⟨_, 3, by decide, read.append route, running, rfl, rfl, rfl, fun r h6 h10 => stays r h6 h10⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractColumnRows

/-! matching/MatchingContractCacheFootprint.lean -/
section RppSource_MatchingContractCacheFootprint
namespace VehicleRoutingSurvey.Routing

set_option maxHeartbeats 700000
set_option maxRecDepth 4096

private theorem publishMinimumContractedBucket_footprint {k : ℕ} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (unit : s.nr 9 = 1)
    (layout : MatchingCacheLayout k s) (offsets : MatchingCacheOffsets k s)
    (merged : s.nr 26 < k) (outside : s.nr 17 < k) :
    ∃ t steps, BlockRuns publishMinimumContractedBucket steps s t ∧ t.halted = false ∧
      MatchingCacheFootprint k s t := by
  by_cases absent : s.nr 1 = 0
  · obtain ⟨t, run, live, natural, real, _⟩ := publishMinimumContractedBucket_empty s entry running absent
    exact ⟨t, 4, run, live, MatchingCacheFootprint.unchanged natural real⟩
  · let seeded := {s with pc := 2, nr := Function.update (Function.update s.nr 23 0) 14 0}
    have seed : BlockRuns [.natConst 23 0, .natConst 14 0] 2 s seeded := by
      apply BlockRuns.of_running_exit
      · simp [seeded, arithmeticStep, entry, running, Function.iterate_succ_apply']
      · exact running
      · rfl
    let a := {seeded with pc := 0}
    have aFixed (r : ℕ) (away23 : r ≠ 23 := by decide) (away14 : r ≠ 14 := by decide) : a.nr r = s.nr r := by
      simp [a, seeded, Function.update_of_ne away23, Function.update_of_ne away14]
    have aOne : a.nr 9 = 1 := (aFixed 9).trans unit
    have named : a.nr 1 ≠ a.nr 23 := by simpa [a, seeded] using absent
    obtain ⟨b, load, live, natural, real, _, _, _, _, fixed⟩ :=
      readMinimumContractedBucket_spec a rfl running aOne
    let ready := {b with pc := 0}
    have kept (r : ℕ) (safe : r ∉ [0, 6, 14, 15, 16, 18, 23] := by decide) : ready.nr r = s.nr r :=
      (fixed r (by simp at safe ⊢; omega)).trans (aFixed r (by simp at safe; omega) (by simp at safe; omega))
    have before : MatchingCacheFootprint k s ready := MatchingCacheFootprint.unchanged natural real
    obtain ⟨t, ticks, insert, done, _, after⟩ := insertMatchingOuterEdgeBlock_footprint (s := ready) rfl live ((kept 9).trans unit)
      ((fixed 14 (by decide)).trans (by simp [a, seeded])) (layout.keeps (fun r high => kept r (by simp; omega)))
      (offsets.keeps before (kept 21) (kept 58)) (by rwa [kept 26]) (by rwa [kept 17])
    have routed := branchOnUnequal_take 1 23 (appendBlock readMinimumContractedBucket insertMatchingOuterEdgeBlock)
      (s := a) rfl running named (load.append insert)
    have footprint := before.chain after (fun r listed => kept r (by simp at listed ⊢; omega))
    exact ⟨_, 2+(2+(8+ticks)), seed.append routed, done, footprint.natural, footprint.real⟩

private theorem writeMergedBucketForOuter_footprint {k : ℕ} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (unit : s.nr 9 = 1) (zero : s.nr 23 = 0)
    (layout : MatchingCacheLayout k s) (offsets : MatchingCacheOffsets k s)
    (merged : s.nr 26 < k) (outside : s.nr 24 < k) :
    ∃ t steps, BlockRuns writeMergedBucketForOuter steps s t ∧ t.halted = false ∧ MatchingCacheFootprint k s t := by
  let a := matchingContractionColumnInput s
  let setup := {a with pc := 1}
  have load : BlockRuns [.natAdd 17 24 23] 1 s setup := by
    apply BlockRuns.of_running_exit
    · simp [a, setup, matchingContractionColumnInput, arithmeticStep, entry, running]
    · exact running
    · rfl
  have aFixed (r : ℕ) (safe : r ≠ 17 := by decide) : a.nr r = s.nr r := by
    simp [a, matchingContractionColumnInput, safe]
  obtain ⟨b, selectTicks, _, choose, live, _, natural, real⟩ :=
    minimumContractedBucket_spec a rfl running ((aFixed 9).trans unit)
  let ready := {b with pc := 0}
  have fixed (r : ℕ) (away : r ∉ [0, 1, 2, 6, 7, 10, 11] := by decide) : ready.nr r = a.nr r := by
    change b.nr r = _
    rw [← choose.run]
    exact arithmeticRun_keeps_from_destination_list _ (by decide) away a selectTicks
  have kept (r : ℕ) (safe : r ∉ [0, 1, 2, 6, 7, 10, 11, 17] := by decide) : ready.nr r = s.nr r :=
    (fixed r (by simp at safe ⊢; omega)).trans (aFixed r (by simp at safe; omega))
  have before : MatchingCacheFootprint k s ready := MatchingCacheFootprint.unchanged natural real
  have target : ready.nr 17 = s.nr 24 := by
    rw [fixed 17]
    simp [a, matchingContractionColumnInput, zero]
  obtain ⟨t, ticks, publish, done, after⟩ := publishMinimumContractedBucket_footprint (s := ready) rfl live ((kept 9).trans unit)
    (layout.keeps (fun r high => kept r (by simp; omega))) (offsets.keeps before (kept 21) (kept 58))
    (by rwa [kept 26]) (by rwa [target])
  have footprint := before.chain after (fun r listed => kept r (by simp at listed ⊢; omega))
  exact ⟨_, 1+(selectTicks+ticks), load.append (choose.append publish), done, footprint.natural, footprint.real⟩

/-- A contraction-column repair writes only the candidate and pair caches. -/
theorem repairMergedBucketForColumn_footprint {k : ℕ} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (unit : s.nr 9 = 1) (zero : s.nr 23 = 0)
    (layout : MatchingCacheLayout k s) (offsets : MatchingCacheOffsets k s)
    (merged : s.nr 26 < k) (outside : s.nr 24 < k) :
    ∃ t steps, BlockRuns repairMergedBucketForColumn steps s t ∧ t.halted = false ∧ MatchingCacheFootprint k s t := by
  by_cases skipped : s.nm (s.nr 51+s.nr 24) ≠ 1 ∨ s.nr 24 = s.nr 26
  · obtain ⟨t, steps, _, run, done, natural, real, _⟩ := repairMergedBucketForColumn_skip s entry running unit skipped
    exact ⟨t, steps, run, done, MatchingCacheFootprint.unchanged natural real⟩
  · have outer : s.nm (s.nr 51+s.nr 24) = 1 := by by_contra h; exact skipped (Or.inl h)
    have distinct : s.nr 24 ≠ s.nr 26 := fun h => skipped (Or.inr h)
    let address := s.nr 51+s.nr 24
    let loaded := {s with pc := 2, nr := Function.update (Function.update s.nr 6 address) 10 1}
    have read : BlockRuns readSurvivingForestRole 2 s loaded := by
      apply BlockRuns.of_running_exit
      · simp [loaded, address, readSurvivingForestRole, arithmeticStep, entry, running, outer,
          Function.iterate_succ_apply']
      · exact running
      · rfl
    let a := {loaded with pc := 0}
    have keep (r : ℕ) (safe6 : r ≠ 6 := by decide) (safe10 : r ≠ 10 := by decide) : a.nr r = s.nr r := by
      simp [a, loaded, Function.update_of_ne safe6, Function.update_of_ne safe10]
    have aOne : a.nr 9 = 1 := (keep 9).trans unit
    have aRole : a.nr 10 = 1 := by simp [a, loaded]
    have before : MatchingCacheFootprint k s a := MatchingCacheFootprint.unchanged rfl rfl
    obtain ⟨t, ticks, write, live, after⟩ := writeMergedBucketForOuter_footprint (s := a) rfl running aOne ((keep 23).trans zero)
      (layout.keeps (fun r hr => keep r (by omega) (by omega))) (offsets.keeps before (keep 21) (keep 58))
      (by rwa [keep 26]) (by rwa [keep 24])
    let routedCode := branchOnUnequal 24 26 writeMergedBucketForOuter
    let innerCode := branchOnAtMost 9 10 routedCode []
    have route := branchOnUnequal_take 24 26 writeMergedBucketForOuter (s := a) rfl running
      (by rwa [keep 24, keep 26]) write
    have inner := branchOnAtMost_left 9 10 routedCode [] (s := a) rfl running (by simp [aOne, aRole]) route live
    have chosen := branchOnAtMost_left 10 9 innerCode [] (s := a) rfl running (by simp [aOne, aRole]) inner live
    have footprint := before.chain after (fun r hr => keep r (by simp at hr; omega) (by simp at hr; omega))
    exact ⟨_, 2+(1+(1+(2+ticks)+1)+1), read.append chosen, live, footprint.natural, footprint.real⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractCacheFootprint

/-! matching/MatchingContractionColumnStep.lean -/
section RppSource_MatchingContractionColumnStep
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096





/-- One actual column step either publishes its decoded minimum or retains all
rows when the surviving column has no outer label. -/
theorem repairMergedBucketForColumn_typed {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} {merged outside : Fin k}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 23 = 0)
    (layout : MatchingCacheLayout k s) (mergedAt : s.nr 26 = merged.val) (outsideAt : s.nr 24 = outside.val)
    (offsets : MatchingCacheOffsets k s) (oldRowValid : ∀ i < s.nr 87, s.nm (s.nr 86+i) < k)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k*k, MatchingPairBucketValid k s i)
    (full : ℕ → List (DualSlack (MatchingDualEvent k)))
    (minima : MatchingContractionColumnEligible s merged outside → ∀ j < s.nr 87, LeastSlackEntry (full j)
      (readMatchingPairBucket (k := k) s (contractedBucketIndex (matchingContractionColumnInput s) j))) :
    ∃ t ticks winner, ticks ≤ 22*s.nr 87+97 ∧ BlockRuns repairMergedBucketForColumn ticks s t ∧ t.halted = false ∧
      MatchingCacheLayout k t ∧ (∀ r ≥ 24, t.nr r = s.nr r) ∧ t.nr 9 = 1 ∧ t.nr 23 = 0 ∧
      t.rr 15 = s.rr 15 ∧ MatchingCacheFootprint k s t ∧
      (if MatchingContractionColumnEligible s merged outside then LeastSlackEntry ((List.range (s.nr 87)).flatMap full) winner
        else winner = none) ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧
        readMatchingCandidate cutAt t i = if i = merged.val ∨ i = outside.val then
          addContractionWinner (fun d => {d with slack := d.slack-(s.rr 15+s.rr 15)}) winner
            (readMatchingCandidate cutAt s i) else readMatchingCandidate cutAt s i) ∧
      (∀ i < k*k, MatchingPairBucketValid k t i ∧
        readMatchingPairBucket (k := k) t i = if i = k*merged.val+outside.val ∨ i = k*outside.val+merged.val then
          addContractionWinner id winner (readMatchingPairBucket (k := k) s i) else readMatchingPairBucket (k := k) s i) := by
  by_cases allowed : MatchingContractionColumnEligible s merged outside
  · obtain ⟨t, steps, winner, budget, run, live, final, fixed, clock, best, afterRows, afterBuckets⟩ :=
      repairMergedBucketForColumn_rows cutAt entry running one zero layout mergedAt outsideAt allowed.2 allowed.1
        (fun x => offsets.offsets x.val x.isLt) (by
          have positive := Nat.zero_lt_of_lt merged.isLt
          have final := offsets.addresses (k-1) (by omega)
          omega) rows buckets oldRowValid full (minima allowed)
    obtain ⟨u, _, observed, _, frame⟩ := repairMergedBucketForColumn_footprint entry running one zero layout offsets
      (by rw [mergedAt]; exact merged.isLt) (by rw [outsideAt]; exact outside.isLt)
    have same := (observed.same_exit run).2
    rw [same] at frame
    have oneAt : t.nr 9 = 1 := by
      rw [← run.run]
      exact (arithmeticRun_keeps_from_destination_list _ (by decide)
        (by decide : 9 ∉ [0, 1, 2, 6, 7, 10, 11, 14, 15, 16, 17, 18, 23]) s steps).trans one
    have clear23 := blockRuns_preservesNaturalZero (r := 23) (by decide) run zero
    exact ⟨t, steps, winner, budget, run, live, final, fixed, oneAt, clear23, clock, frame,
      by simpa only [if_pos allowed] using best, afterRows, afterBuckets⟩
  · have skips : s.nm (s.nr 51+s.nr 24) ≠ 1 ∨ s.nr 24 = s.nr 26 := by
      rw [outsideAt, mergedAt]
      by_cases outer : s.nm (s.nr 51+outside.val) = 1
      · right
        have same : merged = outside := by by_contra h; exact allowed ⟨outer, h⟩
        exact congrArg Fin.val same.symm
      · exact Or.inl outer
    obtain ⟨t, steps, budget, run, live, natural, real, clocks, fixed⟩ :=
      repairMergedBucketForColumn_skip s entry running one skips
    have high (r : ℕ) (hr : 24 ≤ r) : t.nr r = s.nr r := fixed r (by omega) (by omega)
    have ports := matchingCacheReads_unchanged cutAt (m := s) (t := t) natural real (fun r listed =>
      fixed r (by simp [matchingRefreshTableRegisters] at listed; omega)
        (by simp [matchingRefreshTableRegisters] at listed; omega))
    refine ⟨t, steps, none, by omega, run, live, layout.keeps (fun r hr => high r (by omega)), high,
      (fixed 9 (by decide) (by decide)).trans one, (fixed 23 (by decide) (by decide)).trans zero,
      congrFun clocks 15, MatchingCacheFootprint.unchanged natural real, by simp [allowed], ?_, ?_⟩
    · intro i hi
      refine ⟨(ports.1 i).1.symm ▸ rows i hi, ?_⟩
      split <;> simpa only [addContractionWinner, Option.map_none, Option.elim_none] using (ports.1 i).2
    · intro i hi
      refine ⟨(ports.2 i).1.symm ▸ buckets i hi, ?_⟩
      split <;> simpa only [addContractionWinner, Option.map_none, Option.elim_none] using (ports.2 i).2

theorem repairMergedBucketForColumn_keeps_offsets {s t : ArithmeticState} {steps : ℕ}
    (run : BlockRuns repairMergedBucketForColumn steps s t) : t.nr 21 = s.nr 21 := by
  rw [← run.run]
  exact arithmeticRun_keeps_from_destination_list [0, 1, 2, 6, 7, 10, 11, 14, 15, 16, 17, 18, 23]
    (by decide) (by decide) s steps

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionColumnStep

/-! matching/MatchingContractionColumnSweep.lean -/
section RppSource_MatchingContractionColumnSweep
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096







def repairMatchingContractionColumns : List ArithmeticInstruction := countedLoopFromZero 9 24 55 repairMergedBucketForColumn



private theorem absorbedColumnEntries {k : ℕ} (absorbed : List (Fin k))
    (full : Fin k → List (DualSlack (MatchingDualEvent k))) :
    (List.range absorbed.length).flatMap (fun j => if hit : j < absorbed.length then full (absorbed.get ⟨j,hit⟩) else []) =
      absorbed.flatMap full := by
  have indices : (List.finRange absorbed.length).map Fin.val = List.range absorbed.length := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  have reconstruct : (List.finRange absorbed.length).map absorbed.get = absorbed := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [List.getElem_finRange]
  calc
    _ = (List.finRange absorbed.length).flatMap (fun j => full (absorbed.get j)) := by
      rw [← indices, List.flatMap_map]
      congr 1
      funext j
      simp [j.isLt, Function.comp_def]
    _ = ((List.finRange absorbed.length).map absorbed.get).flatMap full := (List.flatMap_map _ _ _).symm
    _ = _ := by rw [reconstruct]

set_option maxHeartbeats 900000 in
/-- Read each surviving outer column from the intact absorbed rows. The actual
execution preserves later columns and publishes only their witnessed minima. -/
theorem repairMatchingContractionColumns_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} (merged : Fin k) (absorbed : List (Fin k))
    (entry : s.pc = 0) (running : s.halted = false) (unit : s.nr 9 = 1) (zero : s.nr 23 = 0)
    (layout : MatchingCacheLayout k s) (offsets : MatchingCacheOffsets k s)
    (mergedAt : s.nr 26 = merged.val) (countAt : s.nr 87 = absorbed.length)
    (encoded : ∀ j : Fin absorbed.length, s.nm (s.nr 86+j.val) = (absorbed.get j).val)
    (rolesBefore : s.nr 51+k ≤ s.nr 58) (absorbedAfter : s.nr 65+2*(k*k) ≤ s.nr 86)
    (survives : ∀ c, MatchingContractionColumnEligible s merged c → c ∉ absorbed)
    (full : Fin k → Fin k → List (DualSlack (MatchingDualEvent k)))
    (minima : ∀ row ∈ absorbed, ∀ v, MatchingContractionColumnEligible s merged v →
      LeastSlackEntry (full row v) (readMatchingPairBucket (k := k) s (k*row.val+v.val)))
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k*k, MatchingPairBucketValid k s i) :
    ∃ t steps, ∃ history : List (ContractionColumnWinner k), steps ≤ k*(22*absorbed.length+100)+2 ∧
      BlockRuns repairMatchingContractionColumns steps s t ∧ t.halted = false ∧
      MatchingCacheFootprint k s t ∧ t.rr 15 = s.rr 15 ∧
      (∀ r, r = 21 ∨ 25 ≤ r → t.nr r = s.nr r) ∧ t.nr 9 = 1 ∧ t.nr 23 = 0 ∧
      (∀ v : Fin k, MatchingContractionColumnEligible s merged v →
        ∃ w, (v,w) ∈ history ∧ LeastSlackEntry (absorbed.flatMap (fun row => full row v)) w) ∧
      (∀ v w, (v,w) ∈ history → if MatchingContractionColumnEligible s merged v then
        LeastSlackEntry (absorbed.flatMap (fun row => full row v)) w else w = none) ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧
        readMatchingCandidate cutAt t i = history.foldl (contractionColumnRowUpdate merged (s.rr 15) i) (readMatchingCandidate cutAt s i)) ∧
      (∀ i < k*k, MatchingPairBucketValid k t i ∧
        readMatchingPairBucket (k := k) t i = history.foldl (contractionColumnPairUpdate merged i) (readMatchingPairBucket (k := k) s i)) := by
  let view := ContractionColumnProgress cutAt s merged absorbed full
  let inv := fun i m => Nonempty (view i m)
  let seeded := {s with pc := 0, nr := Function.update s.nr 24 0}
  have initial : inv 0 seeded := by
    have keep (r : ℕ) (away : r ≠ 24) : seeded.nr r = s.nr r := Function.update_of_ne away _ _
    have ports := matchingCacheReads_unchanged cutAt (m := s) (t := seeded) rfl rfl
      (fun r listed => keep r (by simp [matchingRefreshTableRegisters] at listed; omega))
    refine ⟨⟨rfl, running, by simp [seeded], unit, zero, fun r safe => keep r (by omega), rfl,
      MatchingCacheFootprint.unchanged rfl rfl, [], ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro _ _ tooSmall
      omega
    · simp
    · intro row _ v _ _
      exact (ports.2 _).2
    · intro i hi
      exact ⟨(ports.1 i).1.symm ▸ rows i hi, (ports.1 i).2⟩
    · intro i hi
      exact ⟨(ports.2 i).1.symm ▸ buckets i hi, (ports.2 i).2⟩
  have iterate (j : ℕ) (hj : j < k) (m : ArithmeticState) (hasView : inv j m) :
      ∃ t steps, steps ≤ 22*absorbed.length+97 ∧ BlockRuns repairMergedBucketForColumn steps m t ∧ t.halted = false ∧
        inv (j+1) {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24+t.nr 9)} := by
    obtain ⟨h⟩ := hasView
    let v : Fin k := ⟨j,hj⟩
    have keep (r : ℕ) (safe : r = 21 ∨ 25 ≤ r := by decide) := h.fixed r safe
    have size : m.nr 87 = absorbed.length := (keep 87).trans countAt
    have label : m.nm (m.nr 51+v.val) = s.nm (s.nr 51+v.val) := by
      rw [keep 51, h.footprint.natural _ (.inl (by omega))]
    have guard : MatchingContractionColumnEligible m merged v ↔ MatchingContractionColumnEligible s merged v := by
      simp only [MatchingContractionColumnEligible, label]
    have word (i : ℕ) (hi : i < m.nr 87) : m.nm (m.nr 86+i) = (absorbed.get ⟨i,size ▸ hi⟩).val := by
      rw [keep 86, h.footprint.natural _ (.inr (by omega))]
      exact encoded ⟨i,size ▸ hi⟩
    have offs : MatchingCacheOffsets k m := offsets.keeps h.footprint (keep 21) (keep 58)
    let group := fun i => if hi : i < absorbed.length then full (absorbed.get ⟨i,hi⟩) v else []
    have leastHere (eligible : MatchingContractionColumnEligible m merged v) (i : ℕ) (hi : i < m.nr 87) :
        LeastSlackEntry (group i) (readMatchingPairBucket (k := k) m (contractedBucketIndex (matchingContractionColumnInput m) i)) := by
      let row := absorbed.get ⟨i,size ▸ hi⟩
      have slot : contractedBucketIndex (matchingContractionColumnInput m) i = k*row.val+v.val := by
        have address : (matchingContractionColumnInput m).nr 17 = v.val := by
          simp [matchingContractionColumnInput, h.index, h.zero, v]
        simp only [contractedBucketIndex, address, show (matchingContractionColumnInput m).nr 21 = m.nr 21 from rfl,
          show (matchingContractionColumnInput m).nr 86 = m.nr 86 from rfl,
          show (matchingContractionColumnInput m).nm = m.nm from rfl, word i hi]
        exact congrArg (·+v.val) (offs.offsets row.val row.isLt)
      have rowMem : row ∈ absorbed := List.get_mem _ _
      rw [slot, h.pending row rowMem v (guard.mp eligible) le_rfl]
      simpa only [group, dif_pos (size ▸ hi)] using minima row rowMem v (guard.mp eligible)
    obtain ⟨t, steps, w, cost, run, live, _, nextFixed, nextUnit, nextZero, clock, touched, chosen, nextRows, nextPairs⟩ :=
      repairMergedBucketForColumn_typed cutAt (outside := v) h.entry h.running h.unit h.zero
        (layout.keeps (fun r hr => keep r (Or.inr (by omega)))) ((keep 26).trans mergedAt) h.index offs
        (fun i hi => by rw [word i hi]; exact (absorbed.get ⟨i,size ▸ hi⟩).isLt)
        (fun i hi => (h.rows i (by rwa [keep 61] at hi)).1) (fun i hi => (h.buckets i hi).1) group leastHere
    have newCandidate : if MatchingContractionColumnEligible s merged v then
        LeastSlackEntry (absorbed.flatMap (fun row => full row v)) w else w = none := by
      have all := absorbedColumnEntries absorbed (fun r => full r v)
      have flat : (List.range absorbed.length).flatMap group = absorbed.flatMap (fun r => full r v) := all
      simpa only [size, flat, guard] using chosen
    rw [size] at cost
    let advanced := {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24+t.nr 9)}
    have keepA (r : ℕ) (away : r ≠ 24) : advanced.nr r = t.nr r := Function.update_of_ne away _ _
    have ports := matchingCacheReads_unchanged cutAt (m := t) (t := advanced) rfl rfl
      (fun r listed => keepA r (by simp [matchingRefreshTableRegisters] at listed; omega))
    have footprint := h.footprint.chain touched (fun r listed => keep r (Or.inr (by simp at listed; omega)))
    refine ⟨t, steps, cost, run, live, ⟨rfl, live, ?_, ?_, ?_, ?_, clock.trans h.clock,
      ⟨footprint.natural, footprint.real⟩, h.history++[(v,w)], ?_, ?_, ?_, ?_, ?_⟩⟩
    · simp [nextFixed 24 (by decide), nextUnit, h.index]
    · exact (keepA 9 (by decide)).trans nextUnit
    · exact (keepA 23 (by decide)).trans nextZero
    · intro r safe
      refine (keepA r (by omega)).trans (Eq.trans ?_ (keep r safe))
      rcases safe with rfl | high
      · exact repairMergedBucketForColumn_keeps_offsets run
      · exact nextFixed r (by omega)
    · intro c outer earlier
      obtain pre | now := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ earlier)
      · obtain ⟨winner, inPast, minimum⟩ := h.chosen c outer pre
        exact ⟨winner, List.mem_append_left _ inPast, minimum⟩
      · have same : c = v := Fin.ext now
        subst c
        exact ⟨w, List.mem_append_right _ (by simp), by simpa only [if_pos outer] using newCandidate⟩
    · intro c winner member
      rcases List.mem_append.mp member with past | now
      · obtain ⟨less, minimum⟩ := h.offered c winner past
        exact ⟨by omega, minimum⟩
      · have equal : (c,winner) = (v,w) := List.mem_singleton.mp now
        cases equal
        exact ⟨Nat.lt_succ_self _, newCandidate⟩
    · intro row rowMem later laterOuter notYet
      let slot := k*row.val+later.val
      have within : slot < k*k := by
        have hi := Nat.mul_le_mul_left k (Nat.succ_le_of_lt row.isLt)
        rw [Nat.mul_succ] at hi
        have far := later.isLt
        dsimp [slot]
        omega
      change readMatchingPairBucket (k := k) advanced slot = readMatchingPairBucket (k := k) s slot
      rw [(ports.2 slot).2, (nextPairs slot within).2, h.pending row rowMem later laterOuter (by omega)]
      by_cases outer : MatchingContractionColumnEligible s merged v
      · have distinct : v ≠ later := by
          intro equal
          have positions := congrArg Fin.val equal
          change j = later.val at positions
          omega
        have apart := contractionBucket_futureColumn_untouched absorbed.toFinset
          (merged := merged) (List.mem_toFinset.mpr rowMem)
          (fun h => survives v outer (List.mem_toFinset.mp h)) distinct
        rw [if_neg (fun p => p.elim apart.1 apart.2)]
      · have vacant : w = none := by simpa only [if_neg outer] using newCandidate
        simp only [vacant,addContractionWinner,Option.map_none,Option.elim_none,ite_self,slot]
    · intro i hi
      have inside : i < m.nr 61 := by rwa [keep 61]
      change MatchingCandidateRowValid cutAt advanced i ∧ readMatchingCandidate cutAt advanced i = _
      rw [(ports.1 i).1, (ports.1 i).2]
      refine ⟨(nextRows i inside).1, ?_⟩
      rw [(nextRows i inside).2, (h.rows i hi).2, h.clock, List.foldl_append] <;> rfl
    · intro i hi
      change MatchingPairBucketValid k advanced i ∧ readMatchingPairBucket (k := k) advanced i = _
      rw [(ports.2 i).1, (ports.2 i).2]
      refine ⟨(nextPairs i hi).1, ?_⟩
      rw [(nextPairs i hi).2, (h.buckets i hi).2, List.foldl_append] <;> rfl
  obtain ⟨t, steps, ⟨done⟩, bound, run⟩ := countedLoopFromZero_bounded 9 24 55 k (22*absorbed.length+97)
    repairMergedBucketForColumn inv (s := s) entry running initial
    (fun _ _ ⟨h⟩ => ⟨h.entry, h.running, h.index, (h.fixed 55 (by decide)).trans layout.dimension⟩) iterate
  refine ⟨_, steps, done.history, ?_, run, done.running, ⟨done.footprint.natural, done.footprint.real⟩, done.clock,
    done.fixed, done.unit, done.zero, ?_, ?_, done.rows, done.buckets⟩
  · rw [show 22*absorbed.length+97+3 = 22*absorbed.length+100 by omega] at bound
    omega
  · intro v outer
    exact done.chosen v outer v.isLt
  · intro v w mem
    exact (done.offered v w mem).2

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionColumnSweep

/-! matching/MatchingContractCacheTransfer.lean -/
section RppSource_MatchingContractCacheTransfer
namespace VehicleRoutingSurvey.Routing

/-- Comparing a column's minimum is enough to include all original edges
represented by that column. A vacant minimum represents an empty column. -/
theorem LeastSlackEntry.insertMinimum {Event : Type*} {prior fresh : List (DualSlack Event)}
    {stored candidate : Option (DualSlack Event)} (old : LeastSlackEntry prior stored)
    (new : LeastSlackEntry fresh candidate) :
    LeastSlackEntry (prior ++ fresh) (candidate.elim stored (fun d => insertSlackCandidate d stored)) := by
  cases candidate with
  | none =>
    refine ⟨fun someOld => List.mem_append_left _ (old.sound someOld), ?_⟩
    intro d present
    rcases List.mem_append.mp present with original | added
    · exact old.covers d original
    · obtain ⟨_, contradiction, _⟩ := new.covers d added
      simp at contradiction
  | some d =>
    have merged := old.insert d
    have included := new.sound (rfl : some d = some d)
    refine ⟨?_, ?_⟩
    · intro _ chosen
      rcases List.mem_cons.mp (merged.sound chosen) with equal | original
      · exact List.mem_append_right _ (equal.symm ▸ included)
      · exact List.mem_append_left _ original
    · intro edge present
      rcases List.mem_append.mp present with original | added
      · exact merged.covers edge (List.mem_cons_of_mem _ original)
      · obtain ⟨other, chosen, below⟩ := new.covers edge added
        have equal := Option.some.inj chosen
        obtain ⟨best, isBest, least⟩ := merged.covers d (by simp)
        exact ⟨best, isBest, least.trans (equal.symm ▸ below)⟩

/-- An identical normalization offset on the complete column preserves its minimum. -/
theorem LeastSlackEntry.subtractSlackOffset {Event : Type*} {full : List (DualSlack Event)}
    {best : Option (DualSlack Event)} (before : LeastSlackEntry full best) (offset : ℝ) :
    let raw := fun d : DualSlack Event => {d with slack := d.slack-offset}
    LeastSlackEntry (full.map raw) (best.map raw) := by
  intro raw
  constructor
  · intro d chosen
    cases best with
    | none => simp at chosen
    | some d₀ =>
      have equal : raw d₀ = d := Option.some.inj chosen
      exact List.mem_map.mpr ⟨d₀, before.sound rfl, equal⟩
  · intro d found
    obtain ⟨d₀, present, rfl⟩ := List.mem_map.mp found
    obtain ⟨best₀, chosen, below⟩ := before.covers d₀ present
    exact ⟨raw best₀, by simp only [chosen, Option.map_some], by
      change best₀.slack-offset ≤ d₀.slack-offset
      exact sub_le_sub_right below offset⟩

/-- Contraction rebuilds an outside column from the old outer rows and the newly
outer originals. The outside block's original vertices keep their representative. -/
theorem contractionPairEntries_mem {k : ℕ} (prior after : Fin k → Fin k) (oldOuter fresh : List (Fin k))
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (time : ℝ) (merged outside : Fin k)
    (isMerged : ∀ u, after u = merged ↔ prior u ∈ oldOuter ∨ u ∈ fresh)
    (isOutside : ∀ v, after v = outside ↔ prior v = outside)
    (d : DualSlack (MatchingDualEvent k)) :
    d ∈ normalizedOuterPairEntries after cost effective time merged outside ↔
      d ∈ oldOuter.flatMap (fun old => normalizedOuterPairEntries prior cost effective time old outside) ∨
        ∃ u v, u ∈ fresh ∧ prior v = outside ∧ normalizedOuterEdge cost effective time u v = d := by
  rw [normalizedOuterPairEntries_mem]
  constructor
  · rintro ⟨u, v, inMerged, inOutside, edge⟩
    have vOld := (isOutside v).mp inOutside
    rcases (isMerged u).mp inMerged with old | new
    · exact Or.inl (List.mem_flatMap.mpr ⟨prior u, old,
        normalizedOuterPairEntries_mem.mpr ⟨u, v, rfl, vOld, edge⟩⟩)
    · exact Or.inr ⟨u, v, new, vOld, edge⟩
  · intro present
    rcases present with old | new
    · obtain ⟨row, rowIn, found⟩ := List.mem_flatMap.mp old
      obtain ⟨u, v, atRow, atColumn, edge⟩ := normalizedOuterPairEntries_mem.mp found
      exact ⟨u, v, (isMerged u).mpr (Or.inl (atRow.symm ▸ rowIn)), (isOutside v).mpr atColumn, edge⟩
    · obtain ⟨u, v, newOuter, atColumn, edge⟩ := new
      exact ⟨u, v, (isMerged u).mpr (Or.inr newOuter), (isOutside v).mpr atColumn, edge⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractCacheTransfer

/-! matching/MatchingContractionColumnMinimum.lean -/
section RppSource_MatchingContractionColumnMinimum
namespace VehicleRoutingSurvey.Routing

private noncomputable def matchingContractionColumnWitness {k : ℕ} (col : Fin k)
    (record : ContractionColumnWinner k) : Option (DualSlack (MatchingDualEvent k)) :=
  if record.1 = col then record.2 else none

private theorem contractionColumnPairUpdate_at {k : ℕ} {merged col : Fin k} (separate : merged ≠ col)
    (entry : ContractionColumnWinner k) (cached : Option (DualSlack (MatchingDualEvent k))) :
    contractionColumnPairUpdate merged (k*merged.val+col.val) cached entry =
      (matchingContractionColumnWitness col entry).elim cached (fun d => insertSlackCandidate d cached) := by
  obtain ⟨outside, winner⟩ := entry
  have direct : k*merged.val+col.val = k*merged.val+outside.val ↔ outside = col := by
    constructor
    · intro eq
      exact (Fin.ext ((denseMatrixOffset_eq_iff col.isLt outside.isLt).mp eq).2).symm
    · rintro rfl
      rfl
  have reverse : k*merged.val+col.val ≠ k*outside.val+merged.val := by
    intro eq
    exact separate (Fin.ext ((denseMatrixOffset_eq_iff col.isLt merged.isLt).mp eq).2).symm
  by_cases selected : outside = col
  · cases winner <;> simp [contractionColumnPairUpdate, matchingContractionColumnWitness, direct, selected, addContractionWinner]
  · have apart : col.val ≠ outside.val := fun h => selected (Fin.ext h.symm)
    simp [contractionColumnPairUpdate, matchingContractionColumnWitness, direct, reverse, selected,apart]

private theorem contractionColumnPairFold_at {k : ℕ} {merged col : Fin k} (separate : merged ≠ col)
    (history : List (ContractionColumnWinner k)) (initial : Option (DualSlack (MatchingDualEvent k))) :
    history.foldl (contractionColumnPairUpdate merged (k*merged.val+col.val)) initial =
      insertSlackCandidates (history.filterMap (matchingContractionColumnWitness col)) initial := by
  induction history generalizing initial with
  | nil => rfl
  | cons entry rest ih =>
    rw [List.foldl_cons, contractionColumnPairUpdate_at separate, ih]
    cases selected : matchingContractionColumnWitness col entry <;>
      simp [List.filterMap_cons, selected, insertSlackCandidates]

/-- An outside column contains the exact old-union minimum after the real RAM
scan has published one least witness for that column. A previous bucket at the
base retained only edges already covered by that union. -/
theorem contractionColumnPairFold_least {k : ℕ} {merged col : Fin k} (separate : merged ≠ col)
    (history : List (ContractionColumnWinner k))
    {initial : Option (DualSlack (MatchingDualEvent k))} {prior full : List (DualSlack (MatchingDualEvent k))}
    (old : LeastSlackEntry prior initial) (priorIncluded : ∀ d ∈ prior, d ∈ full)
    (present : ∃ w, (col,w) ∈ history ∧ LeastSlackEntry full w)
    (valid : ∀ w, (col,w) ∈ history → LeastSlackEntry full w) :
    LeastSlackEntry full (history.foldl (contractionColumnPairUpdate merged (k*merged.val+col.val)) initial) := by
  rw [contractionColumnPairFold_at separate]
  let offered := history.filterMap (matchingContractionColumnWitness col)
  let cached := insertSlackCandidates offered initial
  have least : LeastSlackEntry (offered.reverse ++ prior) cached := old.insert_many offered
  have member (d : DualSlack (MatchingDualEvent k)) : d ∈ offered ↔ ∃ w, (col,w) ∈ history ∧ w = some d := by
    constructor
    · intro matchesList
      obtain ⟨⟨a,w⟩, atPair, chosen⟩ := List.mem_filterMap.mp matchesList
      by_cases relevant : a = col
      · subst a
        exact ⟨w, atPair, by simpa [matchingContractionColumnWitness] using chosen⟩
      · simp [matchingContractionColumnWitness, relevant] at chosen
    · rintro ⟨w, atPair, chosen⟩
      exact List.mem_filterMap.mpr ⟨(col,w), atPair, by simpa [matchingContractionColumnWitness] using chosen⟩
  constructor
  · intro d hd
    rcases List.mem_append.mp (least.sound hd) with good | oldDatum
    · obtain ⟨w, included, witness⟩ := (member d).mp (List.mem_reverse.mp good)
      exact (valid w included).sound witness
    · exact priorIncluded d oldDatum
  · intro d available
    obtain ⟨minimum, atColumn, exactMinimum⟩ := present
    obtain ⟨p, isP, lower⟩ := exactMinimum.covers d available
    have inOffered : p ∈ offered := (member p).mpr ⟨minimum, atColumn, isP⟩
    obtain ⟨q, chosen, below⟩ := least.covers p (List.mem_append_left _ (List.mem_reverse.mpr inOffered))
    exact ⟨q, chosen, below.trans lower⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionColumnMinimum

/-! matching/MatchingContractionFreshRows.lean -/
section RppSource_MatchingContractionFreshRows
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

/-- The promoted-original scan loads the original index from the contraction list
and inserts exactly its incident candidates and normalized pair keys. -/
theorem scanFreshContractedOriginal_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} {rep : Fin k → Fin k} {role : Fin k → ℕ}
    {cost : Fin k → Fin k → ℝ} {effective : Fin k → ℝ} {u : Fin k}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (input : MatchingRefreshInput s rep role cost effective)
    (current : s.nm (s.nr 88+s.nr 24) = u.val) (source : s.nr 26 = (rep u).val)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k*k, MatchingPairBucketValid k s i) :
    ∃ t steps, steps ≤ 98*k+4 ∧ BlockRuns scanFreshContractedOriginal steps s t ∧ t.halted = false ∧
      t.rr 15 = s.rr 15 ∧ MatchingRefreshInput t rep role cost effective ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i =
        insertSlackCandidates ((List.finRange k).filterMap (fun v => outerRefreshRowInput rep role cost effective u v i))
          (readMatchingCandidate cutAt s i)) ∧
      (∀ i < k*k, MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i =
        insertSlackCandidates ((List.finRange k).filterMap
          (fun v => outerRefreshPairInput rep role cost effective (s.rr 15) u v i)) (readMatchingPairBucket (k := k) s i)) ∧
      MatchingCacheFootprint k s t ∧
      (∀ r, r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 25] → t.nr r = s.nr r) := by
  let seeded := { s with
    pc := 2
    nr := Function.update (Function.update s.nr 6 (s.nr 88+s.nr 24)) 15 u.val }
  have load : BlockRuns [.natAdd 6 88 24, .natLoad 15 6] 2 s seeded := by
    refine BlockRuns.of_running_exit ?_ running rfl
    simp [seeded, arithmeticStep, entry, running, current, Function.iterate_succ_apply']
  let ready := {seeded with pc := 0}
  have keep (r : ℕ) (not6 : r ≠ 6 := by decide) (not15 : r ≠ 15 := by decide) : ready.nr r = s.nr r := by
    simp [ready, seeded, Function.update_of_ne not6, Function.update_of_ne not15]
  have readyInput : MatchingRefreshInput ready rep role cost effective := input.keeps
    ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩
      (fun r listed => keep r (by simp [matchingRefreshTableRegisters] at listed; omega)
        (by simp [matchingRefreshTableRegisters] at listed; omega))
  have readyRows (i : ℕ) (hi : i < ready.nr 61) : MatchingCandidateRowValid cutAt ready i := by
    rw [keep 61] at hi
    simpa only [MatchingCandidateRowValid, decodeMatchingDictionaryEvent, keep 58, keep 54, show ready.nm = s.nm by rfl]
      using rows i hi
  have readyPairs (i : ℕ) (hi : i < k*k) : MatchingPairBucketValid k ready i := by
    simpa only [MatchingPairBucketValid, keep 65, show ready.nm = s.nm by rfl] using buckets i hi
  obtain ⟨t, steps, budget, scan, live, fixed, time, after, candidates, pairs⟩ := refreshSelectedOuterVertex_rows cutAt (s := ready) (u := u)
    rfl running ((keep 9).trans one) ((keep 14).trans zero) readyInput (by simp [ready, seeded])
    ((keep 26).trans source) readyRows readyPairs
  have offsets : MatchingCacheOffsets k ready :=
    ⟨fun i hi => by have cap := readyInput.offsetsBefore; omega, fun i hi => readyInput.offsets ⟨i, hi⟩⟩
  have reps : MatchingCacheRepresentatives k ready :=
    ⟨fun i hi => by have cap := readyInput.representativesBefore; omega, fun i hi => by
      rw [readyInput.representatives ⟨i, hi⟩]
      exact (rep ⟨i, hi⟩).isLt⟩
  obtain ⟨other, otherSteps, otherRun, _, _, written⟩ := refreshSelectedOuterVertex_footprint (s := ready)
    rfl running ((keep 9).trans one) ((keep 14).trans zero) readyInput.layout offsets reps
    (by rw [keep 26, source]; exact (rep u).isLt)
  have same := (otherRun.same_exit scan).2
  rw [same] at written
  have untouched : MatchingCacheFootprint k s ready := MatchingCacheFootprint.unchanged rfl rfl
  have footprint := untouched.chain written (fun r listed => keep r (by simp at listed; omega) (by simp at listed; omega))
  refine ⟨_, 2+steps, by omega, load.append scan, live, time, ?_, ?_, ?_, ⟨footprint.natural, footprint.real⟩, ?_⟩
  · exact after.keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
  · intro i hi
    have current : i < ready.nr 61 := by rwa [keep 61]
    have same : readMatchingCandidate cutAt ready i = readMatchingCandidate cutAt s i := by
      simp only [readMatchingCandidate, decodeMatchingDictionaryEvent, keep 54, keep 58, keep 59, keep 60,
        show ready.nm = s.nm by rfl, show ready.rm = s.rm by rfl]
    change MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i = _
    simpa only [same] using candidates i current
  · intro i hi
    have same : readMatchingPairBucket (k := k) ready i = readMatchingPairBucket (k := k) s i := by
      simp only [readMatchingPairBucket, keep 65, keep 66, show ready.nm = s.nm by rfl, show ready.rm = s.rm by rfl]
    change MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i = _
    simpa only [same, show ready.rr 15 = s.rr 15 by rfl] using pairs i hi
  · intro r safe
    exact (fixed r (by simp at safe ⊢; omega)).trans (keep r (by simp at safe; omega) (by simp at safe; omega))

def scanFreshContractedOriginals : List ArithmeticInstruction := countedLoopFromZero 9 24 99 scanFreshContractedOriginal

noncomputable def contractionFreshRowInputs {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (i : ℕ) (u : Fin k) :
    List (DualSlack (MatchingDualEvent k)) := (List.finRange k).filterMap (fun v => outerRefreshRowInput rep role cost effective u v i)

noncomputable def contractionFreshPairInputs {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (time : ℝ) (i : ℕ) (u : Fin k) :
    List (DualSlack (MatchingDualEvent k)) := (List.finRange k).filterMap (fun v => outerRefreshPairInput rep role cost effective time u v i)

private structure ContractionFreshProgress {k : ℕ} (cutAt : Fin k → Finset (Fin k)) (s : ArithmeticState)
    (rep : Fin k → Fin k) (role : Fin k → ℕ) (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ)
    (fresh : List (Fin k)) (count : ℕ) (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  live : m.halted = false
  index : m.nr 24 = count
  time : m.rr 15 = s.rr 15
  fixed : ∀ r, r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25] → m.nr r = s.nr r
  input : MatchingRefreshInput m rep role cost effective
  footprint : MatchingCacheFootprint k s m
  rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt m i ∧ readMatchingCandidate cutAt m i =
    insertSlackCandidates ((fresh.take count).flatMap (contractionFreshRowInputs rep role cost effective i))
      (readMatchingCandidate cutAt s i)
  buckets : ∀ i < k*k, MatchingPairBucketValid k m i ∧ readMatchingPairBucket (k := k) m i =
    insertSlackCandidates ((fresh.take count).flatMap (contractionFreshPairInputs rep role cost effective (s.rr 15) i))
      (readMatchingPairBucket (k := k) s i)

set_option maxHeartbeats 700000 in
/-- Run the exact charged scan over the newly outer original list. -/
theorem scanFreshContractedOriginals_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} {rep : Fin k → Fin k} {role : Fin k → ℕ} {cost : Fin k → Fin k → ℝ} {effective : Fin k → ℝ}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (input : MatchingRefreshInput s rep role cost effective) (fresh : List (Fin k))
    (lengthAt : s.nr 99 = fresh.length) (words : ∀ i : Fin fresh.length, s.nm (s.nr 88+i.val) = (fresh.get i).val)
    (representative : ∀ u ∈ fresh, s.nr 26 = (rep u).val) (freshAfter : s.nr 65 + 2*(k*k) ≤ s.nr 88)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k*k, MatchingPairBucketValid k s i) :
    ∃ t steps, steps ≤ fresh.length*(98*k+7)+2 ∧ BlockRuns scanFreshContractedOriginals steps s t ∧ t.halted = false ∧
      t.rr 15 = s.rr 15 ∧ MatchingRefreshInput t rep role cost effective ∧ MatchingCacheFootprint k s t ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i =
        insertSlackCandidates (fresh.flatMap (contractionFreshRowInputs rep role cost effective i)) (readMatchingCandidate cutAt s i)) ∧
      (∀ i < k*k, MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i =
        insertSlackCandidates (fresh.flatMap (contractionFreshPairInputs rep role cost effective (s.rr 15) i))
          (readMatchingPairBucket (k := k) s i)) := by
  let inv := ContractionFreshProgress cutAt s rep role cost effective fresh
  let seeded := {s with pc := 0, nr := Function.update s.nr 24 0}
  have seedKeep (r : ℕ) (away : r ≠ 24) : seeded.nr r = s.nr r := Function.update_of_ne away _ _
  have seedPorts (r : ℕ) (member : r ∈ matchingRefreshTableRegisters) : seeded.nr r = s.nr r :=
    seedKeep r (by simp [matchingRefreshTableRegisters] at member; omega)
  have cache := matchingCacheReads_unchanged cutAt (m := s) (t := seeded) rfl rfl seedPorts
  have initial : inv 0 seeded := by
    refine ⟨rfl, running, by simp [seeded], rfl, fun r safe => seedKeep r (by simp at safe; omega),
      input.keeps (t := seeded) ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ seedPorts, MatchingCacheFootprint.unchanged rfl rfl, ?_, ?_⟩
    · intro i hi
      exact ⟨(cache.1 i).1.symm ▸ rows i hi, by
        simpa only [List.take_zero, List.flatMap_nil, insertSlackCandidates, List.foldl_nil] using (cache.1 i).2⟩
    · intro i hi
      exact ⟨(cache.2 i).1.symm ▸ buckets i hi, by
        simpa only [List.take_zero, List.flatMap_nil, insertSlackCandidates, List.foldl_nil] using (cache.2 i).2⟩
  have recurse (j : ℕ) (hj : j < fresh.length) (m : ArithmeticState) (before : inv j m) :
      ∃ t steps, steps ≤ 98*k+4 ∧ BlockRuns scanFreshContractedOriginal steps m t ∧ t.halted = false ∧
        inv (j+1) {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24+t.nr 9)} := by
    let u := fresh.get ⟨j, hj⟩
    have fixed (r : ℕ) (safe : r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25] := by decide) := before.fixed r safe
    have unit := (fixed 9).trans one
    have indexWord : m.nm (m.nr 88+m.nr 24) = u.val := by
      rw [fixed 88, before.index, before.footprint.natural _ (Or.inr (by omega))]
      exact words ⟨j,hj⟩
    have source : m.nr 26 = (rep u).val := (fixed 26).trans (representative u (List.get_mem _ _))
    have beforeRows (p : ℕ) (within : p < m.nr 61) := (before.rows p (by rwa [fixed 61] at within)).1
    obtain ⟨t, steps, budget, run, live, time, after, updatedRows, updatedPairs, effect, kept⟩ :=
      scanFreshContractedOriginal_rows cutAt before.entry before.live unit ((fixed 14).trans zero)
        before.input indexWord source beforeRows (fun p hp => (before.buckets p hp).1)
    let advanced := {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24+t.nr 9)}
    have keepAdvance (r : ℕ) (away : r ≠ 24) : advanced.nr r = t.nr r := Function.update_of_ne away _ _
    have ports (r : ℕ) (listed : r ∈ matchingRefreshTableRegisters) : advanced.nr r = t.nr r :=
      keepAdvance r (by simp [matchingRefreshTableRegisters] at listed; omega)
    have cache := matchingCacheReads_unchanged cutAt (m := t) (t := advanced) rfl rfl ports
    have footprint := before.footprint.chain effect (fun r listed => fixed r (by simp at listed ⊢; omega))
    have nextPrefix : fresh.take (j+1) = fresh.take j ++ [u] := by
      rw [List.take_succ_eq_append_getElem hj] <;> rfl
    refine ⟨t, steps, budget, run, live, rfl, live, ?_, time.trans before.time, ?_,
      after.keeps (t := advanced) ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ ports,
      ⟨footprint.natural, footprint.real⟩, ?_, ?_⟩
    · simp [kept 24 (by decide), kept 9 (by decide), before.index, unit]
    · intro r safe
      exact (keepAdvance r (by simp at safe; omega)).trans ((kept r (by simp at safe ⊢; omega)).trans (fixed r safe))
    · intro i hi
      have within : i < m.nr 61 := by rwa [fixed 61]
      change MatchingCandidateRowValid cutAt advanced i ∧ readMatchingCandidate cutAt advanced i = _
      rw [(cache.1 i).1, (cache.1 i).2]
      refine ⟨(updatedRows i within).1, ?_⟩
      rw [(updatedRows i within).2, (before.rows i hi).2, nextPrefix]
      simp [contractionFreshRowInputs, List.flatMap_append, insertSlackCandidates, List.foldl_append]
    · intro i hi
      change MatchingPairBucketValid k advanced i ∧ readMatchingPairBucket (k := k) advanced i = _
      rw [(cache.2 i).1, (cache.2 i).2]
      refine ⟨(updatedPairs i hi).1, ?_⟩
      rw [(updatedPairs i hi).2, (before.buckets i hi).2, before.time, nextPrefix]
      simp [contractionFreshPairInputs, List.flatMap_append, insertSlackCandidates, List.foldl_append]
  obtain ⟨t, steps, done, budget, ran⟩ := countedLoopFromZero_bounded 9 24 99 fresh.length (98*k+4)
    scanFreshContractedOriginal inv (s := s) entry running initial
    (fun _ _ h => ⟨h.entry, h.live, h.index, (h.fixed 99 (by decide)).trans lengthAt⟩) recurse
  have all : fresh.take fresh.length = fresh := List.take_of_length_le le_rfl
  let exitState := relocateState 1 {t with pc := (countedLoop 9 24 99 scanFreshContractedOriginal).length}
  have ports := matchingCacheReads_unchanged cutAt (m := t) (t := exitState) rfl rfl (fun _ _ => rfl)
  refine ⟨exitState, steps, ?_, ran, done.live, done.time, ?_, ⟨done.footprint.natural, done.footprint.real⟩, ?_, ?_⟩
  · rw [show 98*k+4+3 = 98*k+7 by omega] at budget
    omega
  · exact done.input.keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
  · intro i hi
    rw [(ports.1 i).1, (ports.1 i).2]
    simpa only [all] using done.rows i hi
  · intro i hi
    rw [(ports.2 i).1, (ports.2 i).2]
    simpa only [all] using done.buckets i hi

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionFreshRows

/-! matching/MatchingContractionPairOffers.lean -/
section RppSource_MatchingContractionPairOffers
namespace VehicleRoutingSurvey.Routing

theorem matchingPairSlot_eq {k : ℕ} (a b x y : Fin k) :
    k*a.val+b.val = k*x.val+y.val ↔ a = x ∧ b = y := by
  simpa only [Fin.ext_iff] using (denseMatrixOffset_eq_iff (i := a.val) (i' := x.val) b.isLt y.isLt)

theorem LeastSlackEntry.of_mem_iff {Event : Type*} {xs ys : List (DualSlack Event)}
    {w : Option (DualSlack Event)} (least : LeastSlackEntry xs w) (same : ∀ d, d ∈ xs ↔ d ∈ ys) :
    LeastSlackEntry ys w where
  sound h := (same _).mp (least.sound h)
  covers d hd := least.covers d ((same d).mpr hd)

theorem normalizedOuterPairEntries_swap_mem {k : ℕ} (rep : Fin k → Fin k)
    {cost : Fin k → Fin k → ℝ} (symmetric : ∀ u v, cost u v = cost v u)
    (effective : Fin k → ℝ) (time : ℝ) (a b : Fin k) (d : DualSlack (MatchingDualEvent k)) :
    d ∈ normalizedOuterPairEntries rep cost effective time a b ↔
      d ∈ normalizedOuterPairEntries rep cost effective time b a := by
  simp only [normalizedOuterPairEntries_mem]
  constructor <;> rintro ⟨u,v,hu,hv,edge⟩ <;>
    exact ⟨v,u,hv,hu,(normalizedOuterEdge_swap symmetric effective time v u).trans edge⟩

/-- Every insertion by the promoted-original scan comes from the merged block.
Both directed physical slots receive the same normalized edge. -/
theorem contractionFreshPairOffers_mem {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (time : ℝ)
    (fresh : List (Fin k)) (merged : Fin k) (freshRep : ∀ u ∈ fresh, rep u = merged)
    (a b : Fin k) (d : DualSlack (MatchingDualEvent k)) :
    d ∈ fresh.flatMap (contractionFreshPairInputs rep role cost effective time (k*a.val+b.val)) ↔
      ∃ u ∈ fresh, ∃ v, merged ≠ rep v ∧ role (rep v) = 1 ∧
        ((a = merged ∧ b = rep v) ∨ (a = rep v ∧ b = merged)) ∧
        normalizedOuterEdge cost effective time u v = d := by
  simp only [List.mem_flatMap, contractionFreshPairInputs, List.mem_filterMap, List.mem_finRange,
    true_and, outerRefreshPairInput_some_iff]
  constructor
  · rintro ⟨u,inside,v,separate,⟨outer,coords⟩,edge⟩
    rw [freshRep u inside] at separate coords
    exact ⟨u,inside,v,separate,outer,coords,edge⟩
  · rintro ⟨u,inside,v,separate,outer,coords,edge⟩
    refine ⟨u,inside,v,?_,⟨outer,?_⟩,edge⟩ <;> rwa [freshRep u inside]

theorem contractionFreshPairOffers_swap {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (time : ℝ)
    (fresh : List (Fin k)) (merged : Fin k) (freshRep : ∀ u ∈ fresh, rep u = merged)
    (a b : Fin k) (d : DualSlack (MatchingDualEvent k)) :
    d ∈ fresh.flatMap (contractionFreshPairInputs rep role cost effective time (k*a.val+b.val)) ↔
      d ∈ fresh.flatMap (contractionFreshPairInputs rep role cost effective time (k*b.val+a.val)) := by
  rw [contractionFreshPairOffers_mem rep role cost effective time fresh merged freshRep,
    contractionFreshPairOffers_mem rep role cost effective time fresh merged freshRep]
  constructor <;> rintro ⟨u, hu, v, hv, outer, h, edge⟩ <;>
    exact ⟨u, hu, v, hv, outer, h.elim (fun p => Or.inr p.symm) (fun p => Or.inl p.symm), edge⟩

theorem contractionColumnPairFold_swap {k : ℕ} (merged a b : Fin k)
    (history : List (ContractionColumnWinner k)) (initial : Option (DualSlack (MatchingDualEvent k))) :
    history.foldl (contractionColumnPairUpdate merged (k*a.val+b.val)) initial =
      history.foldl (contractionColumnPairUpdate merged (k*b.val+a.val)) initial := by
  have same : contractionColumnPairUpdate merged (k*a.val+b.val) = contractionColumnPairUpdate merged (k*b.val+a.val) := by
    funext old entry
    unfold contractionColumnPairUpdate
    simp only [matchingPairSlot_eq]
    have iffCoords : ((a = merged ∧ b = entry.1) ∨ (a = entry.1 ∧ b = merged)) ↔
        ((b = merged ∧ a = entry.1) ∨ (b = entry.1 ∧ a = merged)) := by tauto
    simp only [iffCoords]
  rw [same]

theorem contractionColumnPairFold_untouched {k : ℕ} (merged a b : Fin k)
    (history : List (ContractionColumnWinner k))
    (admissible : ∀ v w, (v,w) ∈ history → ((a = merged ∧ b = v) ∨ (a = v ∧ b = merged)) → w = none)
    (initial : Option (DualSlack (MatchingDualEvent k))) :
    history.foldl (contractionColumnPairUpdate merged (k*a.val+b.val)) initial = initial := by
  induction history generalizing initial with
  | nil => rfl
  | cons entry tail ih =>
    obtain ⟨col,w⟩ := entry
    rw [List.foldl_cons, ih (fun v candidate found => admissible v candidate (List.mem_cons_of_mem _ found))]
    simp only [contractionColumnPairUpdate, matchingPairSlot_eq]
    split
    · rename_i aliases
      simp [admissible col w (List.mem_cons_self) aliases, addContractionWinner]
    · rfl

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionPairOffers

/-! matching/MatchingContractionPairMeaning.lean -/
section RppSource_MatchingContractionPairMeaning
namespace VehicleRoutingSurvey.Routing



/-- The actual two cache folds maintain normalized minimum keys for every
distinct outer pair as well as vacancy at original vertices still outside the outer forest. -/
theorem matchingContractionPairBuckets {k : ℕ} {s t : ArithmeticState}
    (prior next : Fin k → Fin k) (oldRole newRole : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (symmetric : ∀ u v, cost u v = cost v u) (effective : Fin k → ℝ)
    (merged : Fin k) (absorbed fresh : List (Fin k)) (history : List (ContractionColumnWinner k))
    (shape : MatchingContractionPairGeometry prior next oldRole newRole merged absorbed fresh)
    (before : MatchingSearchOuterBuckets s prior oldRole cost effective)
    (roleAt : ∀ c : Fin k, s.nm (s.nr 51+c.val) = newRole c) (clock : t.rr 15 = s.rr 15)
    (chosen : ∀ c : Fin k, MatchingContractionColumnEligible s merged c → ∃ w, (c,w) ∈ history ∧
      LeastSlackEntry (absorbed.flatMap (fun r => normalizedOuterPairEntries prior cost effective (s.rr 15) r c)) w)
    (offered : ∀ c w, (c,w) ∈ history → if MatchingContractionColumnEligible s merged c then
      LeastSlackEntry (absorbed.flatMap (fun r => normalizedOuterPairEntries prior cost effective (s.rr 15) r c)) w else w = none)
    (buckets : ∀ i < k*k, MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i =
      insertSlackCandidates (fresh.flatMap (contractionFreshPairInputs next newRole cost effective (s.rr 15) i))
        (history.foldl (contractionColumnPairUpdate merged i) (readMatchingPairBucket (k := k) s i))) :
    MatchingSearchOuterBuckets t next newRole cost effective := by
  let old := normalizedOuterPairEntries prior cost effective (s.rr 15)
  let updated := normalizedOuterPairEntries next cost effective (s.rr 15)
  let delta := fun a b : Fin k => fresh.flatMap (contractionFreshPairInputs next newRole cost effective (s.rr 15) (k*a.val+b.val))
  have source : ∀ u ∈ fresh, next u = merged := fun u hu => (shape.mergedFiber u).mpr (.inr hu)
  have existsFresh := contractionFreshPairOffers_mem next newRole cost effective (s.rr 15) fresh merged source
  have oldBase := shape.absorbedOuter merged shape.baseMember
  have atMerged (b : Fin k) (distinct : merged ≠ b) (outer : newRole b = 1)
      (w : Option (DualSlack (MatchingDualEvent k))) (bucket : LeastSlackEntry (old merged b) w) :
      LeastSlackEntry ((delta merged b).reverse ++ absorbed.flatMap (fun r => old r b))
        (insertSlackCandidates (delta merged b)
          (history.foldl (contractionColumnPairUpdate merged (k*merged.val+b.val)) w)) := by
    have eligible : MatchingContractionColumnEligible s merged b := ⟨(roleAt b).trans outer, distinct⟩
    apply LeastSlackEntry.insert_many
    exact contractionColumnPairFold_least distinct history bucket
      (fun d hd => List.mem_flatMap.mpr ⟨merged,shape.baseMember,hd⟩) (chosen b eligible)
      (fun w h => by simpa only [if_pos eligible] using offered b w h)
  have mergedMembers (b : Fin k) (distinct : merged ≠ b) (outer : newRole b = 1) (d : DualSlack (MatchingDualEvent k)) :
      d ∈ (delta merged b).reverse ++ absorbed.flatMap (fun r => old r b) ↔ d ∈ updated merged b := by
    rw [List.mem_append, List.mem_reverse, existsFresh,
      contractionPairEntries_mem prior next absorbed fresh cost effective (s.rr 15) merged b
        shape.mergedFiber (shape.survivorFiber b distinct.symm outer)]
    constructor
    · rintro (⟨u,hu,v,_,_,coords,edge⟩ | oldEdge)
      · rcases coords with ⟨_, hv⟩ | ⟨_, impossible⟩
        · exact Or.inr ⟨u,v,hu,(shape.survivorFiber b distinct.symm outer v).mp hv.symm,edge⟩
        · exact (distinct impossible.symm).elim
      · exact Or.inl oldEdge
    · rintro (oldEdge | ⟨u,v,hu,hv,edge⟩)
      · exact Or.inr oldEdge
      · have newV := (shape.survivorFiber b distinct.symm outer v).mpr hv
        exact Or.inl ⟨u,hu,v,by rwa [newV],by rwa [newV],Or.inl ⟨rfl,newV.symm⟩,edge⟩
  refine ⟨fun i hi => (buckets i hi).1, ?_, ?_⟩
  · intro a b distinct left right
    rw [clock, (buckets _ (matchingPairSlot_lt a b)).2]
    change LeastSlackEntry (updated a b) (insertSlackCandidates (delta a b)
      (history.foldl (contractionColumnPairUpdate merged (k*a.val+b.val)) (readMatchingPairBucket (k := k) s (k*a.val+b.val))))
    by_cases atLeft : a = merged
    · subst a
      exact (atMerged b distinct right _ (before.least merged b distinct oldBase
        (shape.survivorOuter b distinct.symm right))).of_mem_iff (mergedMembers b distinct right)
    by_cases atRight : b = merged
    · subst b
      have bucket := (before.least a merged distinct (shape.survivorOuter a atLeft left) oldBase).of_mem_iff
        (normalizedOuterPairEntries_swap_mem prior symmetric effective (s.rr 15) a merged)
      have opposite := contractionColumnPairFold_least distinct.symm history bucket
        (fun d hd => List.mem_flatMap.mpr ⟨merged, shape.baseMember, hd⟩)
        (chosen a ⟨(roleAt a).trans left, distinct.symm⟩)
        (fun w hw => by simpa only [if_pos (show MatchingContractionColumnEligible s merged a from
          ⟨(roleAt a).trans left, distinct.symm⟩)] using offered a w hw)
      rw [contractionColumnPairFold_swap merged a merged]
      apply (opposite.insert_many (delta a merged)).of_mem_iff
      intro d
      calc
        _ ↔ d ∈ (delta merged a).reverse ++ absorbed.flatMap (fun r => old r a) := by
          simp only [List.mem_append, List.mem_reverse]
          exact or_congr (contractionFreshPairOffers_swap next newRole cost effective (s.rr 15) fresh merged source a merged d) Iff.rfl
        _ ↔ d ∈ updated merged a := mergedMembers a distinct.symm left d
        _ ↔ _ := normalizedOuterPairEntries_swap_mem next symmetric effective (s.rr 15) merged a d
    have noOffers : delta a b = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro d hd
      obtain ⟨_,_,_,_,_,coords,_⟩ := (existsFresh a b d).mp hd
      exact coords.elim (fun p => atLeft p.1) (fun p => atRight p.2)
    rw [noOffers, contractionColumnPairFold_untouched merged a b history
      (fun _ _ _ p => (p.elim (fun h => atLeft h.1) (fun h => atRight h.2)).elim)]
    apply (before.least a b distinct (shape.survivorOuter a atLeft left) (shape.survivorOuter b atRight right)).of_mem_iff
    intro d
    simp only [updated, normalizedOuterPairEntries_mem, shape.survivorFiber a atLeft left, shape.survivorFiber b atRight right]
  · intro a b inactive
    have priorInactive : oldRole (prior a) ≠ 1 ∨ oldRole (prior b) ≠ 1 :=
      inactive.imp (fun off on => off (shape.outerPersists a on)) (fun off on => off (shape.outerPersists b on))
    have noOffers : delta a b = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro d hd
      obtain ⟨_,_,v,_,outer,coords,_⟩ := (existsFresh a b d).mp hd
      have baseOuter := shape.outerAtRepresentative merged shape.baseOuter
      rcases coords with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [shape.idempotent, baseOuter, outer] at inactive
    have noColumn (v w) (member : (v,w) ∈ history) (coords : (a = merged ∧ b = v) ∨ (a = v ∧ b = merged)) : w = none := by
      have hidden : ¬ MatchingContractionColumnEligible s merged v := by
        intro active
        have vOuter := shape.outerAtRepresentative v ((roleAt v).symm.trans active.1)
        have baseOuter := shape.outerAtRepresentative merged shape.baseOuter
        rcases coords with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [baseOuter, vOuter] at inactive
      simpa only [if_neg hidden] using offered v w member
    rw [(buckets _ (matchingPairSlot_lt a b)).2]
    change insertSlackCandidates (delta a b) _ = none
    rw [noOffers, contractionColumnPairFold_untouched merged a b history noColumn, before.inactive a b priorInactive] <;> rfl

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionPairMeaning

/-! matching/BlossomLaminarity.lean -/
section RppSource_BlossomLaminarity
namespace VehicleRoutingSurvey.Routing

variable {k : ℕ} {vertices : Finset (Fin k)} {cuts : Finset (Finset (Fin k))}







theorem TopLevelMatchingBlocks.contract_cuts_nested (blocks : TopLevelMatchingBlocks vertices cuts)
    {children : Finset (Finset (Fin k))} (top : children ⊆ vertices.image blocks.block)
    (nested : ∀ S ∈ cuts, ∀ u ∈ S, ∀ v ∈ S, blocks.block u = blocks.block v) :
    ∀ S ∈ insert (children.biUnion id) cuts, ∀ u ∈ S, ∀ v ∈ S,
      (blocks.contract children top).block u = (blocks.contract children top).block v := by
  have selected (w : Fin k) (inside : w ∈ children.biUnion id) : blocks.block w ∈ children := by
    obtain ⟨child, childMem, inChild⟩ := Finset.mem_biUnion.mp inside
    obtain ⟨x, xIn, childEq⟩ := Finset.mem_image.mp (top childMem)
    have same : blocks.block w = child := (blocks.same_of_mem xIn (childEq.symm ▸ inChild)).trans childEq
    rwa [same]
  intro S inS u inU v inV
  rcases Finset.mem_insert.mp inS with rfl | old
  · simp [TopLevelMatchingBlocks.contract, selected u inU, selected v inV]
  · simp only [TopLevelMatchingBlocks.contract, nested S old u inU v inV]





end VehicleRoutingSurvey.Routing
end RppSource_BlossomLaminarity

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

/-! matching/MatchingContractionIncomingMeaning.lean -/
section RppSource_MatchingContractionIncomingMeaning
namespace VehicleRoutingSurvey.Routing

def incomingEdgeAt {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ) (cost : Fin k → Fin k → ℝ)
    (effective : Fin k → ℝ) (v : Fin k) (d : DualSlack (MatchingDualEvent k)) : Prop :=
  ∃ u, rep u ≠ rep v ∧ role (rep u) = 1 ∧ role (rep v) ≠ 1 ∧
    matchingSearchRawEdge cost effective u v (if role (rep v) = 0 then 1 else 0) = d

/-- At a physical incoming row the neighbor scan identifies one original target;
the two outer selectors always lie below the incoming slab. -/
theorem outerRefreshIncoming_iff {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ) (cost : Fin k → Fin k → ℝ)
    (effective : Fin k → ℝ) (u w v : Fin k) (d : DualSlack (MatchingDualEvent k)) :
    outerRefreshRowInput rep role cost effective u w (k+v.val) = some d ↔
      w = v ∧ rep u ≠ rep w ∧ role (rep w) ≠ 1 ∧
      matchingSearchRawEdge cost effective u w (if role (rep w) = 0 then 1 else 0) = d := by
  have below (z : Fin k) : k+v.val ≠ z.val := by have h := z.isLt; omega
  by_cases same : rep u = rep w
  · simp [outerRefreshRowInput,same]
  by_cases outer : role (rep w) = 1
  · simp [outerRefreshRowInput,same,outerNeighborRowCandidate,outer,below]
  by_cases query : w = v
  · subst w
    simp [outerRefreshRowInput,same,outerNeighborRowCandidate,outer,matchingSearchRawEdge]
  · have other : v.val ≠ w.val := fun eq => query (Fin.ext eq).symm
    simp [outerRefreshRowInput,same,outerNeighborRowCandidate,outer,other,query]

theorem contractionIncomingOffers_mem {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (fresh : List (Fin k))
    (v : Fin k) (d : DualSlack (MatchingDualEvent k)) :
    d ∈ fresh.flatMap (contractionFreshRowInputs rep role cost effective (k+v.val)) ↔
      ∃ u ∈ fresh, rep u ≠ rep v ∧ role (rep v) ≠ 1 ∧
        matchingSearchRawEdge cost effective u v (if role (rep v) = 0 then 1 else 0) = d := by
  simp only [List.mem_flatMap,contractionFreshRowInputs,List.mem_filterMap,List.mem_finRange,true_and,outerRefreshIncoming_iff]
  constructor
  · rintro ⟨u,h,w,rfl,rest⟩
    exact ⟨u,h,rest⟩
  · rintro ⟨u,h,rest⟩
    exact ⟨u,h,v,rfl,rest⟩

/-- A promoted target loses its incoming row. Each surviving nonouter target
retains all its old outer neighbors and acquires exactly the newly outer ones. -/
theorem contractionIncomingEntries_iff {k : ℕ} (prior next : Fin k → Fin k) (oldRole newRole : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (fresh : List (Fin k))
    (outer : ∀ u, newRole (next u) = 1 ↔ oldRole (prior u) = 1 ∨ u ∈ fresh)
    (survive : ∀ u, u ∉ fresh → newRole (next u) = oldRole (prior u))
    (v : Fin k) (d : DualSlack (MatchingDualEvent k)) :
    incomingEdgeAt next newRole cost effective v d ↔
      (v ∉ fresh ∧ incomingEdgeAt prior oldRole cost effective v d) ∨
        d ∈ fresh.flatMap (contractionFreshRowInputs next newRole cost effective (k+v.val)) := by
  rw [contractionIncomingOffers_mem]
  constructor
  · rintro ⟨u,apart,on,off,datum⟩
    have stayed : v ∉ fresh := fun added => off ((outer v).mpr (.inr added))
    have role := survive v stayed
    rcases (outer u).mp on with old | added
    · apply Or.inl
      refine ⟨stayed,u,?_,old,?_,?_⟩
      · intro same
        exact off (role.trans (same ▸ old))
      · exact fun previous => off (role.trans previous)
      · rwa [← role]
    · exact Or.inr ⟨u,added,apart,off,datum⟩
  · rintro (⟨stayed,u,_,source,off,datum⟩ | ⟨u,added,apart,off,datum⟩)
    · have role := survive v stayed
      have after := (outer u).mpr (.inl source)
      refine ⟨u,?_,after,?_,?_⟩
      · intro same
        exact off (role.symm.trans (same ▸ after))
      · rwa [role]
      · rwa [role]
    · exact ⟨u,apart,(outer u).mpr (.inr added),off,datum⟩

theorem contractionColumnRowFold_above {k : ℕ} (merged : Fin k) (time : ℝ) {i : ℕ} (later : k ≤ i)
    (history : List (ContractionColumnWinner k)) (cached : Option (DualSlack (MatchingDualEvent k))) :
    history.foldl (contractionColumnRowUpdate merged time i) cached = cached := by
  induction history with
  | nil => rfl
  | cons record tail ih =>
    have outside := record.1.isLt
    have inside := merged.isLt
    have skip : ¬(i = merged.val ∨ i = record.1.val) := by omega
    simpa only [List.foldl_cons,contractionColumnRowUpdate,if_neg skip] using ih

/-- Interpret the real incoming-row reset, all column publications and the fresh
scan as the least entry of the new incoming group. -/
theorem contractionIncomingRow_least {k : ℕ} (prior next : Fin k → Fin k) (oldRole newRole : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (fresh : List (Fin k)) (merged v : Fin k) (clock : ℝ)
    (history : List (ContractionColumnWinner k)) (cached : Option (DualSlack (MatchingDualEvent k)))
    (oldEntries newEntries : List (DualSlack (MatchingDualEvent k)))
    (was : ∀ d, d ∈ oldEntries ↔ incomingEdgeAt prior oldRole cost effective v d)
    (isNow : ∀ d, d ∈ newEntries ↔ incomingEdgeAt next newRole cost effective v d)
    (old : LeastSlackEntry oldEntries cached)
    (outer : ∀ u, newRole (next u) = 1 ↔ oldRole (prior u) = 1 ∨ u ∈ fresh)
    (survive : ∀ u, u ∉ fresh → newRole (next u) = oldRole (prior u)) :
    LeastSlackEntry newEntries (insertSlackCandidates (fresh.flatMap (contractionFreshRowInputs next newRole cost effective (k+v.val)))
      (history.foldl (contractionColumnRowUpdate merged clock (k+v.val)) (if v ∈ fresh then none else cached))) := by
  let priorRows := if v ∈ fresh then [] else oldEntries
  have initial : LeastSlackEntry priorRows (if v ∈ fresh then none else cached) := by
    by_cases erased : v ∈ fresh
    · simp only [priorRows,if_pos erased]
      constructor <;> simp
    · simpa only [priorRows,if_neg erased] using old
  rw [contractionColumnRowFold_above merged clock (by omega)]
  apply (initial.insert_many _).of_mem_iff
  intro d
  rw [List.mem_append,List.mem_reverse,isNow,contractionIncomingEntries_iff prior next oldRole newRole cost effective fresh outer survive]
  by_cases wiped : v ∈ fresh <;> simp [priorRows,wiped,was,or_comm]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionIncomingMeaning

/-! matching/MatchingContractionRowMinimum.lean -/
section RppSource_MatchingContractionRowMinimum
namespace VehicleRoutingSurvey.Routing

private noncomputable def contractionRowColumnEntries {k : ℕ} (s : ArithmeticState) (merged : Fin k)
    (i : ℕ) (columns : Fin k → List (DualSlack (MatchingDualEvent k))) (v : Fin k) : List (DualSlack (MatchingDualEvent k)) :=
  if (i = merged.val ∨ i = v.val) ∧ MatchingContractionColumnEligible s merged v then
    (columns v).map (fun d => {d with slack := d.slack-(s.rr 15+s.rr 15)}) else []

private theorem contractionRowHistory_least {k : ℕ} (s : ArithmeticState) (merged : Fin k)
    (i : ℕ) (columns : Fin k → List (DualSlack (MatchingDualEvent k))) (history : List (ContractionColumnWinner k))
    (offered : ∀ v w, (v,w) ∈ history → if MatchingContractionColumnEligible s merged v then LeastSlackEntry (columns v) w else w = none)
    (prior : List (DualSlack (MatchingDualEvent k))) (cached : Option (DualSlack (MatchingDualEvent k)))
    (before : LeastSlackEntry prior cached) :
    LeastSlackEntry (prior ++ history.flatMap (fun h => contractionRowColumnEntries s merged i columns h.1))
      (history.foldl (contractionColumnRowUpdate merged (s.rr 15) i) cached) := by
  induction history generalizing prior cached with
  | nil => simpa using before
  | cons record tail ih =>
    obtain ⟨v,w⟩ := record
    have atColumn := offered v w List.mem_cons_self
    have one : LeastSlackEntry (prior ++ contractionRowColumnEntries s merged i columns v)
        (contractionColumnRowUpdate merged (s.rr 15) i cached (v,w)) := by
      by_cases target : i = merged.val ∨ i = v.val
      · by_cases outer : MatchingContractionColumnEligible s merged v
        · have least : LeastSlackEntry (columns v) w := by simpa only [if_pos outer] using atColumn
          simpa only [contractionRowColumnEntries, if_pos (And.intro target outer), contractionColumnRowUpdate,
            if_pos target, addContractionWinner] using before.insertMinimum (least.subtractSlackOffset (s.rr 15+s.rr 15))
        · have empty : w = none := by simpa only [if_neg outer] using atColumn
          simpa [contractionRowColumnEntries, contractionColumnRowUpdate, target, outer, empty, addContractionWinner] using before
      · simpa [contractionRowColumnEntries, contractionColumnRowUpdate, target] using before
    have result := ih (fun v w h => offered v w (List.mem_cons_of_mem _ h)) _ _ one
    simpa only [List.flatMap_cons, List.foldl_cons, List.append_assoc] using result

/-- Each eligible column contributes its entire covered group to the two selector
rows touched by its publication. This holds for the actual strict-improvement
fold, including duplicate witnesses and ties. -/
theorem contractionRowFold_least {k : ℕ} (s : ArithmeticState) (merged : Fin k)
    (i : ℕ) (columns : Fin k → List (DualSlack (MatchingDualEvent k))) (history : List (ContractionColumnWinner k))
    (chosen : ∀ v, MatchingContractionColumnEligible s merged v → ∃ w, (v,w) ∈ history ∧ LeastSlackEntry (columns v) w)
    (offered : ∀ v w, (v,w) ∈ history → if MatchingContractionColumnEligible s merged v then LeastSlackEntry (columns v) w else w = none)
    (prior final : List (DualSlack (MatchingDualEvent k))) (cached : Option (DualSlack (MatchingDualEvent k)))
    (before : LeastSlackEntry prior cached)
    (members : ∀ d, d ∈ final ↔ d ∈ prior ∨ ∃ v, (i = merged.val ∨ i = v.val) ∧ MatchingContractionColumnEligible s merged v ∧
      ∃ e ∈ columns v, {e with slack := e.slack-(s.rr 15+s.rr 15)} = d) :
    LeastSlackEntry final (history.foldl (contractionColumnRowUpdate merged (s.rr 15) i) cached) := by
  apply (contractionRowHistory_least s merged i columns history offered prior cached before).of_mem_iff
  intro d
  rw [members, List.mem_append]
  apply or_congr Iff.rfl
  constructor
  · intro present
    obtain ⟨⟨v,w⟩,_,edge⟩ := List.mem_flatMap.mp present
    by_cases both : (i = merged.val ∨ i = v.val) ∧ MatchingContractionColumnEligible s merged v
    · have offers : d ∈ (columns v).map (fun e => {e with slack := e.slack-(s.rr 15+s.rr 15)}) := by
        simpa only [contractionRowColumnEntries, if_pos both] using edge
      exact ⟨v,both.1,both.2,List.mem_map.mp offers⟩
    · simp [contractionRowColumnEntries, both] at edge
  · rintro ⟨v,touched,outer,e,atColumn,edge⟩
    obtain ⟨w,hist,_⟩ := chosen v outer
    refine List.mem_flatMap.mpr ⟨(v,w),hist,?_⟩
    simpa only [contractionRowColumnEntries, if_pos (And.intro touched outer)] using
      (List.mem_map.mpr ⟨e,atColumn,edge⟩ : d ∈ (columns v).map (fun x => {x with slack := x.slack-(s.rr 15+s.rr 15)}))

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionRowMinimum

/-! matching/MatchingContractionOuterMeaning.lean -/
section RppSource_MatchingContractionOuterMeaning
namespace VehicleRoutingSurvey.Routing

def outerEdgeAt {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ) (cost : Fin k → Fin k → ℝ)
    (effective : Fin k → ℝ) (i : Fin k) (d : DualSlack (MatchingDualEvent k)) : Prop :=
  ∃ u v, rep u = i ∧ rep u ≠ rep v ∧ role (rep u) = 1 ∧ role (rep v) = 1 ∧ matchingSearchRawEdge cost effective u v 2 = d

theorem matchingSearchRawEdge_swap {k : ℕ} {cost : Fin k → Fin k → ℝ} (symmetric : ∀ u v, cost u v = cost v u)
    (effective : Fin k → ℝ) (u v : Fin k) (rate : ℝ) :
    matchingSearchRawEdge cost effective u v rate = matchingSearchRawEdge cost effective v u rate := by
  have key : cost u v-effective u-effective v = cost v u-effective v-effective u := by rw [symmetric u v]; ring
  simp only [matchingSearchRawEdge,key,show s(u,v) = s(v,u) from Sym2.eq_swap]

private def contractionOldOuterOffer {k : ℕ} (prior : Fin k → Fin k) (newRole : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (absorbed : List (Fin k)) (merged row : Fin k)
    (d : DualSlack (MatchingDualEvent k)) : Prop :=
  ∃ c, merged ≠ c ∧ newRole c = 1 ∧ (row = merged ∨ row = c) ∧
    ∃ u v, prior u ∈ absorbed ∧ prior v = c ∧ matchingSearchRawEdge cost effective u v 2 = d

private theorem contractionFreshOuterOffers_mem {k : ℕ} (next : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (fresh : List (Fin k)) (merged row : Fin k)
    (source : ∀ u ∈ fresh, next u = merged) (d : DualSlack (MatchingDualEvent k)) :
    d ∈ fresh.flatMap (contractionFreshRowInputs next role cost effective row.val) ↔
      ∃ u ∈ fresh, ∃ v, merged ≠ next v ∧ role (next v) = 1 ∧ (row = merged ∨ row = next v) ∧
        matchingSearchRawEdge cost effective u v 2 = d := by
  have offer (u : Fin k) (hu : u ∈ fresh) (v : Fin k) :
      outerRefreshRowInput next role cost effective u v row.val = some d ↔
        merged ≠ next v ∧ role (next v) = 1 ∧ (row = merged ∨ row = next v) ∧ matchingSearchRawEdge cost effective u v 2 = d := by
    have away : row.val ≠ k+v.val := by have h := row.isLt; omega
    by_cases same : merged = next v
    · simp [outerRefreshRowInput,source u hu,same]
    by_cases on : role (next v) = 1
    · by_cases atRow : row = merged ∨ row = next v
      · have rowWord : row.val = merged.val ∨ row.val = (next v).val := atRow.imp (congrArg Fin.val) (congrArg Fin.val)
        simp [outerRefreshRowInput,source u hu,same,outerNeighborRowCandidate,on,rowWord,atRow,matchingSearchRawEdge]
      · have neither : ¬(row.val = merged.val ∨ row.val = (next v).val) := fun h => atRow (h.imp Fin.ext Fin.ext)
        simp [outerRefreshRowInput,source u hu,same,outerNeighborRowCandidate,on,neither,atRow]
    · simp [outerRefreshRowInput,source u hu,same,outerNeighborRowCandidate,on,away]
  simp only [List.mem_flatMap,contractionFreshRowInputs,List.mem_filterMap,List.mem_finRange,true_and]
  constructor <;> rintro ⟨u,hu,v,present⟩
  · exact ⟨u,hu,v,(offer u hu v).mp present⟩
  · exact ⟨u,hu,v,(offer u hu v).mpr present⟩

/-- Separate all exterior post-contraction edges according to the three sources
that physically populate the outer selector: untouched old row, published old
outer columns and original vertices newly promoted to outer status. -/
private theorem contractionOuterGroups_mem {k : ℕ} (prior next : Fin k → Fin k) (oldRole newRole : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (symmetric : ∀ u v, cost u v = cost v u) (effective : Fin k → ℝ)
    (absorbed fresh : List (Fin k)) (merged row : Fin k)
    (shape : MatchingContractionPairGeometry prior next oldRole newRole merged absorbed fresh)
    (kept : Fin k → Prop) (outside : ∀ c, newRole c = 1 → c ≠ merged → kept c)
    (fibers : ∀ c, kept c → ∀ u, prior u = c ↔ next u = c) (d : DualSlack (MatchingDualEvent k)) :
    outerEdgeAt next newRole cost effective row d ↔
      (kept row ∧ outerEdgeAt prior oldRole cost effective row d) ∨
      contractionOldOuterOffer prior newRole cost effective absorbed merged row d ∨
      d ∈ fresh.flatMap (contractionFreshRowInputs next newRole cost effective row.val) := by
  have source : ∀ u ∈ fresh, next u = merged := fun u hu => (shape.mergedFiber u).mpr (.inr hu)
  rw [contractionFreshOuterOffers_mem next newRole cost effective fresh merged row source]
  have swap := fun u v => matchingSearchRawEdge_swap symmetric effective u v 2
  constructor
  · rintro ⟨u,v,atRow,separate,onU,onV,edge⟩
    have crosses (x y : Fin k) (inBase : next x = merged) (away : merged ≠ next y) (yOuter : newRole (next y) = 1)
        (query : row = merged ∨ row = next y) (event : matchingSearchRawEdge cost effective x y 2 = d) :
        contractionOldOuterOffer prior newRole cost effective absorbed merged row d ∨
          ∃ u ∈ fresh, ∃ v, merged ≠ next v ∧ newRole (next v) = 1 ∧ (row = merged ∨ row = next v) ∧
            matchingSearchRawEdge cost effective u v 2 = d := by
      rcases (shape.mergedFiber x).mp inBase with old | added
      · exact .inl ⟨next y,away,yOuter,query,x,y,old,(shape.survivorFiber _ away.symm yOuter y).mp rfl,event⟩
      · exact .inr ⟨x,added,y,away,yOuter,query,event⟩
    by_cases left : next u = merged
    · exact Or.inr (crosses u v left (left ▸ separate) onV (Or.inl (atRow.symm.trans left)) edge)
    by_cases right : next v = merged
    · exact Or.inr (crosses v u right (Ne.symm left) onU (Or.inr atRow.symm) ((swap v u).trans edge))
    have hu := (shape.survivorFiber (next u) left onU u).mp rfl
    have hv := (shape.survivorFiber (next v) right onV v).mp rfl
    refine Or.inl ⟨atRow ▸ outside (next u) onU left,u,v,hu.trans atRow,?_,?_,?_,edge⟩
    · rwa [hu,hv]
    · rw [hu]; exact shape.survivorOuter _ left onU
    · rw [hv]; exact shape.survivorOuter _ right onV
  · have baseEdge (u v : Fin k) (hu : next u = merged) (away : merged ≠ next v) (on : newRole (next v) = 1)
        (atRow : row = merged ∨ row = next v) (edge : matchingSearchRawEdge cost effective u v 2 = d) :
        outerEdgeAt next newRole cost effective row d := by
      have inside : newRole (next u) = 1 := hu.symm ▸ shape.baseOuter
      have distinct : next u ≠ next v := hu.symm ▸ away
      rcases atRow with left | right
      · exact ⟨u,v,hu.trans left.symm,distinct,inside,on,edge⟩
      · exact ⟨v,u,right.symm,distinct.symm,on,inside,(swap v u).trans edge⟩
    rintro (⟨keep,u,v,atRow,distinct,onU,onV,edge⟩ | ⟨c,away,on,query,u,v,inBase,atCol,edge⟩ | ⟨u,hu,v,away,on,query,edge⟩)
    · have newRow := (fibers row keep u).mp atRow
      refine ⟨u,v,newRow,?_,shape.outerPersists u onU,shape.outerPersists v onV,edge⟩
      intro same
      exact distinct (atRow.trans ((fibers row keep v).mpr (same.symm.trans newRow)).symm)
    · have newCol := (shape.survivorFiber c away.symm on v).mpr atCol
      apply baseEdge u v ((shape.mergedFiber u).mpr (.inl inBase)) _ _ _ edge <;> rwa [newCol]
    · exact baseEdge u v (source u hu) away on query edge

private theorem contractionOldOuterOffer_iff {k : ℕ} (s : ArithmeticState)
    (prior : Fin k → Fin k) (newRole : Fin k → ℕ) (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ)
    (absorbed : List (Fin k)) (merged row : Fin k) (roleAt : ∀ v : Fin k, s.nm (s.nr 51+v.val) = newRole v)
    (d : DualSlack (MatchingDualEvent k)) :
    contractionOldOuterOffer prior newRole cost effective absorbed merged row d ↔
      ∃ v, (row.val = merged.val ∨ row.val = v.val) ∧ MatchingContractionColumnEligible s merged v ∧
        ∃ e ∈ absorbed.flatMap (fun r => normalizedOuterPairEntries prior cost effective (s.rr 15) r v),
          {e with slack := e.slack-(s.rr 15+s.rr 15)} = d := by
  have raw (u v : Fin k) : (let e := normalizedOuterEdge cost effective (s.rr 15) u v
      {e with slack := e.slack-(s.rr 15+s.rr 15)}) = matchingSearchRawEdge cost effective u v 2 := by
    simp [normalizedOuterEdge,matchingSearchRawEdge]
  constructor
  · rintro ⟨c,away,on,query,u,v,inBase,atCol,edge⟩
    exact ⟨c,query.imp (congrArg Fin.val) (congrArg Fin.val),⟨(roleAt c).trans on,away⟩,
      normalizedOuterEdge cost effective (s.rr 15) u v,List.mem_flatMap.mpr ⟨prior u,inBase,
        normalizedOuterPairEntries_mem.mpr ⟨u,v,rfl,atCol,rfl⟩⟩,(raw u v).trans edge⟩
  · rintro ⟨c,query,eligible,e,h,edge⟩
    obtain ⟨r,hr,fields⟩ := List.mem_flatMap.mp h
    obtain ⟨u,v,atRow,atCol,rfl⟩ := normalizedOuterPairEntries_mem.mp fields
    exact ⟨c,eligible.2,(roleAt c).symm.trans eligible.1,query.imp Fin.ext Fin.ext,u,v,atRow.symm ▸ hr,
      atCol,(raw u v).symm.trans edge⟩

/-- The physical outer selector fold is the least entry over the whole new
outer row. An old row survives precisely at a representative outside the cycle. -/
theorem contractionOuterRow_least {k : ℕ} (s : ArithmeticState) (prior next : Fin k → Fin k) (oldRole newRole : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (symmetric : ∀ u v, cost u v = cost v u) (effective : Fin k → ℝ)
    (absorbed fresh : List (Fin k)) (merged row : Fin k)
    (shape : MatchingContractionPairGeometry prior next oldRole newRole merged absorbed fresh)
    (kept : Fin k → Prop) [DecidablePred kept] (outside : ∀ c, newRole c = 1 → c ≠ merged → kept c)
    (fibers : ∀ c, kept c → ∀ u, prior u = c ↔ next u = c)
    (roleAt : ∀ v : Fin k, s.nm (s.nr 51+v.val) = newRole v)
    (oldEntries newEntries : List (DualSlack (MatchingDualEvent k))) (cached : Option (DualSlack (MatchingDualEvent k)))
    (was : ∀ d, d ∈ oldEntries ↔ outerEdgeAt prior oldRole cost effective row d)
    (isNow : ∀ d, d ∈ newEntries ↔ outerEdgeAt next newRole cost effective row d)
    (old : LeastSlackEntry oldEntries cached) (history : List (ContractionColumnWinner k))
    (chosen : ∀ v, MatchingContractionColumnEligible s merged v → ∃ w, (v,w) ∈ history ∧
      LeastSlackEntry (absorbed.flatMap (fun r => normalizedOuterPairEntries prior cost effective (s.rr 15) r v)) w)
    (offered : ∀ v w, (v,w) ∈ history → if MatchingContractionColumnEligible s merged v then
      LeastSlackEntry (absorbed.flatMap (fun r => normalizedOuterPairEntries prior cost effective (s.rr 15) r v)) w else w = none) :
    LeastSlackEntry newEntries (insertSlackCandidates (fresh.flatMap (contractionFreshRowInputs next newRole cost effective row.val))
      (history.foldl (contractionColumnRowUpdate merged (s.rr 15) row.val) (if kept row then cached else none))) := by
  classical
  let seed := if kept row then oldEntries else []
  let columns := fun v : Fin k => absorbed.flatMap (fun r => normalizedOuterPairEntries prior cost effective (s.rr 15) r v)
  let parts := fun v : Fin k => if (row.val = merged.val ∨ row.val = v.val) ∧ MatchingContractionColumnEligible s merged v then
      (columns v).map (fun e => {e with slack := e.slack-(s.rr 15+s.rr 15)}) else []
  let full := seed ++ (List.finRange k).flatMap parts
  have initial : LeastSlackEntry seed (if kept row then cached else none) := by
    by_cases retain : kept row
    · simpa only [seed,if_pos retain] using old
    · simp only [seed,if_neg retain]; constructor <;> simp
  have hits (d : DualSlack (MatchingDualEvent k)) : d ∈ (List.finRange k).flatMap parts ↔
      ∃ v, (row.val = merged.val ∨ row.val = v.val) ∧ MatchingContractionColumnEligible s merged v ∧
        ∃ e ∈ columns v, {e with slack := e.slack-(s.rr 15+s.rr 15)} = d := by
    simp only [List.mem_flatMap,List.mem_finRange,true_and]
    apply exists_congr
    intro v
    by_cases hit : (row.val = merged.val ∨ row.val = v.val) ∧ MatchingContractionColumnEligible s merged v
    · simp only [parts,if_pos hit,List.mem_map,hit.1,hit.2,true_and]
    · simp only [parts,if_neg hit,List.not_mem_nil]
      tauto
  have initialPlus := contractionRowFold_least s merged row.val columns history chosen offered seed full _ initial
    (fun d => by simp only [full,List.mem_append,hits])
  apply (initialPlus.insert_many _).of_mem_iff
  intro d
  rw [isNow,contractionOuterGroups_mem prior next oldRole newRole cost symmetric effective absorbed fresh merged row shape kept outside fibers,
    List.mem_append,List.mem_reverse,show d ∈ full ↔ d ∈ seed ∨ d ∈ (List.finRange k).flatMap parts from List.mem_append,hits,
    ← contractionOldOuterOffer_iff s prior newRole cost effective absorbed merged row roleAt]
  by_cases retain : kept row <;> simp only [seed,retain,if_true,if_false,true_and,false_and,List.not_mem_nil,was] <;> tauto

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionOuterMeaning

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

theorem contractionFreshRowInputs_cut {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (fresh : List (Fin k)) (i : Fin k) :
    fresh.flatMap (contractionFreshRowInputs rep role cost effective (2*k+i.val)) = [] := by
  have absent (u v : Fin k) : outerRefreshRowInput rep role cost effective u v (2*k+i.val) = none := by
    have uBound := (rep u).isLt
    have vBound := (rep v).isLt
    have index := v.isLt
    simp [outerRefreshRowInput,outerNeighborRowCandidate,show 2*k+i.val ≠ (rep u).val by omega,
      show 2*k+i.val ≠ (rep v).val by omega,show 2*k+i.val ≠ k+v.val by omega]
  simp [contractionFreshRowInputs,absent]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionCutMeaning

/-! matching/MatchingContractClearRows.lean -/
section RppSource_MatchingContractClearRows
namespace VehicleRoutingSurvey.Routing

/-- Erase the two selector IDs belonging to one absorbed block. Every other
candidate, dictionary word, and real cache entry remains readable as before. -/
theorem clearContractedCandidateRows_effect (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 23 = 0) :
    ∃ t steps, steps ≤ 9 ∧ BlockRuns clearContractedCandidateRows steps s t ∧ t.halted = false ∧
      (∀ r, r ≠ 6 → r ≠ 10 → t.nr r = s.nr r) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ addr, t.nm addr =
        if s.nm (s.nr 89+s.nr 7) ≠ 0 ∧
          (addr = s.nr 58+s.nr 7 ∨ addr = s.nr 58+(2*s.nr 55+s.nr 7)) then 0 else s.nm addr := by
  by_cases skip : s.nm (s.nr 89+s.nr 7) ≤ s.nr 23
  · let t := (arithmeticStep clearContractedCandidateRows)^[3] s
    have final : t.pc = clearContractedCandidateRows.length ∧ t.halted = false ∧
        t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
      simp [t, clearContractedCandidateRows, arithmeticStep, entry, running, skip, Function.iterate_succ_apply']
    have empty : s.nm (s.nr 89+s.nr 7) = 0 := by omega
    refine ⟨t, 3, by decide, BlockRuns.of_running_exit rfl final.2.1 final.1, final.2.1, ?_,
      final.2.2.2.1, final.2.2.2.2, ?_⟩
    · intro r away6 away10
      simp [t, clearContractedCandidateRows, arithmeticStep, entry, running, skip, Function.iterate_succ_apply', away6, away10]
    · intro addr
      simp [final.2.2.1, empty]
  · have present : s.nm (s.nr 89+s.nr 7) ≠ 0 := by omega
    let t := (arithmeticStep clearContractedCandidateRows)^[9] s
    have final : t.pc = clearContractedCandidateRows.length ∧ t.halted = false ∧
        t.nm = Function.update (Function.update s.nm (s.nr 58+s.nr 7) 0)
          (s.nr 58+(2*s.nr 55+s.nr 7)) 0 ∧ t.rm = s.rm ∧ t.rr = s.rr := by
      simp [t, clearContractedCandidateRows, arithmeticStep, entry, running, zero, present,
        Function.iterate_succ_apply', two_mul]
    refine ⟨t, 9, le_rfl, BlockRuns.of_running_exit rfl final.2.1 final.1, final.2.1, ?_,
      final.2.2.2.1, final.2.2.2.2, ?_⟩
    · intro r away6 away10
      simp [t, clearContractedCandidateRows, arithmeticStep, entry, running, skip, Function.iterate_succ_apply', away6, away10]
    · intro addr
      rw [final.2.2.1]
      by_cases cut : addr = s.nr 58+(2*s.nr 55+s.nr 7)
      · simp [cut, present]
      · rw [Function.update_of_ne cut]
        by_cases row : addr = s.nr 58+s.nr 7
        · simp [row, present]
        · simp [Function.update_of_ne row, cut, row, present]

/-- Invalidate the incoming row of the newly outer original in the scan list. -/
theorem clearPromotedIncomingCandidate_effect (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 23 = 0) :
    ∃ t, BlockRuns clearPromotedIncomingCandidate 5 s t ∧ t.halted = false ∧
      (∀ r, r ≠ 6 → r ≠ 10 → t.nr r = s.nr r) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      t.nm = Function.update s.nm (s.nr 58+(s.nr 55+s.nm (s.nr 88+s.nr 7))) 0 := by
  let t := (arithmeticStep clearPromotedIncomingCandidate)^[5] s
  have final : t.pc = clearPromotedIncomingCandidate.length ∧ t.halted = false ∧
      t.nm = Function.update s.nm (s.nr 58+(s.nr 55+s.nm (s.nr 88+s.nr 7))) 0 ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, clearPromotedIncomingCandidate, arithmeticStep, entry, running, zero, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl final.2.1 final.1, final.2.1, ?_, final.2.2.2.1, final.2.2.2.2, final.2.2.1⟩
  intro r away6 away10
  simp [t, clearPromotedIncomingCandidate, arithmeticStep, entry, running, Function.iterate_succ_apply', away6, away10]

private structure ContractionClearProgress (s : ArithmeticState) (slots : ℕ → List ℕ) (count : ℕ)
    (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  running : m.halted = false
  index : m.nr 7 = count
  fixed : ∀ r, r ≠ 6 → r ≠ 7 → r ≠ 10 → m.nr r = s.nr r
  natural : ∀ a, m.nm a = if a ∈ (List.range count).flatMap slots then 0 else s.nm a
  real : m.rm = s.rm
  realRegisters : m.rr = s.rr

private theorem contractionClearLoop {s : ArithmeticState} (limit n budget : ℕ) (body : List ArithmeticInstruction)
    (slots : ℕ → List ℕ) (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (limitAt : s.nr limit = n) (no6 : limit ≠ 6) (no7 : limit ≠ 7) (no10 : limit ≠ 10)
    (scope : ∀ i < n, ∀ a ∈ slots i, s.nr 58 ≤ a ∧ a < s.nr 58+s.nr 61)
    (cell : ∀ i < n, ∀ m : ArithmeticState, m.pc = 0 → m.halted = false → m.nr 7 = i →
      (∀ r, r ≠ 6 → r ≠ 7 → r ≠ 10 → m.nr r = s.nr r) →
      (∀ a, a < s.nr 58 ∨ s.nr 58+s.nr 61 ≤ a → m.nm a = s.nm a) →
      ∃ t steps, steps ≤ budget ∧ BlockRuns body steps m t ∧ t.halted = false ∧
        (∀ r, r ≠ 6 → r ≠ 10 → t.nr r = m.nr r) ∧ t.rm = m.rm ∧ t.rr = m.rr ∧
        ∀ a, t.nm a = if a ∈ slots i then 0 else m.nm a) :
    ∃ t steps, steps ≤ n*(budget+3)+2 ∧ BlockRuns (countedLoopFromZero 9 7 limit body) steps s t ∧
      t.halted = false ∧ (∀ r, r ≠ 6 → r ≠ 7 → r ≠ 10 → t.nr r = s.nr r) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ a, t.nm a = if a ∈ (List.range n).flatMap slots then 0 else s.nm a := by
  let inv := ContractionClearProgress s slots
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, by simp, rfl, rfl⟩
    intro r _ away _
    exact Function.update_of_ne away _ _
  have next (i : ℕ) (inside : i < n) (m : ArithmeticState) (h : inv i m) :
      ∃ t steps, steps ≤ budget ∧ BlockRuns body steps m t ∧ t.halted = false ∧
        inv (i+1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7+t.nr 9)} := by
    have outside (a : ℕ) (safe : a < s.nr 58 ∨ s.nr 58+s.nr 61 ≤ a) : m.nm a = s.nm a := by
      have absent : a ∉ (List.range i).flatMap slots := by
        intro inSlots
        obtain ⟨j, hj, word⟩ := List.mem_flatMap.mp inSlots
        have contained := scope j ((List.mem_range.mp hj).trans inside) a word
        omega
      rw [h.natural, if_neg absent]
    obtain ⟨t, steps, bound, run, live, kept, memories, reals, written⟩ :=
      cell i inside m h.entry h.running h.index h.fixed outside
    have mOne := (h.fixed 9 (by decide) (by decide) (by decide)).trans one
    refine ⟨t, steps, bound, run, live, rfl, live, ?_, ?_, ?_, memories.trans h.real, reals.trans h.realRegisters⟩
    · simp [kept 7 (by decide) (by decide), kept 9 (by decide) (by decide), h.index, mOne]
    · intro r h6 h7 h10
      exact (Function.update_of_ne h7 _ _).trans ((kept r h6 h10).trans (h.fixed r h6 h7 h10))
    · intro a
      change t.nm a = _
      rw [written, h.natural, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      by_cases now : a ∈ slots i <;> simp [List.mem_append, now]
  obtain ⟨t, steps, completed, cost, run⟩ := countedLoopFromZero_bounded 9 7 limit n budget body inv
    (s := s) entry running initial
    (fun _ _ h => ⟨h.entry, h.running, h.index, (h.fixed limit no6 no7 no10).trans limitAt⟩) next
  exact ⟨_, steps, by omega, run, completed.running, completed.fixed, completed.real, completed.realRegisters, completed.natural⟩

def contractionMaskedIdSlots (s : ArithmeticState) (i : ℕ) : List ℕ :=
  if s.nm (s.nr 89+i) ≠ 0 then [s.nr 58+i, s.nr 58+(2*s.nr 55+i)] else []

theorem clearContractedCandidateRows_loop {s : ArithmeticState} (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 9 = 1) (zero : s.nr 23 = 0) (rows : s.nr 61 = 3*s.nr 55)
    (markAfter : s.nr 58+s.nr 61 ≤ s.nr 89) :
    ∃ t steps, steps ≤ 12*s.nr 55+2 ∧
      BlockRuns (countedLoopFromZero 9 7 55 clearContractedCandidateRows) steps s t ∧ t.halted = false ∧
      (∀ r, r ≠ 6 → r ≠ 7 → r ≠ 10 → t.nr r = s.nr r) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ a, t.nm a = if a ∈ (List.range (s.nr 55)).flatMap (contractionMaskedIdSlots s) then 0 else s.nm a := by
  simpa only [Nat.mul_comm 12] using contractionClearLoop 55 (s.nr 55) 9 clearContractedCandidateRows
    (contractionMaskedIdSlots s) entry running one rfl (by decide) (by decide) (by decide) (by
      intro i inside a hit
      unfold contractionMaskedIdSlots at hit
      split at hit
      · simp at hit
        omega
      · simp at hit) (by
      intro i _ m start live atIndex fixed outside
      have port (r : ℕ) (a : r ≠ 6 := by decide) (b : r ≠ 7 := by decide) (c : r ≠ 10 := by decide) := fixed r a b c
      obtain ⟨t, steps, cap, run, ready, next, real, registers, effect⟩ :=
        clearContractedCandidateRows_effect m start live ((port 23).trans zero)
      refine ⟨t, steps, cap, run, ready, next, real, registers, ?_⟩
      intro address
      rw [effect, port 89, atIndex, port 58, port 55, outside _ (.inr (by omega))]
      by_cases hit : s.nm (s.nr 89+i) ≠ 0 <;> simp [contractionMaskedIdSlots, hit])

def contractionPromotedIdSlots (s : ArithmeticState) (i : ℕ) : List ℕ :=
  [s.nr 58+(s.nr 55+s.nm (s.nr 88+i))]

theorem clearPromotedIncomingCandidate_loop {s : ArithmeticState} (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 9 = 1) (zero : s.nr 23 = 0) (rows : s.nr 61 = 3*s.nr 55)
    (freshAfter : s.nr 58+s.nr 61 ≤ s.nr 88) (freshIn : ∀ j < s.nr 99, s.nm (s.nr 88+j) < s.nr 55) :
    ∃ t steps, steps ≤ 8*s.nr 99+2 ∧
      BlockRuns (countedLoopFromZero 9 7 99 clearPromotedIncomingCandidate) steps s t ∧ t.halted = false ∧
      (∀ r, r ≠ 6 → r ≠ 7 → r ≠ 10 → t.nr r = s.nr r) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ a, t.nm a = if a ∈ (List.range (s.nr 99)).flatMap (contractionPromotedIdSlots s) then 0 else s.nm a := by
  simpa only [Nat.mul_comm 8] using contractionClearLoop 99 (s.nr 99) 5 clearPromotedIncomingCandidate
    (contractionPromotedIdSlots s) entry running one rfl (by decide) (by decide) (by decide) (by
      intro i inside a hit
      have h := freshIn i inside
      simp only [contractionPromotedIdSlots, List.mem_singleton] at hit
      omega) (by
      intro i _ m start live atIndex fixed outside
      have port (r : ℕ) (a : r ≠ 6 := by decide) (b : r ≠ 7 := by decide) (c : r ≠ 10 := by decide) := fixed r a b c
      obtain ⟨t, run, ready, next, real, registers, effect⟩ :=
        clearPromotedIncomingCandidate_effect m start live ((port 23).trans zero)
      refine ⟨t, 5, le_rfl, run, ready, next, real, registers, ?_⟩
      intro address
      rw [effect, port 88, atIndex, port 58, port 55, outside _ (.inr (by omega))]
      simp [Function.update_apply, contractionPromotedIdSlots])

theorem candidateIdClear_cache {k : ℕ} (cutAt : Fin k → Finset (Fin k)) {s t : ArithmeticState}
    (layout : MatchingCacheLayout k s) (cleared : List ℕ)
    (scope : ∀ a ∈ cleared, s.nr 58 ≤ a ∧ a < s.nr 58+s.nr 61)
    (natural : ∀ a, t.nm a = if a ∈ cleared then 0 else s.nm a) (real : t.rm = s.rm)
    (fixed : ∀ r ≥ 50, t.nr r = s.nr r)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k*k, MatchingPairBucketValid k s i) :
    MatchingCacheFootprint k s t ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i =
        if s.nr 58+i ∈ cleared then none else readMatchingCandidate cutAt s i) ∧
      (∀ i < k*k, MatchingPairBucketValid k t i ∧
        readMatchingPairBucket (k := k) t i = readMatchingPairBucket (k := k) s i) := by
  have port (r : ℕ) (safe : 50 ≤ r := by decide) := fixed r safe
  have ids := layout.idsBefore
  have after := layout.recordsBefore
  have keeps (a : ℕ) (escape : a < s.nr 58 ∨ s.nr 58+s.nr 61 ≤ a) : t.nm a = s.nm a := by
    rw [natural, if_neg (fun found => by have h := scope a found; omega)]
  refine ⟨⟨fun addr safe => keeps addr (by omega), fun a _ => congrFun real a⟩, ?_, ?_⟩
  · intro i hi
    by_cases wipe : s.nr 58+i ∈ cleared
    · have id : t.nm (t.nr 58+i) = 0 := by rw [port 58, natural, if_pos wipe]
      simp [MatchingCandidateRowValid, readMatchingCandidate, id, wipe, decodeMatchingDictionaryEvent]
    · have id : t.nm (t.nr 58+i) = s.nm (s.nr 58+i) := by rw [port 58, natural, if_neg wipe]
      have decode : decodeMatchingDictionaryEvent k cutAt t (s.nm (s.nr 58+i)) =
          decodeMatchingDictionaryEvent k cutAt s (s.nm (s.nr 58+i)) := by
        rcases rows i hi with empty | ⟨chosen, _⟩
        · simp [decodeMatchingDictionaryEvent, empty]
        · unfold decodeMatchingDictionaryEvent
          rw [chosen, port 54]
          have cell : t.nm (s.nr 54+((i+1-1)+(i+1-1))) = s.nm (s.nr 54+((i+1-1)+(i+1-1))) :=
            keeps _ (.inr (by omega))
          have next : t.nm (s.nr 54+((i+1-1)+(i+1-1))+1) = s.nm (s.nr 54+((i+1-1)+(i+1-1))+1) :=
            keeps _ (.inr (by omega))
          simp only [cell, next]
      refine ⟨?_, ?_⟩
      · simpa only [MatchingCandidateRowValid, id, decode] using rows i hi
      · simp only [readMatchingCandidate, if_neg wipe, id, decode, port 59, port 60, real]
  · intro i hi
    have first : t.nm (t.nr 65+(i+i)) = s.nm (s.nr 65+(i+i)) := by rw [port 65, keeps _ (.inr (by omega))]
    have second : t.nm (t.nr 65+(i+i)+1) = s.nm (s.nr 65+(i+i)+1) := by rw [port 65, keeps _ (.inr (by omega))]
    exact ⟨by simpa only [MatchingPairBucketValid, first, second] using buckets i hi,
      by simp only [readMatchingPairBucket, first, second, port 66, real]⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractClearRows

/-! matching/MatchingContractionCacheSeed.lean -/
section RppSource_MatchingContractionCacheSeed
namespace VehicleRoutingSurvey.Routing

def seedMatchingContractionCache : List ArithmeticInstruction :=
  [.natConst 23 0, .natConst 14 0, .natAdd 26 12 23]

def clearMatchingContractionIds : List ArithmeticInstruction :=
  appendBlock seedMatchingContractionCache
    (appendBlock (countedLoopFromZero 9 7 55 clearContractedCandidateRows)
      (countedLoopFromZero 9 7 99 clearPromotedIncomingCandidate))

def matchingContractionClearedAddresses (s : ArithmeticState) : List ℕ :=
  (List.range (s.nr 55)).flatMap (contractionMaskedIdSlots s) ++
    (List.range (s.nr 99)).flatMap (contractionPromotedIdSlots s)

private theorem contractionMaskedIdSlots_inside {s : ArithmeticState} (rows : s.nr 61 = 3*s.nr 55)
    {a : ℕ} (present : a ∈ (List.range (s.nr 55)).flatMap (contractionMaskedIdSlots s)) :
    s.nr 58 ≤ a ∧ a < s.nr 58+s.nr 61 := by
  obtain ⟨i, hi, used⟩ := List.mem_flatMap.mp present
  have inside := List.mem_range.mp hi
  unfold contractionMaskedIdSlots at used
  split at used
  · simp at used
    omega
  · simp at used

private theorem contractionPromotedIdSlots_inside {s : ArithmeticState} (rows : s.nr 61 = 3*s.nr 55)
    (freshIn : ∀ j < s.nr 99, s.nm (s.nr 88+j) < s.nr 55)
    {a : ℕ} (present : a ∈ (List.range (s.nr 99)).flatMap (contractionPromotedIdSlots s)) :
    s.nr 58 ≤ a ∧ a < s.nr 58+s.nr 61 := by
  obtain ⟨i, hi, used⟩ := List.mem_flatMap.mp present
  have bound := freshIn i (List.mem_range.mp hi)
  simp only [contractionPromotedIdSlots, List.mem_singleton] at used
  omega

theorem matchingContractionClearedAddresses_inside {s : ArithmeticState}
    (rows : s.nr 61 = 3*s.nr 55) (freshIn : ∀ j < s.nr 99, s.nm (s.nr 88+j) < s.nr 55)
    {a : ℕ} (present : a ∈ matchingContractionClearedAddresses s) :
    s.nr 58 ≤ a ∧ a < s.nr 58+s.nr 61 := by
  rcases List.mem_append.mp present with mask | fresh
  · exact contractionMaskedIdSlots_inside rows mask
  · exact contractionPromotedIdSlots_inside rows freshIn fresh

/-- Initialize the merged representative and invalidate just the affected rows.
Both pair caches and the registry remain readable throughout the preparation. -/
theorem clearMatchingContractionIds_effect {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (rows : s.nr 61 = 3*s.nr 55)
    (markAfter : s.nr 58+s.nr 61 ≤ s.nr 89) (freshAfter : s.nr 58+s.nr 61 ≤ s.nr 88)
    (freshIn : ∀ j < s.nr 99, s.nm (s.nr 88+j) < s.nr 55) :
    ∃ t steps, steps ≤ 12*s.nr 55+8*s.nr 99+7 ∧ BlockRuns clearMatchingContractionIds steps s t ∧
      t.halted = false ∧ t.nr 14 = 0 ∧ t.nr 23 = 0 ∧ t.nr 26 = s.nr 12 ∧
      (∀ r, r ∉ [6, 7, 10, 14, 23, 26] → t.nr r = s.nr r) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ addr, t.nm addr = if addr ∈ matchingContractionClearedAddresses s then 0 else s.nm addr := by
  let seed := { s with
    pc := 3
    nr := Function.update (Function.update (Function.update s.nr 23 0) 14 0) 26 (s.nr 12) }
  have seeded : BlockRuns seedMatchingContractionCache 3 s seed := by
    refine BlockRuns.of_running_exit ?_ running rfl
    simp [seed, seedMatchingContractionCache, arithmeticStep, entry, running, Function.iterate_succ_apply']
  let a := {seed with pc := 0}
  have aFixed (r : ℕ) (safe : r ∉ [14, 23, 26] := by decide) : a.nr r = s.nr r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at safe
    obtain ⟨h14,h23,h26⟩ := safe
    simp [a, seed, h14, h23, h26]
  have aOne := (aFixed 9).trans one
  have aZero : a.nr 23 = 0 := by simp [a, seed]
  obtain ⟨b, outerSteps, outerBudget, outerRun, bLive, outerFixed, outerReal, outerRR, outerWritten⟩ :=
    clearContractedCandidateRows_loop (s := a) rfl running aOne aZero
      (by rw [aFixed 61, aFixed 55]; exact rows) (by rw [aFixed 58, aFixed 61, aFixed 89]; exact markAfter)
  let start := {b with pc := 0}
  have keepB (r : ℕ) (h6 : r ≠ 6 := by decide) (h7 : r ≠ 7 := by decide) (h10 : r ≠ 10 := by decide) :=
    outerFixed r h6 h7 h10
  have port (r : ℕ) (safe : r ∉ [6, 7, 10, 14, 23, 26] := by decide) : start.nr r = s.nr r :=
    (keepB r (by simp at safe; omega) (by simp at safe; omega) (by simp at safe; omega)).trans
      (aFixed r (by simp at safe ⊢; omega))
  have maskAppend : (List.range (a.nr 55)).flatMap (contractionMaskedIdSlots a) =
      (List.range (s.nr 55)).flatMap (contractionMaskedIdSlots s) := by
    rw [aFixed 55]
    apply congrArg (fun f => (List.range (s.nr 55)).flatMap f)
    funext i
    simp only [contractionMaskedIdSlots, aFixed 55, aFixed 58, aFixed 89, show a.nm = s.nm from rfl]
  have outerEffect (addr : ℕ) : start.nm addr =
      if addr ∈ (List.range (s.nr 55)).flatMap (contractionMaskedIdSlots s) then 0 else s.nm addr := by
    simpa only [maskAppend, show a.nm = s.nm from rfl] using outerWritten addr
  have absentFresh (i : ℕ) : start.nm (s.nr 88+i) = s.nm (s.nr 88+i) := by
    have outside : s.nr 88+i ∉ (List.range (s.nr 55)).flatMap (contractionMaskedIdSlots s) := fun found => by
      have h := contractionMaskedIdSlots_inside rows found
      omega
    rw [outerEffect, if_neg outside]
  obtain ⟨t, innerSteps, innerBudget, innerRun, live, innerFixed, innerReal, innerRR, innerWritten⟩ :=
    clearPromotedIncomingCandidate_loop (s := start) rfl bLive ((port 9).trans one) ((keepB 23).trans aZero)
      (by rw [port 61, port 55]; exact rows) (by rw [port 58, port 61, port 88]; exact freshAfter)
      (fun i hi => by rw [port 99] at hi; rw [port 88, absentFresh, port 55]; exact freshIn i hi)
  have promoted : (List.range (start.nr 99)).flatMap (contractionPromotedIdSlots start) =
      (List.range (s.nr 99)).flatMap (contractionPromotedIdSlots s) := by
    rw [port 99]
    apply congrArg (fun f => (List.range (s.nr 99)).flatMap f)
    funext i
    simp only [contractionPromotedIdSlots, port 58, port 55, port 88, absentFresh]
  rw [aFixed 55] at outerBudget
  rw [port 99] at innerBudget
  have prepare : BlockRuns clearMatchingContractionIds (3+(outerSteps+innerSteps)) s _ :=
    seeded.append (outerRun.append innerRun)
  refine ⟨_, _, by omega, prepare, live, ?_, ?_, ?_, ?_, innerReal.trans outerReal, innerRR.trans outerRR, ?_⟩
  · exact (innerFixed 14 (by decide) (by decide) (by decide)).trans ((keepB 14).trans (by simp [a, seed]))
  · exact (innerFixed 23 (by decide) (by decide) (by decide)).trans ((keepB 23).trans aZero)
  · exact (innerFixed 26 (by decide) (by decide) (by decide)).trans ((keepB 26).trans (by simp [a, seed]))
  · intro r safe
    exact (innerFixed r (by simp at safe; omega) (by simp at safe; omega) (by simp at safe; omega)).trans (port r safe)
  · intro addr
    change t.nm addr = _
    rw [innerWritten, promoted, outerEffect, matchingContractionClearedAddresses]
    by_cases wiped : addr ∈ (List.range (s.nr 99)).flatMap (contractionPromotedIdSlots s) <;> simp [List.mem_append,wiped]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionCacheSeed

/-! matching/MatchingContractionClearedGroups.lean -/
section RppSource_MatchingContractionClearedGroups
namespace VehicleRoutingSurvey.Routing

/-- Characterize the actual stores of both invalidation passes in the three
selector slabs using the typed cycle and promoted-original list. -/
theorem matchingContractionClearedGroups {k : ℕ} (s : ArithmeticState)
    (cycle : Finset (Fin k)) (fresh : List (Fin k)) (dimension : s.nr 55 = k)
    (count : s.nr 99 = fresh.length) (marked : ∀ v : Fin k, s.nm (s.nr 89+v.val) ≠ 0 ↔ v ∈ cycle)
    (encoded : ∀ j : Fin fresh.length, s.nm (s.nr 88+j.val) = (fresh.get j).val) (g : MatchingCandidateGroup k) :
    s.nr 58+g.slot ∈ matchingContractionClearedAddresses s ↔
      match g with | .outer v | .cut v => v ∈ cycle | .incoming v => v ∈ fresh := by
  have mask (row : ℕ) : s.nr 58+row ∈ (List.range (s.nr 55)).flatMap (contractionMaskedIdSlots s) ↔
      ∃ v ∈ cycle, row = v.val ∨ row = 2*k+v.val := by
    constructor
    · intro hit
      obtain ⟨i,hi,h⟩ := List.mem_flatMap.mp hit
      have inside : i < k := dimension ▸ List.mem_range.mp hi
      let v : Fin k := ⟨i,inside⟩
      by_cases off : s.nm (s.nr 89+i) = 0
      · simp [contractionMaskedIdSlots,off] at h
      · refine ⟨v,(marked v).mp off,?_⟩
        simpa [contractionMaskedIdSlots,off,dimension,v] using h
    · rintro ⟨v,on,(rfl | rfl)⟩ <;>
        exact List.mem_flatMap.mpr ⟨v.val,List.mem_range.mpr (dimension.symm ▸ v.isLt),
          by simp [contractionMaskedIdSlots,(marked v).mpr on,dimension]⟩
  have incoming (row : ℕ) : s.nr 58+row ∈ (List.range (s.nr 99)).flatMap (contractionPromotedIdSlots s) ↔
      ∃ u ∈ fresh, row = k+u.val := by
    constructor
    · intro hit
      obtain ⟨i,hi,h⟩ := List.mem_flatMap.mp hit
      let j : Fin fresh.length := ⟨i,count ▸ List.mem_range.mp hi⟩
      refine ⟨fresh.get j,List.get_mem _ _,?_⟩
      simpa only [contractionPromotedIdSlots,List.mem_singleton,dimension,
        show s.nm (s.nr 88+i) = (fresh.get j).val from encoded j, Nat.add_right_inj] using h
    · rintro ⟨u,hu,rfl⟩
      obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hu
      exact List.mem_flatMap.mpr ⟨j.val,List.mem_range.mpr (count.symm ▸ j.isLt),
        by simp [contractionPromotedIdSlots,dimension,encoded j]⟩
  rw [matchingContractionClearedAddresses,List.mem_append,mask,incoming]
  cases g with
  | outer v =>
    change (∃ w ∈ cycle, v.val = w.val ∨ v.val = 2*k+w.val) ∨ (∃ w ∈ fresh, v.val = k+w.val) ↔ _
    constructor
    · rintro (⟨w,hw,eq | eq⟩ | ⟨w,_,eq⟩)
      · exact (Fin.ext eq).symm ▸ hw
      · have hv := v.isLt; omega
      · have hv := v.isLt; omega
    · intro hv; exact Or.inl ⟨v,hv,Or.inl rfl⟩
  | incoming v =>
    change (∃ w ∈ cycle, k+v.val = w.val ∨ k+v.val = 2*k+w.val) ∨ (∃ w ∈ fresh, k+v.val = k+w.val) ↔ _
    constructor
    · rintro (⟨w,_,eq | eq⟩ | ⟨w,hw,eq⟩)
      · have h := w.isLt; omega
      · have h := v.isLt; omega
      · exact (Fin.ext (Nat.add_left_cancel eq)).symm ▸ hw
    · intro hv; exact Or.inr ⟨v,hv,rfl⟩
  | cut v =>
    change (∃ w ∈ cycle, 2*k+v.val = w.val ∨ 2*k+v.val = 2*k+w.val) ∨ (∃ w ∈ fresh, 2*k+v.val = k+w.val) ↔ _
    constructor
    · rintro (⟨w,_,eq | eq⟩ | ⟨w,_,eq⟩)
      · have h := w.isLt; omega
      · exact (Fin.ext (Nat.add_left_cancel eq)).symm ▸ ‹w ∈ cycle›
      · have h := w.isLt; omega
    · intro hv; exact Or.inl ⟨v,hv,Or.inr rfl⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionClearedGroups

/-! matching/MatchingContractionGroupMinimum.lean -/
section RppSource_MatchingContractionGroupMinimum
namespace VehicleRoutingSurvey.Routing



def matchingContractionGroupCleared {k : ℕ} (cycle : Finset (Fin k)) (fresh : List (Fin k)) :
    MatchingCandidateGroup k → Prop
  | .outer v | .cut v => v ∈ cycle
  | .incoming v => v ∈ fresh

/-- The physical clear, merged column offers and newly outer originals produce
the full minima for all three selector slabs of the contracted partition. -/
theorem contractionSearchGroupMinimum {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    (part : CompactMatchingPartition state) (forest : AlternatingForestState (Fin k)) (positive : 0 < k)
    (symmetric : ∀ u v, cost u v = cost v u)
    (nested : ∀ S ∈ state.cuts, ∀ u ∈ S, ∀ v ∈ S, part.blocks.block u = part.blocks.block v)
    (cycle : Finset (Fin k)) (base : Fin k) (baseIn : base ∈ cycle) (fixed : ∀ v ∈ cycle, part.representative v = v)
    (odd : Odd cycle.card) (covered : ∀ c ∈ cycle, c ≠ base → c ∈ state.covered) (baseOuter : ∃ p, forest.role base = .outer p)
    (s : ArithmeticState) (absorbed fresh : List (Fin k)) (history : List (ContractionColumnWinner k))
    (group : MatchingCandidateGroup k) (cached : Option (DualSlack (MatchingDualEvent k)))
    (old : LeastSlackEntry (contractionSearchEntries part forest positive group) cached) :
    let next := part.contract cycle base baseIn fixed odd covered
    let after := forest.contract cycle base
    let priorRole := fun v => alternatingRoleCode (forest.role v)
    let role := fun v => alternatingRoleCode (after.role v)
    let effective := effectiveVertexPotential state.cuts state.potential state.cutDual
    MatchingContractionPairGeometry part.representative next.representative priorRole role base absorbed fresh →
      (∀ v, role (next.representative v) = if v ∈ fresh then 1 else priorRole (part.representative v)) →
      (∀ v : Fin k, s.nm (s.nr 51+v.val) = role v) →
      (∀ v, MatchingContractionColumnEligible s base v → ∃ w, (v,w) ∈ history ∧
        LeastSlackEntry (absorbed.flatMap (fun r => normalizedOuterPairEntries part.representative cost effective (s.rr 15) r v)) w) →
      (∀ v w, (v,w) ∈ history → if MatchingContractionColumnEligible s base v then
        LeastSlackEntry (absorbed.flatMap (fun r => normalizedOuterPairEntries part.representative cost effective (s.rr 15) r v)) w else w = none) →
      let cleared := matchingContractionGroupCleared cycle fresh group
      LeastSlackEntry (contractionSearchEntries next after positive group)
        (insertSlackCandidates (fresh.flatMap (contractionFreshRowInputs next.representative role cost effective group.slot))
          (history.foldl (contractionColumnRowUpdate base (s.rr 15) group.slot)
            (@ite _ cleared (Classical.propDecidable cleared) none cached))) := by
  classical
  intro next after priorRole role effective shape changes roleAt chosen offered cleared
  have nextNest : ∀ S ∈ insert (part.contractCut cycle) state.cuts, ∀ u ∈ S, ∀ v ∈ S, next.blocks.block u = next.blocks.block v :=
    part.blocks.contract_cuts_nested (Finset.image_mono part.blocks.block (Finset.subset_univ cycle)) nested
  have eff : effectiveVertexPotential (insert (part.contractCut cycle) state.cuts) state.potential
      (extendBlossomCutDual state.cuts state.cutDual) = effective := by
    funext v
    exact effectiveVertexPotential_register_cut _ _ _ _ _
  cases group with
  | outer row =>
    have outside (c : Fin k) (outer : role c = 1) (away : c ≠ base) : c ∉ cycle := by
      intro hc
      simp [role,after,AlternatingForestState.contract,hc,away,alternatingRoleCode] at outer
    have fibers (c : Fin k) (hc : c ∉ cycle) (v : Fin k) : part.representative v = c ↔ next.representative v = c := by
      rw [part.contract_representative]
      by_cases merged : part.representative v ∈ cycle
      · have oldAway : part.representative v ≠ c := fun h => hc (h ▸ merged)
        have newAway : base ≠ c := fun h => hc (h ▸ baseIn)
        simp [blossomRepresentative,merged,oldAway,newAway]
      · simp [blossomRepresentative,merged]
    have haveMin := contractionOuterRow_least s part.representative next.representative priorRole role cost symmetric effective
      absorbed fresh base row shape (fun v => v ∉ cycle) outside fibers roleAt _ _ cached
      (matchingSearchOuterGroup_mem_iff part forest positive symmetric nested row)
      (fun d => by
        have w := matchingSearchOuterGroup_mem_iff next after positive symmetric nextNest row d
        change _ ↔ outerEdgeAt next.representative role cost
          (effectiveVertexPotential (insert (part.contractCut cycle) state.cuts) state.potential (extendBlossomCutDual state.cuts state.cutDual)) row d at w
        simpa only [eff] using w) old history chosen offered
    by_cases deleted : row ∈ cycle <;>
      simpa [cleared,matchingContractionGroupCleared,deleted,MatchingCandidateGroup.slot,contractionSearchEntries] using haveMin
  | incoming row =>
    have initial : (@ite _ cleared (Classical.propDecidable cleared) none cached) =
        (if row ∈ fresh then none else cached) := by
      by_cases h : row ∈ fresh <;> simp [cleared,matchingContractionGroupCleared,h]
    rw [initial]
    apply contractionIncomingRow_least part.representative next.representative priorRole role cost effective fresh base row
      (s.rr 15) history cached (contractionSearchEntries part forest positive (.incoming row)) _
      (matchingSearchIncomingGroup_mem_iff part forest positive symmetric nested row) _ old
    · intro u
      by_cases new : u ∈ fresh <;> simp [changes,new]
    · intro u absent
      simp only [changes,if_neg absent]
    · intro d
      have w := matchingSearchIncomingGroup_mem_iff next after positive symmetric nextNest row d
      change _ ↔ incomingEdgeAt next.representative role cost
        (effectiveVertexPotential (insert (part.contractCut cycle) state.cuts) state.potential (extendBlossomCutDual state.cuts state.cutDual)) row d at w
      simpa only [contractionSearchEntries,eff] using w
  | cut row =>
    have oldEntry : cached = matchingCutGroupEntry part forest row := matchingCutGroupEntry_of_least old
    have newEntry := contractionCutGroupEntry part forest cycle base baseIn fixed odd covered baseOuter row
    have initial : (@ite _ cleared (Classical.propDecidable cleared) none cached) =
        (if row ∈ cycle then none else cached) := by
      by_cases h : row ∈ cycle <;> simp [cleared,matchingContractionGroupCleared,h]
    rw [initial]
    change LeastSlackEntry _ (insertSlackCandidates (fresh.flatMap (contractionFreshRowInputs next.representative role cost effective (2*k+row.val)))
      (history.foldl (contractionColumnRowUpdate base (s.rr 15) (2*k+row.val)) (if row ∈ cycle then none else cached)))
    rw [contractionFreshRowInputs_cut,contractionColumnRowFold_above base _ (by omega),oldEntry,←newEntry]
    exact matchingCutGroupEntry_least next after positive row

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionGroupMinimum

/-! matching/MatchingContractionCacheRepair.lean -/
section RppSource_MatchingContractionCacheRepair
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096
set_option maxHeartbeats 900000

theorem repairMatchingContractionCache_split : repairMatchingContractionCache =
    appendBlock clearMatchingContractionIds (appendBlock repairMatchingContractionColumns scanFreshContractedOriginals) := by
  rfl

private theorem cacheFootprint_low {k : ℕ} {s t : ArithmeticState} (frame : MatchingCacheFootprint k s t) :
    CacheMemoryFrame s t :=
  ⟨fun a low => frame.natural a (Or.inl low), fun a low _ _ => frame.real a (Or.inl low)⟩

/-- Exact effects of the actual contraction cache repair: erase obsolete rows,
merge the surviving outer columns, and scan the newly outer originals. -/
theorem repairMatchingContractionCache_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} {rep : Fin k → Fin k} {role : Fin k → ℕ} {cost : Fin k → Fin k → ℝ} {effective : Fin k → ℝ}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (input : MatchingRefreshInput s rep role cost effective) (merged : Fin k) (baseAt : s.nr 12 = merged.val)
    (absorbed fresh : List (Fin k)) (absorbedCount : s.nr 87 = absorbed.length) (freshCount : s.nr 99 = fresh.length)
    (absorbedWords : ∀ j : Fin absorbed.length, s.nm (s.nr 86+j.val) = (absorbed.get j).val)
    (freshWords : ∀ j : Fin fresh.length, s.nm (s.nr 88+j.val) = (fresh.get j).val)
    (freshRep : ∀ u ∈ fresh, rep u = merged)
    (absorbedAfter : s.nr 65+2*(k*k) ≤ s.nr 86) (freshAfter : s.nr 65+2*(k*k) ≤ s.nr 88)
    (markAfter : s.nr 58+s.nr 61 ≤ s.nr 89)
    (survives : ∀ c, MatchingContractionColumnEligible s merged c → c ∉ absorbed)
    (full : Fin k → Fin k → List (DualSlack (MatchingDualEvent k)))
    (minima : ∀ row ∈ absorbed, ∀ v, MatchingContractionColumnEligible s merged v →
      LeastSlackEntry (full row v) (readMatchingPairBucket (k := k) s (k*row.val+v.val)))
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k*k, MatchingPairBucketValid k s i) :
    ∃ t steps, ∃ history : List (ContractionColumnWinner k),
      steps ≤ (112+22*absorbed.length)*k + (15+98*k)*fresh.length+11 ∧
      BlockRuns repairMatchingContractionCache steps s t ∧ t.halted = false ∧
      MatchingCacheFootprint k s t ∧ MatchingRefreshInput t rep role cost effective ∧ t.rr 15 = s.rr 15 ∧
      (∀ v : Fin k, MatchingContractionColumnEligible s merged v →
        ∃ w, (v,w) ∈ history ∧ LeastSlackEntry (absorbed.flatMap (fun row => full row v)) w) ∧
      (∀ v w, (v,w) ∈ history → if MatchingContractionColumnEligible s merged v then
        LeastSlackEntry (absorbed.flatMap (fun row => full row v)) w else w = none) ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i =
        insertSlackCandidates (fresh.flatMap (contractionFreshRowInputs rep role cost effective i))
          (history.foldl (contractionColumnRowUpdate merged (s.rr 15) i)
            (if s.nr 58+i ∈ matchingContractionClearedAddresses s then none else readMatchingCandidate cutAt s i))) ∧
      (∀ i < k*k, MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i =
        insertSlackCandidates (fresh.flatMap (contractionFreshPairInputs rep role cost effective (s.rr 15) i))
          (history.foldl (contractionColumnPairUpdate merged i) (readMatchingPairBucket (k := k) s i))) := by
  have idsEnd : s.nr 58+s.nr 61 ≤ s.nr 65 := by
    have ids := input.layout.idsBefore
    have records := input.layout.recordsBefore
    omega
  have encodedFresh (j : ℕ) (inside : j < s.nr 99) : s.nm (s.nr 88+j) < s.nr 55 := by
    let i : Fin fresh.length := ⟨j, freshCount ▸ inside⟩
    rw [show j = i.val from rfl, freshWords i, input.layout.dimension]
    exact (fresh.get i).isLt
  have idRows : s.nr 61 = 3*s.nr 55 := by rw [input.layout.dimension]; exact input.layout.rows
  obtain ⟨front, frontSteps, frontBudget, frontRun, frontLive, zero14, zero23, frontBase, frontFixed, frontReal, frontClock, natural⟩ :=
    clearMatchingContractionIds_effect entry running one idRows markAfter (by omega) encodedFresh
  let a := {front with pc := 0}
  have aKeep (r : ℕ) (safe : r ∉ [6, 7, 10, 14, 23, 26] := by decide) : a.nr r = s.nr r := frontFixed r safe
  have frontEffect : ∀ addr, a.nm addr = if addr ∈ matchingContractionClearedAddresses s then 0 else s.nm addr := natural
  obtain ⟨aFrame, aRows, aBuckets⟩ := candidateIdClear_cache cutAt input.layout (matchingContractionClearedAddresses s)
    (fun _ found => matchingContractionClearedAddresses_inside idRows encodedFresh found) frontEffect frontReal
    (fun r high => aKeep r (by simp; omega)) rows buckets
  have aInput : MatchingRefreshInput a rep role cost effective :=
    input.keeps (cacheFootprint_low aFrame) (fun r hr => aKeep r (by simp [matchingRefreshTableRegisters] at hr ⊢; omega))
  have aOffsets : MatchingCacheOffsets k a :=
    ⟨fun i hi => by have endAt := aInput.offsetsBefore; omega, fun i hi => aInput.offsets ⟨i, hi⟩⟩
  have aGuard (v : Fin k) : MatchingContractionColumnEligible a merged v ↔ MatchingContractionColumnEligible s merged v := by
    have same : a.nm (a.nr 51+v.val) = s.nm (s.nr 51+v.val) := by
      rw [aKeep 51, aFrame.natural _ (.inl (by have h := input.rolesBefore; have hi := v.isLt; omega))]
    simp only [MatchingContractionColumnEligible, same]
  have aAbsorbed (j : Fin absorbed.length) : a.nm (a.nr 86+j.val) = (absorbed.get j).val := by
    rw [aKeep 86, aFrame.natural _ (.inr (by omega))]
    exact absorbedWords j
  obtain ⟨column, colSteps, history, colBudget, colRun, colLive, colFrame, colTime, colFixed, colOne, colZero,
    winners, offered, colRows, colBuckets⟩ := repairMatchingContractionColumns_rows cutAt merged absorbed (s := a)
    rfl frontLive ((aKeep 9).trans one) zero23 aInput.layout aOffsets (frontBase.trans baseAt)
    ((aKeep 87).trans absorbedCount) aAbsorbed aInput.rolesBefore (by rwa [aKeep 65, aKeep 86])
    (fun c h => survives c ((aGuard c).mp h)) full
    (fun row h v outer => by
      have hi := Nat.mul_le_mul_left k (Nat.succ_le_of_lt row.isLt)
      rw [Nat.mul_succ] at hi
      have tail := v.isLt
      rw [(aBuckets _ (by omega)).2]
      exact minima row h v ((aGuard v).mp outer))
    (fun i hi => (aRows i (by rwa [aKeep 61] at hi)).1) (fun i hi => (aBuckets i hi).1)
  let b := {column with pc := 0}
  have stable (r : ℕ) (safe : 25 ≤ r := by decide) : b.nr r = a.nr r := colFixed r (Or.inr safe)
  have bMetric : b.nr 20 = a.nr 20 := by
    change column.nr 20 = _
    rw [← colRun.run]
    exact arithmeticRun_keeps_from_destination_list [0, 1, 2, 6, 7, 10, 11, 14, 15, 16, 17, 18, 23, 24]
      (by decide) (by decide) a colSteps
  have bInput : MatchingRefreshInput b rep role cost effective := aInput.keeps ⟨(cacheFootprint_low colFrame).natural,
    (cacheFootprint_low colFrame).real⟩ (fun r listed => by
      by_cases metric : r = 20
      · exact metric.symm ▸ bMetric
      · exact colFixed r (by simp [matchingRefreshTableRegisters] at listed; omega))
  have bZero : b.nr 14 = 0 :=
    blockRuns_preservesNaturalZero (code := repairMatchingContractionColumns) (r := 14) (s := a) (t := column)
      (by decide) colRun zero14
  have bFrame : MatchingCacheFootprint k s b :=
    ⟨(aFrame.chain colFrame (fun r h => aKeep r (by simp at h ⊢; omega))).natural,
      (aFrame.chain colFrame (fun r h => aKeep r (by simp at h ⊢; omega))).real⟩
  have bFresh (j : Fin fresh.length) : b.nm (b.nr 88+j.val) = (fresh.get j).val := by
    rw [stable 88, aKeep 88, bFrame.natural _ (.inr (by omega))]
    exact freshWords j
  have bTime : b.rr 15 = s.rr 15 := colTime.trans (congrFun frontClock 15)
  obtain ⟨t, finalSteps, finalBudget, finalRun, ready, finalTime, finalInput, finalFrame, finalRows, finalBuckets⟩ :=
    scanFreshContractedOriginals_rows cutAt (s := b) rfl colLive colOne bZero bInput fresh
      ((stable 99).trans ((aKeep 99).trans freshCount)) bFresh
      (fun u mem => by rw [stable 26, frontBase, baseAt, freshRep u mem]) (by rwa [stable 65, aKeep 65, stable 88, aKeep 88])
      (fun i hi => (colRows i (by rwa [stable 61] at hi)).1) (fun i hi => (colBuckets i hi).1)
  have allRun := frontRun.append (colRun.append finalRun)
  rw [← repairMatchingContractionCache_split] at allRun
  have lastFrame := bFrame.chain finalFrame (fun r listed =>
    (stable r (by simp at listed; omega)).trans (aKeep r (by simp at listed ⊢; omega)))
  rw [input.layout.dimension, freshCount] at frontBudget
  refine ⟨_, _, history, ?_, allRun, ready, ⟨lastFrame.natural, lastFrame.real⟩, ?_, finalTime.trans bTime, ?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ _ := Nat.add_le_add frontBudget (Nat.add_le_add colBudget finalBudget)
      _ = _ := by ring
  · exact finalInput.keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
  · intro v outer
    exact winners v ((aGuard v).mpr outer)
  · intro v w mem
    simpa only [aGuard v] using offered v w mem
  · intro i hi
    have aInside : i < a.nr 61 := by rwa [aKeep 61]
    have bInside : i < b.nr 61 := by rwa [stable 61]
    change MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i = _
    refine ⟨(finalRows i bInside).1, ?_⟩
    change readMatchingCandidate cutAt t i = _
    have bRead : readMatchingCandidate cutAt b i = readMatchingCandidate cutAt column i := rfl
    rw [(finalRows i bInside).2, bRead, (colRows i aInside).2, (aRows i hi).2, congrFun frontClock 15]
  · intro i hi
    change MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i = _
    refine ⟨(finalBuckets i hi).1, ?_⟩
    have bRead : readMatchingPairBucket (k := k) b i = readMatchingPairBucket (k := k) column i := rfl
    rw [(finalBuckets i hi).2, bTime, bRead, (colBuckets i hi).2, (aBuckets i hi).2]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionCacheRepair

/-! matching/MatchingContractionPairRAM.lean -/
section RppSource_MatchingContractionPairRAM
namespace VehicleRoutingSurvey.Routing

/-- Execute the entire repair on physical cache, dictionary and representative
tables. The output retains the normalized minimum and inactivity invariant. -/
theorem repairMatchingContractionCache_outerBuckets {k : ℕ} (cuts : Fin k → Finset (Fin k))
    {s : ArithmeticState} (prior next : Fin k → Fin k) (oldRole newRole : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (symmetric : ∀ u v, cost u v = cost v u) (effective : Fin k → ℝ)
    (merged : Fin k) (absorbed fresh : List (Fin k))
    (shape : MatchingContractionPairGeometry prior next oldRole newRole merged absorbed fresh)
    (entry : s.pc = 0) (live : s.halted = false) (unit : s.nr 9 = 1)
    (input : MatchingRefreshInput s next newRole cost effective) (baseAt : s.nr 12 = merged.val)
    (absorbedCount : s.nr 87 = absorbed.length) (freshCount : s.nr 99 = fresh.length)
    (absorbedWords : ∀ j : Fin absorbed.length, s.nm (s.nr 86+j.val) = (absorbed.get j).val)
    (freshWords : ∀ j : Fin fresh.length, s.nm (s.nr 88+j.val) = (fresh.get j).val)
    (absorbedAfter : s.nr 65+2*(k*k) ≤ s.nr 86) (freshAfter : s.nr 65+2*(k*k) ≤ s.nr 88)
    (markAfter : s.nr 58+s.nr 61 ≤ s.nr 89)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cuts s i)
    (before : MatchingSearchOuterBuckets s prior oldRole cost effective) :
    ∃ t ticks, ticks ≤ (112+22*absorbed.length)*k + (15+98*k)*fresh.length+11 ∧
      BlockRuns repairMatchingContractionCache ticks s t ∧ t.halted = false ∧
      MatchingCacheFootprint k s t ∧ MatchingRefreshInput t next newRole cost effective ∧ t.rr 15 = s.rr 15 ∧
      MatchingSearchOuterBuckets t next newRole cost effective ∧
      ∃ history : List (ContractionColumnWinner k),
        (∀ v : Fin k, MatchingContractionColumnEligible s merged v →
          ∃ w, (v,w) ∈ history ∧ LeastSlackEntry (absorbed.flatMap
            (fun r => normalizedOuterPairEntries prior cost effective (s.rr 15) r v)) w) ∧
        (∀ v w, (v,w) ∈ history → if MatchingContractionColumnEligible s merged v then
          LeastSlackEntry (absorbed.flatMap (fun r => normalizedOuterPairEntries prior cost effective (s.rr 15) r v)) w else w = none) ∧
        ∀ i < s.nr 61, MatchingCandidateRowValid cuts t i ∧ readMatchingCandidate cuts t i =
          insertSlackCandidates (fresh.flatMap (contractionFreshRowInputs next newRole cost effective i))
            (history.foldl (contractionColumnRowUpdate merged (s.rr 15) i)
              (if s.nr 58+i ∈ matchingContractionClearedAddresses s then none else readMatchingCandidate cuts s i)) := by
  have active (c : Fin k) (h : MatchingContractionColumnEligible s merged c) : newRole c = 1 :=
    (input.roles c).symm.trans h.1
  have survives (c : Fin k) (h : MatchingContractionColumnEligible s merged c) : c ∉ absorbed :=
    shape.survivorOutside c h.2.symm (active c h)
  obtain ⟨t,ticks,history,budget,run,finished,frame,nextInput,clock,chosen,offered,finalRows,finalPairs⟩ :=
    repairMatchingContractionCache_rows cuts entry live unit input merged baseAt absorbed fresh absorbedCount freshCount
      absorbedWords freshWords (fun u hu => (shape.mergedFiber u).mpr (.inr hu)) absorbedAfter freshAfter markAfter
      survives (normalizedOuterPairEntries prior cost effective (s.rr 15))
      (fun r hr c hc => before.least r c (fun equal => survives c hc (equal ▸ hr))
        (shape.absorbedOuter r hr) (shape.survivorOuter c hc.2.symm (active c hc))) rows before.valid
  exact ⟨t,ticks,budget,run,finished,frame,nextInput,clock,
    matchingContractionPairBuckets prior next oldRole newRole cost symmetric effective merged absorbed fresh history shape
      before input.roles clock chosen offered finalPairs, history, chosen, offered, finalRows⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionPairRAM

/-! matching/MatchingContractionSearchRows.lean -/
section RppSource_MatchingContractionSearchRows
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

/-- Execute the actual contraction suffix and recover all selector rows, pair
cache entries, selector addresses and the empty winner at its unique exit. -/
theorem matchingContractionSuffix_searchRows {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    (part : CompactMatchingPartition state) (forest : AlternatingForestState (Fin k)) (positive : 0 < k)
    (symmetric : ∀ u v, cost u v = cost v u)
    (nested : ∀ S ∈ state.cuts, ∀ u ∈ S, ∀ v ∈ S, part.blocks.block u = part.blocks.block v)
    (cycle : Finset (Fin k)) (base : Fin k) (baseIn : base ∈ cycle) (fixed : ∀ v ∈ cycle, part.representative v = v)
    (odd : Odd cycle.card) (covered : ∀ c ∈ cycle, c ≠ base → c ∈ state.covered) (baseOuter : ∃ p, forest.role base = .outer p)
    (s : ArithmeticState) (absorbed fresh : List (Fin k)) (cutAt : Fin k → Finset (Fin k))
    (entry : s.pc = 0) (live : s.halted = false) (unit : s.nr 9 = 1) (baseAt : s.nr 12 = base.val)
    (absorbedCount : s.nr 87 = absorbed.length) (freshCount : s.nr 99 = fresh.length)
    (absorbedWords : ∀ j : Fin absorbed.length, s.nm (s.nr 86+j.val) = (absorbed.get j).val)
    (freshWords : ∀ j : Fin fresh.length, s.nm (s.nr 88+j.val) = (fresh.get j).val)
    (marked : ∀ v : Fin k, s.nm (s.nr 89+v.val) ≠ 0 ↔ v ∈ cycle)
    (absorbedAfter : s.nr 65+2*(k*k) ≤ s.nr 86) (freshAfter : s.nr 65+2*(k*k) ≤ s.nr 88)
    (markAfter : s.nr 58+s.nr 61 ≤ s.nr 89)
    (valid : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (least : ∀ g, LeastSlackEntry (contractionSearchEntries part forest positive g) (readMatchingCandidate cutAt s g.slot)) :
    let next := part.contract cycle base baseIn fixed odd covered
    let after := forest.contract cycle base
    let oldRole := fun r => alternatingRoleCode (forest.role r)
    let role := fun r => alternatingRoleCode (after.role r)
    let effective := effectiveVertexPotential state.cuts state.potential state.cutDual
    MatchingContractionPairGeometry part.representative next.representative oldRole role base absorbed fresh →
    (∀ v, role (next.representative v) = if v ∈ fresh then 1 else oldRole (part.representative v)) →
    MatchingRefreshInput s next.representative role cost effective →
    MatchingSearchOuterBuckets s part.representative oldRole cost effective →
      ∃ t ticks, ticks ≤ (112+22*absorbed.length)*k + (15+98*k)*fresh.length+16 ∧
        BlockRuns (appendBlock repairMatchingContractionCache resetMatchingSelector) ticks s t ∧ t.halted = false ∧
        t.nr 1 = 0 ∧ MatchingCacheFootprint k s t ∧ t.rr 15 = s.rr 15 ∧
        (∀ r ∉ [0,1,2,3,4,5,6,7,8,10,11,14,15,16,17,18,19,23,24,25,26], t.nr r = s.nr r) ∧
        MatchingSearchRows next after positive cutAt t ∧ MatchingRefreshInput t next.representative role cost effective ∧
        MatchingSearchOuterBuckets t next.representative role cost effective := by
  classical
  intro next after oldRole role effective shape changes input buckets
  obtain ⟨m,ticks,budget,run,ready,frame,newRead,clock,newPairs,history,chosen,offered,rows⟩ :=
    repairMatchingContractionCache_outerBuckets cutAt part.representative next.representative oldRole role cost symmetric effective
      base absorbed fresh shape entry live unit input baseAt absorbedCount freshCount absorbedWords freshWords absorbedAfter freshAfter markAfter valid buckets
  obtain ⟨u,_,_,other,_,_,cacheKeeps,_,zero⟩ := repairMatchingContractionCache_spec s entry live unit
    (by have h := input.layout.idsBefore; omega) (by have h := input.layout.idsBefore; have z := input.layout.recordsBefore; omega)
  have same := (other.same_exit run).2
  subst u
  let b := {m with pc := 0}
  obtain ⟨t,reset,done,natural,real,empty,ids,slacks,rates,count⟩ := resetMatchingSelector_spec b rfl ready zero
  have port (r : ℕ) (away : r ∉ [0,1,3,4,5,8] := by decide) : t.nr r = m.nr r := by
    rw [← reset.run]
    exact arithmeticRun_keeps_from_destination_list [0,1,3,4,5,8] (by decide) away b 5
  have regs (r : ℕ) (hr : r ∈ matchingRefreshTableRegisters) : t.nr r = m.nr r :=
    port r (by simp [matchingRefreshTableRegisters] at hr; simp; omega)
  have endClock : t.rr 15 = m.rr 15 := by
    rw [← reset.run]
    exact arithmeticRun_keeps_real_from_destination_list [0] (by decide) (by decide) b 5
  obtain ⟨endRows,endPairs⟩ := matchingCacheReads_unchanged cutAt (m := m) (t := t) natural real regs
  have lastFrame : MatchingCacheFootprint k s t := ⟨fun a h => (congrFun natural a).trans (frame.natural a h),
    fun a h => (congrFun real a).trans (frame.real a h)⟩
  have endInput := newRead.keeps (t := t) ⟨fun a _ => congrFun natural a,fun a _ _ _ => congrFun real a⟩ regs
  let out := relocateState repairMatchingContractionCache.length t
  have outInput := endInput.keeps (t := out) ⟨fun _ _ => rfl,fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
  refine ⟨out,ticks+5,by omega,run.append reset,done,empty,⟨lastFrame.natural,lastFrame.real⟩,endClock.trans clock,
    (fun r kept => (port r (by simp at kept ⊢; omega)).trans (cacheKeeps r (by simp at kept ⊢; omega))),
    ⟨outInput.layout,count.trans (port 61).symm,ids.trans (port 58).symm,slacks.trans (port 59).symm,
      rates.trans (port 60).symm,?_,?_⟩,outInput,⟨?_,?_,?_⟩⟩
  · intro i hi
    change MatchingCandidateRowValid cutAt t i
    rw [(endRows i).1]
    exact (rows i ((endInput.layout.rows.trans input.layout.rows.symm) ▸ hi)).1
  · intro g
    change LeastSlackEntry (contractionSearchEntries next after positive g) (readMatchingCandidate cutAt t g.slot)
    rw [(endRows g.slot).2,(rows _ (input.layout.rows.symm ▸ g.slot_lt)).2]
    have erased := matchingContractionClearedGroups s cycle fresh input.layout.dimension freshCount marked freshWords g
    change _ ↔ matchingContractionGroupCleared cycle fresh g at erased
    have result := contractionSearchGroupMinimum part forest positive symmetric nested cycle base baseIn fixed odd covered baseOuter
      s absorbed fresh history g _ (least g) shape changes input.roles chosen offered
    by_cases h : s.nr 58+g.slot ∈ matchingContractionClearedAddresses s
    · simpa only [if_pos h,if_pos (erased.mp h)] using result
    · simpa only [if_neg h,if_neg (erased.not.mp h)] using result
  · intro i hi
    change MatchingPairBucketValid k t i
    rw [(endPairs i).1]
    exact newPairs.valid _ hi
  · intro x y diff a c
    change LeastSlackEntry (normalizedOuterPairEntries next.representative cost effective (t.rr 15) x y) (readMatchingPairBucket t _)
    rw [endClock,(endPairs _).2]
    exact newPairs.least x y diff a c
  · intro x y off
    change readMatchingPairBucket (k := k) t _ = none
    rw [(endPairs _).2]
    exact newPairs.inactive _ _ off

end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractionSearchRows

open VehicleRoutingSurvey.Routing SupplyChainTheory in
theorem solution : (fun {P : Prop} (_ : P) => P) (@VehicleRoutingSurvey.Routing.matchingContractionSuffix_searchRows) :=
  @VehicleRoutingSurvey.Routing.matchingContractionSuffix_searchRows
