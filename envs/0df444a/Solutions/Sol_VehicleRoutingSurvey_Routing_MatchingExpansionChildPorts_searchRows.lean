-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.MatchingExpansionChildPorts.searchRows
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T16:00:58.754497+00:00
-- url     : https://prove2.me/submissions/c578452d-b64c-4e6a-b9cd-99a0874431ba

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



theorem effectiveVertexPotential_erase_zero {k : ℕ} (cuts : Finset (Finset (Fin k)))
    {B : Finset (Fin k)} (present : B ∈ cuts) (potential : Fin k → ℝ)
    (cutDual : Finset (Fin k) → ℝ) (zero : cutDual B = 0) (v : Fin k) :
    effectiveVertexPotential (cuts.erase B) potential cutDual v = effectiveVertexPotential cuts potential cutDual v := by
  simp only [effectiveVertexPotential, Finset.sum_filter]
  congr 1
  simpa [zero] using Finset.sum_erase_add cuts (fun S => if v ∈ S then cutDual S else 0) present










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





end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionPartition

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

theorem expansionCutNat_keeps_prefix {s : ArithmeticState} (dict : s.nr 58 ≤ s.nr 54)
    {a : ℕ} (below : a < s.nr 58) : expansionCutNat s a = s.nm a := by
  unfold expansionCutNat
  split
  · rfl
  · split
    · exact Function.update_of_ne (by omega) _ _
    · exact installedMatchingInnerCutNat_preserves_prefix (expansionCutReadyFull s)
        (by simpa [expansionCutReadyFull] using dict) a (by simpa [expansionCutReadyFull] using below)

theorem expansionCutReal_keeps_prefix {s : ArithmeticState} (rates : s.nr 59 ≤ s.nr 60)
    {a : ℕ} (below : a < s.nr 59) : expansionCutReal s a = s.rm a := by
  unfold expansionCutReal
  split
  · rfl
  · unfold installedMatchingInnerCutReal
    split
    · rfl
    · simp (disch := omega) [installedMatchingCandidateReal, growthInnerCutData, readyGrowthInnerNode,
        innerCutCandidateSlot, expansionCutReadyFull, Function.update_of_ne]

private structure ExpansionCutScan (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 7 = i
  fixed : ∀ r, r ∉ [0, 6, 7, 10, 15, 16, 18, 19, 28] → s.nr r = initial.nr r
  natural : ∀ a < initial.nr 58, s.nm a = initial.nm a
  real : ∀ a < initial.nr 59, s.rm a = initial.rm a

theorem restoreExpansionCuts_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (dict : s.nr 58 ≤ s.nr 54) (rates : s.nr 59 ≤ s.nr 60) :
    ∃ t steps, BlockRuns restoreExpansionCuts steps s t ∧ t.halted = false ∧ steps ≤ 35 * s.nr 55 + 2 ∧
      (∀ a < s.nr 58, t.nm a = s.nm a) ∧ (∀ a < s.nr 59, t.rm a = s.rm a) ∧
      ∀ r, r ∉ [0, 6, 7, 10, 15, 16, 18, 19, 28] → t.nr r = s.nr r := by
  let inv := ExpansionCutScan s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    intro r away
    exact Function.update_of_ne (by simp at away; omega) _ _
  have control (i : ℕ) (m : ArithmeticState) (h : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 55 = s.nr 55 :=
    ⟨h.entry, h.running, h.index, h.fixed 55 (by decide)⟩
  have next (i : ℕ) (_ : i < s.nr 55) (m : ArithmeticState) (h : inv i m) :
      ∃ t steps, steps ≤ 32 ∧ BlockRuns restoreExpansionCutCell steps m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    obtain ⟨t, steps, runs, live, budget, nat, real, fixed⟩ := restoreExpansionCutCell_spec h.entry h.running
      ((h.fixed 9 (by decide)).trans one) ((h.fixed 14 (by decide)).trans zero)
    refine ⟨t, steps, budget, runs, live, rfl, live, ?_, ?_, ?_, ?_⟩
    · simp [fixed 7 (by decide), fixed 9 (by decide), h.index, h.fixed 9 (by decide), one]
    · intro r away
      change Function.update t.nr 7 (t.nr 7 + t.nr 9) r = s.nr r
      rw [Function.update_of_ne (by simp at away; omega : r ≠ 7)]
      exact (fixed r (by simp at away ⊢; omega)).trans (h.fixed r away)
    · intro a below
      have dictAt : m.nr 58 ≤ m.nr 54 := by rwa [h.fixed 58 (by decide), h.fixed 54 (by decide)]
      exact ((congrFun nat a).trans (expansionCutNat_keeps_prefix dictAt
        (by rwa [h.fixed 58 (by decide)]))).trans (h.natural a below)
    · intro a below
      have ratesAt : m.nr 59 ≤ m.nr 60 := by rwa [h.fixed 59 (by decide), h.fixed 60 (by decide)]
      exact ((congrFun real a).trans (expansionCutReal_keeps_prefix ratesAt
        (by rwa [h.fixed 59 (by decide)]))).trans (h.real a below)
  obtain ⟨_, steps, result, budget, runs⟩ := countedLoopFromZero_bounded 9 7 55 (s.nr 55) 32
    restoreExpansionCutCell inv entry running initial control next
  exact ⟨_, steps, runs, result.running, by omega, result.natural, result.real, result.fixed⟩

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionCutRAM

/-! matching/ExpansionFreshRAM.lean -/
section RppSource_ExpansionFreshRAM
namespace VehicleRoutingSurvey.Routing





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

/-! matching/ExpansionNeighborRAM.lean -/
section RppSource_ExpansionNeighborRAM
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

theorem refreshExpansionOuterCell_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ t steps, BlockRuns refreshExpansionOuterCell steps s t ∧ t.halted = false ∧
      steps ≤ 98 * s.nr 55 + 6 ∧ CacheMemoryFrame s t ∧
      ∀ r, r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 25, 26] → t.nr r = s.nr r := by
  let addr := s.nr 88 + s.nr 24
  let orig := s.nm addr
  let repAddr := s.nr 57 + orig
  let loaded := Function.update (Function.update (Function.update s.nr 6 addr) 15 orig) 6 repAddr
  let a := { s with pc := 0, nr := Function.update loaded 26 (s.nm repAddr) }
  have loads : BlockRuns readExpansionOuterOriginal 4 s {a with pc := 4} := by
    apply BlockRuns.of_running_exit
    · simp [a, loaded, addr, orig, repAddr, readExpansionOuterOriginal, arithmeticStep, entry, running,
        Function.iterate_succ_apply']
    · exact running
    · rfl
  obtain ⟨t, steps, cost, scans, live, nat, real⟩ := refreshSelectedOuterVertex_spec a rfl running
    (by simpa [a, loaded] using one) (by simpa [a, loaded] using dict) (by simpa [a, loaded] using bucket)
  have size : a.nr 55 = s.nr 55 := by simp [a, loaded]
  rw [size, Nat.mul_comm] at cost
  have total : BlockRuns refreshExpansionOuterCell (4 + steps) s _ := loads.append scans
  refine ⟨_, _, total, live, by omega, ?_, ?_⟩
  · constructor
    · intro address safe
      exact nat address (by simpa [a, loaded] using safe)
    · intro address safe rates pairs
      exact real address (by simpa [a, loaded] using safe) (by simpa [a, loaded] using rates) (by simpa [a, loaded] using pairs)
  · intro r safe
    rw [← total.run]
    exact arithmeticRun_keeps_from_destination_list _ (by decide) safe s _

private structure ExpansionOuterScan (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 24 = i
  fixed : ∀ r, r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 26] → s.nr r = initial.nr r
  preserved : CacheMemoryFrame initial s

/-- Rescan every neighbor of each newly outer original. Its input list length
is the sole multiplier on the linear neighbor-scan cost. -/
theorem refreshExpansionOuterOriginals_spec {s : ArithmeticState} (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ t steps, BlockRuns refreshExpansionOuterOriginals steps s t ∧ t.halted = false ∧
      steps ≤ (98 * s.nr 55 + 9) * s.nr 99 + 2 ∧ CacheMemoryFrame s t ∧
      ∀ r, r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 26] → t.nr r = s.nr r := by
  let inv := ExpansionOuterScan s
  have start : inv 0 {s with pc := 0, nr := Function.update s.nr 24 0} := by
    refine ⟨rfl, running, by simp, ?_, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    intro r safe
    exact Function.update_of_ne (by simp at safe; omega) _ _
  have control (i : ℕ) (m : ArithmeticState) (h : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 24 = i ∧ m.nr 99 = s.nr 99 :=
    ⟨h.entry, h.running, h.index, h.fixed 99 (by decide)⟩
  have next (i : ℕ) (_ : i < s.nr 99) (m : ArithmeticState) (h : inv i m) :
      ∃ t steps, steps ≤ 98 * s.nr 55 + 6 ∧ BlockRuns refreshExpansionOuterCell steps m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)} := by
    have same (r : ℕ) (safe : r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 26] := by decide) :
        m.nr r = s.nr r := h.fixed r safe
    obtain ⟨t, steps, runs, live, cost, frame, fixed⟩ := refreshExpansionOuterCell_spec h.entry h.running
      ((same 9).trans one) (by rwa [same 58, same 54]) (by rwa [same 58, same 65])
    rw [same 55] at cost
    refine ⟨t, steps, cost, runs, live, rfl, live, ?_, ?_, ?_⟩
    · simp [fixed 24 (by decide), fixed 9 (by decide), h.index, same 9, one]
    · intro r safe
      change Function.update t.nr 24 (t.nr 24 + t.nr 9) r = s.nr r
      rw [Function.update_of_ne (by simp at safe; omega : r ≠ 24)]
      exact (fixed r (by simp at safe ⊢; omega)).trans (same r safe)
    · constructor
      · intro address below
        exact (frame.natural address (by rwa [same 58])).trans (h.preserved.natural address below)
      · intro address below rates pairs
        exact (frame.real address (by rwa [same 59]) (by rwa [same 59, same 60]) (by rwa [same 59, same 66])).trans
          (h.preserved.real address below rates pairs)
  obtain ⟨_, steps, done, cost, runs⟩ := countedLoopFromZero_bounded 9 24 99 (s.nr 99) (98 * s.nr 55 + 6)
    refreshExpansionOuterCell inv entry running start control next
  have total : 1 + (s.nr 99 * (98 * s.nr 55 + 6 + 3) + 1) = (98 * s.nr 55 + 9) * s.nr 99 + 2 := by
    rw [show 98 * s.nr 55 + 6 + 3 = 98 * s.nr 55 + 9 by omega, Nat.mul_comm (98 * s.nr 55 + 9)]
    omega
  exact ⟨_, steps, runs, done.running, cost.trans_eq total, ⟨done.preserved.natural, done.preserved.real⟩, done.fixed⟩

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionNeighborRAM

/-! matching/ExpansionCacheRAM.lean -/
section RppSource_ExpansionCacheRAM
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096





/-- Cache repair first counts exactly the newly outer originals, updates the
incoming and cut ranges, then pays one full neighbor scan per collected original. -/
theorem restoreExpansionCacheBlock_spec {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (layout : ExpansionCacheFrame s) :
    ∃ t steps, BlockRuns restoreExpansionCacheBlock steps s t ∧ t.halted = false ∧
      steps ≤ 63 * s.nr 55 + (98 * s.nr 55 + 9) * (freshExpansionOriginals s (s.nr 55)).length + 14 ∧
      ExpansionCacheRestored s t := by
  obtain ⟨collected, collectSteps, collect, collectLive, collectCost, count, _, collectNat, collectReal, cFixed⟩ :=
    collectExpansionOuterOriginals_spec entry running layout.one
      (layout.rolesBelowIncoming.trans layout.cacheBelowWorkList) layout.workListBelowMembers
  let a := {collected with pc := 0}
  have ca (r : ℕ) (safe : r ∉ [0, 6, 7, 10, 19, 99] := by decide) : a.nr r = s.nr r := cFixed r safe
  have caNat (addr : ℕ) (before : addr < s.nr 58) : a.nm addr = s.nm addr :=
    collectNat addr (.inl (before.trans_le layout.cacheBelowWorkList))
  obtain ⟨rerated, rateSteps, rerate, rateLive, rateCost, rateNat, rateReal, aFixed⟩ :=
    restoreExpansionIncomingRates_spec (s := a) rfl collectLive ((ca 9).trans layout.one) ((ca 14).trans layout.zero)
      (by rw [ca 51, ca 55, ca 58]; exact layout.rolesBelowIncoming)
      (by rw [ca 58, ca 55, ca 79]; exact layout.incomingBelowMembers)
  let b := {rerated with pc := 0}
  have cb (r : ℕ) (safe : r ∉ [0, 6, 7, 10, 11, 19, 99] := by decide) : b.nr r = s.nr r :=
    (aFixed r (by simp at safe ⊢; omega)).trans (ca r (by simp at safe ⊢; omega))
  have cbCount : b.nr 99 = (freshExpansionOriginals s (s.nr 55)).length := (aFixed 99 (by decide)).trans count
  have cbNat (addr : ℕ) (before : addr < s.nr 58) : b.nm addr = s.nm addr := by
    change rerated.nm addr = _
    rw [rateNat, expansionIncomingNat, ca 55, ca 58, if_neg]
    · exact caNat addr before
    · rintro ⟨i, hi, atRow, _⟩
      omega
  have cbReal (addr : ℕ) (before : addr < s.nr 59) : b.rm addr = s.rm addr := by
    change rerated.rm addr = _
    rw [rateReal, expansionIncomingReal, ca 55, ca 60, if_neg]
    · exact congrFun collectReal addr
    · have rates := layout.rates
      rintro ⟨i, hi, atRow, _⟩
      omega
  obtain ⟨cuts, cutSteps, install, cutsLive, cutCost, cutNat, cutReal, bFixed⟩ := restoreExpansionCuts_spec
    (s := b) rfl rateLive ((cb 9).trans layout.one) ((cb 14).trans layout.zero)
      (by rw [cb 58, cb 54]; exact layout.dictionary) (by rw [cb 59, cb 60]; exact layout.rates)
  let c := {cuts with pc := 0}
  have cc (r : ℕ) (safe : r ∉ [0, 6, 7, 10, 11, 15, 16, 18, 19, 28, 99] := by decide) : c.nr r = s.nr r :=
    (bFixed r (by simp at safe ⊢; omega)).trans (cb r (by simp at safe ⊢; omega))
  have ccCount : c.nr 99 = (freshExpansionOriginals s (s.nr 55)).length := (bFixed 99 (by decide)).trans cbCount
  obtain ⟨scanned, scanSteps, refresh, scanLive, scanCost, scanFrame, scFixed⟩ := refreshExpansionOuterOriginals_spec
    (s := c) rfl cutsLive ((cc 9).trans layout.one)
      (by rw [cc 58, cc 54]; exact layout.dictionary) (by rw [cc 58, cc 65]; exact layout.buckets)
  let d := {scanned with pc := 0}
  have cd (r : ℕ) (safe : r ∉ [0, 6, 7, 10, 11, 15, 16, 17, 18, 19, 24, 25, 26, 28, 99] := by decide) :
      d.nr r = s.nr r := (scFixed r (by simp at safe ⊢; omega)).trans (cc r (by simp at safe ⊢; omega))
  obtain ⟨t, resets, tLive, lastNat, lastReal, lastZero, ids, slack, rates, rows⟩ :=
    resetMatchingSelector_spec d rfl scanLive ((cd 14).trans layout.zero)
  have finalFixed (r : ℕ) (safe : r ∉ [0, 1, 3, 4, 5, 8]) : t.nr r = d.nr r := by
    rw [← resets.run]
    exact arithmeticRun_keeps_from_destination_list _ (by decide) safe d 5
  have dCount : d.nr 99 = (freshExpansionOriginals s (s.nr 55)).length := (scFixed 99 (by decide)).trans ccCount
  let ticks := collectSteps + (rateSteps + (cutSteps + (scanSteps + 5)))
  have full : BlockRuns restoreExpansionCacheBlock ticks s _ :=
    collect.append (rerate.append (install.append (refresh.append resets)))
  have time : t.rr 15 = s.rr 15 := by
    have fixed : ((arithmeticStep restoreExpansionCacheBlock)^[ticks] s).rr 15 = s.rr 15 :=
      arithmeticRun_keeps_real_from_destination_list [0, 2, 3, 4, 5] (by decide) (by decide) s ticks
    rw [full.run] at fixed
    exact fixed
  have finished : ExpansionCacheRestored s t := by
    refine ⟨(finalFixed 99 (by decide)).trans dCount, lastZero, ids.trans (cd 58), slack.trans (cd 59),
      rates.trans (cd 60), rows.trans (cd 61), time, ?_, ?_, ?_⟩
    · intro addr before
      exact (congrFun lastNat addr).trans ((scanFrame.natural addr (by rwa [cc 58])).trans
        ((cutNat addr (by rwa [cb 58])).trans (cbNat addr before)))
    · intro addr before
      exact (congrFun lastReal addr).trans ((scanFrame.real addr (by rwa [cc 59])
        (by rw [cc 59, cc 60]; exact layout.rates) (by rw [cc 59, cc 66]; exact layout.scores)).trans
        ((cutReal addr (by rwa [cb 59])).trans (cbReal addr before)))
    · intro r high other
      exact (finalFixed r (by simp; omega)).trans (cd r (by simp; omega))
  rw [ca 55] at rateCost
  rw [cb 55] at cutCost
  rw [cc 55, ccCount] at scanCost
  refine ⟨_, _, full, tLive, by dsimp [ticks]; omega,
    finished.fresh, finished.zero, finished.identifiers, finished.slacks, finished.rates, finished.rows,
    finished.time, finished.natural, finished.real, finished.fixed⟩



end VehicleRoutingSurvey.Routing
end RppSource_ExpansionCacheRAM

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

/-! matching/ExpansionNeighborFootprint.lean -/
section RppSource_ExpansionNeighborFootprint
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096





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





end VehicleRoutingSurvey.Routing
end RppSource_ExpansionNeighborFootprint

/-! matching/MatchingActiveSelection.lean -/
section RppSource_MatchingActiveSelection
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



theorem MatchingCandidateGroup.slot_lt {k : ℕ} (g : MatchingCandidateGroup k) : g.slot < 3 * k := by
  cases g with
  | outer u | incoming u | cut u => have := u.isLt; simp [MatchingCandidateGroup.slot] <;> omega








end VehicleRoutingSurvey.Routing
end RppSource_MatchingActiveSelection

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

/-! matching/ExpansionCutRows.lean -/
section RppSource_ExpansionCutRows
namespace VehicleRoutingSurvey.Routing

theorem restoreExpansionCutCell_innerRow {k : ℕ} {s : ArithmeticState} {v : Fin k}
    (cutAt : Fin k → Finset (Fin k)) (layout : MatchingCacheLayout k s)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (index : s.nr 7 = v.val) (owner : expansionChildOf s v.val = v.val)
    (inner : 1 < expansionRepRole s v.val) (node : s.nm (s.nr 74 + v.val) ≠ 0) :
    ∃ t steps, BlockRuns restoreExpansionCutCell steps s t ∧ t.halted = false ∧ steps ≤ 32 ∧
      MatchingCandidateRowValid cutAt t (2 * k + v.val) ∧
      readMatchingCandidate cutAt t (2 * k + v.val) =
        some ⟨.cut (cutAt v), s.rm (s.nr 75 + s.nm (s.nr 74 + v.val)), 1⟩ := by
  obtain ⟨t, steps, runs, live, cost, natural, real, fixed⟩ := restoreExpansionCutCell_spec entry running one zero
  let slot := 2 * k + v.val
  let address := s.nr 54 + (slot + slot)
  let d := s.rm (s.nr 75 + s.nm (s.nr 74 + v.val))
  have origOwner : expansionChildOf s (s.nr 7) = s.nr 7 := by rw [index]; exact owner
  have innerAt : ¬expansionRepRole s (s.nr 7) ≤ 1 := by rw [index]; exact Nat.not_le.mpr inner
  have stateNode : matchingInnerNode (expansionCutReadyFull s) = s.nm (s.nr 74 + v.val) := by
    simp [matchingInnerNode, expansionCutReadyFull, index]
  have slotWords : s.nr 55 + s.nr 55 + v.val = slot := by rw [layout.dimension]; dsimp [slot]; omega
  let seed := growthInnerCutData (readyGrowthInnerNode (expansionCutReadyFull s))
  have seedSlot : seed.nr 18 = slot := by
    simpa [seed, growthInnerCutData, readyGrowthInnerNode, expansionCutReadyFull, innerCutCandidateSlot, index]
      using slotWords
  have seedFirst : seed.nr 15 = v.val := by
    simp [seed, growthInnerCutData, readyGrowthInnerNode, expansionCutReadyFull, index]
  have seedLast : seed.nr 16 = k := layout.dimension
  have seedScore : seed.rr 0 = d := by
    simp [seed, growthInnerCutData, readyGrowthInnerNode, expansionCutReadyFull, matchingInnerNode, index, d]
  have seedRate : seed.rr 4 = 1 := rfl
  have natWords : t.nm = Function.update
      (Function.update (Function.update s.nm (s.nr 58 + slot) (slot + 1)) address v.val)
      (address + 1) k := by
    rw [natural, expansionCutNat, if_neg (not_not.mpr origOwner), if_neg innerAt,
      installedMatchingInnerCutNat, if_neg (by simpa only [stateNode] using node)]
    change installedMatchingCandidateNat seed = _
    simp only [installedMatchingCandidateNat, seedSlot, seedFirst, seedLast, address,
      show seed.nm = s.nm from rfl, show seed.nr 54 = s.nr 54 from rfl, show seed.nr 58 = s.nr 58 from rfl]
  have realWords : t.rm = Function.update (Function.update s.rm (s.nr 59 + slot) d) (s.nr 60 + slot) 1 := by
    rw [real, expansionCutReal, if_neg (fun h => h.elim (fun e => e origOwner) innerAt),
      installedMatchingInnerCutReal, if_neg (by simpa only [stateNode] using node)]
    change installedMatchingCandidateReal seed = _
    simp only [installedMatchingCandidateReal, seedSlot, seedScore, seedRate,
      show seed.rm = s.rm from rfl, show seed.nr 59 = s.nr 59 from rfl, show seed.nr 60 = s.nr 60 from rfl]
  have rows := layout.rows
  have vp := v.isLt
  have idsBefore := layout.idsBefore
  have slacksBefore := layout.slacksBefore
  have id : t.nm (t.nr 58 + slot) = slot + 1 := by
    rw [fixed 58 (by decide), natWords]
    simp (disch := omega) [slot, address, Function.update_of_ne]
  have first : t.nm (t.nr 54 + (slot + slot)) = v.val := by
    rw [fixed 54 (by decide), natWords]
    simp (disch := omega) [address, Function.update_of_ne]
  have second : t.nm (t.nr 54 + (slot + slot) + 1) = k := by
    rw [fixed 54 (by decide), natWords]
    simp [address]
  have decoded : decodeMatchingDictionaryEvent k cutAt t (slot + 1) = some (.cut (cutAt v)) := by
    simp [decodeMatchingDictionaryEvent, first, second, vp]
  have slack : t.rm (t.nr 59 + slot) = d := by
    rw [fixed 59 (by decide), realWords]
    simp (disch := omega) [Function.update_of_ne, slot]
  have rate : t.rm (t.nr 60 + slot) = 1 := by rw [fixed 60 (by decide), realWords]; simp
  have stored : decodeMatchingDictionaryEvent k cutAt t (t.nm (t.nr 58 + slot)) = some (.cut (cutAt v)) := by
    rwa [id]
  have item : readMatchingCandidate cutAt t slot = some ⟨.cut (cutAt v), d, 1⟩ := by
    simp [readMatchingCandidate, id, decoded, slack, rate]
  exact ⟨t, steps, runs, live, cost, Or.inr ⟨id, .cut (cutAt v), stored⟩, item⟩

theorem restoreExpansionCutCell_emptyRow {k : ℕ} {s : ArithmeticState} {v : Fin k}
    (cutAt : Fin k → Finset (Fin k)) (size : s.nr 55 = k)
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (index : s.nr 7 = v.val) (owner : expansionChildOf s v.val = v.val)
    (cleared : expansionRepRole s v.val ≤ 1 ∨ s.nm (s.nr 74 + v.val) = 0) :
    ∃ t steps, BlockRuns restoreExpansionCutCell steps s t ∧ t.halted = false ∧ steps ≤ 32 ∧
      MatchingCandidateRowValid cutAt t (2 * k + v.val) ∧ readMatchingCandidate cutAt t (2 * k + v.val) = none := by
  obtain ⟨t, steps, runs, live, cost, natural, _, fixed⟩ := restoreExpansionCutCell_spec entry running one zero
  let slot := 2 * k + v.val
  have origOwner : expansionChildOf s (s.nr 7) = s.nr 7 := by rw [index]; exact owner
  have slotWords : s.nr 55 + s.nr 55 + s.nr 7 = slot := by rw [size, index]; dsimp [slot]; omega
  have clearedMem : t.nm = Function.update s.nm (s.nr 58 + slot) 0 := by
    rw [natural, expansionCutNat, if_neg (not_not.mpr origOwner)]
    by_cases noCut : expansionRepRole s (s.nr 7) ≤ 1
    · rw [if_pos noCut, slotWords]
    · have singleton : s.nm (s.nr 74 + v.val) = 0 := cleared.resolve_left (by simpa only [index] using noCut)
      have stateNode : matchingInnerNode (expansionCutReadyFull s) = 0 := by
        simp [matchingInnerNode, expansionCutReadyFull, index, singleton]
      rw [if_neg noCut, installedMatchingInnerCutNat, if_pos stateNode]
      change Function.update s.nm (s.nr 58 + (s.nr 55 + s.nr 55 + s.nr 7)) 0 = _
      rw [slotWords]
  have missing : t.nm (t.nr 58 + slot) = 0 := by
    rw [fixed 58 (by decide), clearedMem]
    simp
  exact ⟨t, steps, runs, live, cost, Or.inl missing,
    by change readMatchingCandidate cutAt t slot = none; simp [readMatchingCandidate, missing, decodeMatchingDictionaryEvent]⟩

/-- Changing one cut row leaves the other decoded candidate rows unchanged. -/
theorem expansionCutCell_keeps_otherRows {k : ℕ} {s t : ArithmeticState}
    (cutAt : Fin k → Finset (Fin k)) (layout : MatchingCacheLayout k s) (index : s.nr 7 < k)
    (natural : t.nm = expansionCutNat s) (real : t.rm = expansionCutReal s)
    (fixed : ∀ r ≥ 50, t.nr r = s.nr r) {i : ℕ} (within : i < s.nr 61) (other : i ≠ 2 * k + s.nr 7)
    (before : MatchingCandidateRowValid cutAt s i) :
    MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i = readMatchingCandidate cutAt s i := by
  let target := 2 * k + s.nr 7
  let dict (j : ℕ) := s.nr 54 + (j + j)
  have targetEq : s.nr 55 + s.nr 55 + s.nr 7 = target := by rw [layout.dimension]; dsimp [target]; omega
  have targetWithin : target < s.nr 61 := by rw [layout.rows]; dsimp [target]; omega
  have idsBefore := layout.idsBefore
  have slacksBefore := layout.slacksBefore
  let seed := growthInnerCutData (readyGrowthInnerNode (expansionCutReadyFull s))
  have seedSlot : seed.nr 18 = target := by
    simpa [seed, growthInnerCutData, readyGrowthInnerNode, expansionCutReadyFull, innerCutCandidateSlot]
      using targetEq
  have untouchedNat (a : ℕ) (aId : a ≠ s.nr 58 + target) (aFirst : a ≠ dict target)
      (aSecond : a ≠ dict target + 1) : t.nm a = s.nm a := by
    rw [natural, expansionCutNat]
    split
    · rfl
    · split
      · rw [targetEq, Function.update_of_ne aId]
      · unfold installedMatchingInnerCutNat
        split
        · change Function.update s.nm (s.nr 58 + (s.nr 55 + s.nr 55 + s.nr 7)) 0 a = s.nm a
          rw [targetEq, Function.update_of_ne aId]
        · change installedMatchingCandidateNat seed a = s.nm a
          simp only [installedMatchingCandidateNat, seedSlot, show seed.nr 58 = s.nr 58 from rfl,
            show seed.nr 54 = s.nr 54 from rfl, show seed.nm = s.nm from rfl,
            ← show dict target = s.nr 54 + (target + target) from rfl,
            Function.update_of_ne aId, Function.update_of_ne aFirst, Function.update_of_ne aSecond]
  have untouchedReal (a : ℕ) (aSlack : a ≠ s.nr 59 + target) (aRate : a ≠ s.nr 60 + target) : t.rm a = s.rm a := by
    rw [real, expansionCutReal]
    split
    · rfl
    · unfold installedMatchingInnerCutReal
      split
      · rfl
      · change installedMatchingCandidateReal seed a = s.rm a
        simp only [installedMatchingCandidateReal, seedSlot, show seed.nr 59 = s.nr 59 from rfl,
          show seed.nr 60 = s.nr 60 from rfl, show seed.rm = s.rm from rfl,
          Function.update_of_ne aSlack, Function.update_of_ne aRate]
  have identification : t.nm (t.nr 58 + i) = s.nm (s.nr 58 + i) := by
    rw [fixed 58 (by decide)]
    exact untouchedNat _ (by omega) (by dsimp [dict]; omega) (by dsimp [dict]; omega)
  have oldWords (j : ℕ) (pairWord : j ≤ 1) : t.nm (dict i + j) = s.nm (dict i + j) :=
    untouchedNat _ (by dsimp [dict]; omega) (by dsimp [dict]; omega) (by dsimp [dict]; omega)
  have oldEvent : decodeMatchingDictionaryEvent k cutAt t (s.nm (s.nr 58 + i)) =
      decodeMatchingDictionaryEvent k cutAt s (s.nm (s.nr 58 + i)) := by
    rcases before with absent | ⟨own, _, _⟩
    · simp [absent, decodeMatchingDictionaryEvent]
    · have wordA : t.nm (s.nr 54 + (i + i)) = s.nm (s.nr 54 + (i + i)) := by simpa [dict] using oldWords 0 (by decide)
      have wordB : t.nm (s.nr 54 + (i + i) + 1) = s.nm (s.nr 54 + (i + i) + 1) := oldWords 1 (by decide)
      simp [own, decodeMatchingDictionaryEvent, fixed 54 (by decide), wordA, wordB]
  have slack : t.rm (t.nr 59 + i) = s.rm (s.nr 59 + i) := by
    rw [fixed 59 (by decide)]
    exact untouchedReal _ (by omega) (by omega)
  have rate : t.rm (t.nr 60 + i) = s.rm (s.nr 60 + i) := by
    rw [fixed 60 (by decide)]
    exact untouchedReal _ (by omega) (by omega)
  exact ⟨by simpa only [MatchingCandidateRowValid, identification, oldEvent] using before,
    by simp only [readMatchingCandidate, identification, oldEvent, slack, rate]⟩

end VehicleRoutingSurvey.Routing
end RppSource_ExpansionCutRows

/-! matching/MatchingExpansionCutValues.lean -/
section RppSource_MatchingExpansionCutValues
namespace VehicleRoutingSurvey.Routing

/-- The cut pass ends before the normalized outer-pair buckets. -/
structure ExpansionCutMemoryFrame (s t : ArithmeticState) : Prop where
  natural : ∀ a, (a < s.nr 58 ∨ s.nr 65 ≤ a) → t.nm a = s.nm a
  real : ∀ a, (a < s.nr 59 ∨ s.nr 66 ≤ a) → t.rm a = s.rm a

theorem expansionCutCell_memoryFrame {k : ℕ} {s t : ArithmeticState}
    (layout : MatchingCacheLayout k s) (index : s.nr 7 < k)
    (nat : t.nm = expansionCutNat s) (real : t.rm = expansionCutReal s) : ExpansionCutMemoryFrame s t := by
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

theorem ExpansionCutMemoryFrame.pair {k : ℕ} {s t : ArithmeticState} (frame : ExpansionCutMemoryFrame s t)
    (ids : t.nr 65 = s.nr 65) (scores : t.nr 66 = s.nr 66) (i : ℕ) :
    MatchingPairBucketValid k t i = MatchingPairBucketValid k s i ∧
      readMatchingPairBucket (k := k) t i = readMatchingPairBucket (k := k) s i := by
  have first := frame.natural (s.nr 65 + (i+i)) (.inr (by omega))
  have second := frame.natural (s.nr 65 + (i+i) + 1) (.inr (by omega))
  have score := frame.real (s.nr 66 + i) (.inr (by omega))
  constructor <;> simp only [MatchingPairBucketValid, readMatchingPairBucket, ids, scores, first, second, score]

def expansionCutRowValue {k : ℕ} (cutAt : Fin k → Finset (Fin k)) (s : ArithmeticState) (v : Fin k) :
    Option (DualSlack (MatchingDualEvent k)) :=
  if expansionRepRole s v.val ≤ 1 ∨ s.nm (s.nr 74 + v.val) = 0 then none else
    some ⟨.cut (cutAt v), s.rm (s.nr 75 + s.nm (s.nr 74 + v.val)), 1⟩

theorem restoreExpansionCutCell_rows {k : ℕ} {s : ArithmeticState} (cutAt : Fin k → Finset (Fin k))
    (layout : MatchingCacheLayout k s) (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 9 = 1) (zero : s.nr 14 = 0) (v : Fin k) (index : s.nr 7 = v.val)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i) :
    ∃ t steps, BlockRuns restoreExpansionCutCell steps s t ∧ t.halted = false ∧ steps ≤ 32 ∧
      ExpansionCutMemoryFrame s t ∧ (∀ r, r ∉ [0,6,10,15,16,18,19,28] → t.nr r = s.nr r) ∧
      ∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i =
        if i = 2*k + v.val ∧ expansionChildOf s v.val = v.val then expansionCutRowValue cutAt s v
        else readMatchingCandidate cutAt s i := by
  obtain ⟨t, steps, run, live, short, nat, real, fixed⟩ := restoreExpansionCutCell_spec entry running one zero
  have within : s.nr 7 < k := index.symm ▸ v.isLt
  have high (r : ℕ) (hr : 50 ≤ r) := fixed r (by simp; omega)
  refine ⟨t, steps, run, live, short, expansionCutCell_memoryFrame layout within nat real, fixed, ?_⟩
  intro i hi
  by_cases hit : i = 2*k+v.val
  · subst i
    by_cases owner : expansionChildOf s v.val = v.val
    · rw [if_pos ⟨rfl, owner⟩]
      by_cases empty : expansionRepRole s v.val ≤ 1 ∨ s.nm (s.nr 74 + v.val) = 0
      · obtain ⟨z, _, check, _, _, valid, value⟩ := restoreExpansionCutCell_emptyRow cutAt layout.dimension entry running
          one zero index owner empty
        have same := (check.same_exit run).2
        subst z
        exact ⟨valid, by simpa only [expansionCutRowValue, if_pos empty] using value⟩
      · obtain ⟨inner, node⟩ := not_or.mp empty
        obtain ⟨z, _, check, _, _, valid, value⟩ := restoreExpansionCutCell_innerRow cutAt layout entry running one zero
          index owner (Nat.lt_of_not_ge inner) node
        have same := (check.same_exit run).2
        subst z
        exact ⟨valid, by simpa only [expansionCutRowValue, if_neg empty] using value⟩
    · have notOwn : expansionChildOf s (s.nr 7) ≠ s.nr 7 := by simpa only [index] using owner
      have sameNat : t.nm = s.nm := by rw [nat, expansionCutNat, if_pos notOwn]
      have sameReal : t.rm = s.rm := by rw [real, expansionCutReal, if_pos (Or.inl notOwn)]
      have kept := rows (2*k+v.val) hi
      rw [if_neg (fun h => owner h.2)]
      constructor
      · simpa only [MatchingCandidateRowValid, decodeMatchingDictionaryEvent, sameNat, high 54 (by decide),
          high 58 (by decide)] using kept
      · simp only [readMatchingCandidate, decodeMatchingDictionaryEvent, sameNat, sameReal, high 54 (by decide),
          high 58 (by decide), high 59 (by decide), high 60 (by decide)]
  · rw [if_neg (fun h => hit h.1)]
    exact expansionCutCell_keeps_otherRows cutAt layout within nat real high hi (by simpa only [index] using hit) (rows i hi)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionCutValues

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

/-- The selected direct-child cut row writes the canonical mathematical cut
entry, including the empty cells for leaves and noninner representatives. -/
theorem expansionCutRowValue_eq_group {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    (dual : MatchingSearchDualMemory part forest s) (v : Fin k) :
    expansionCutRowValue (matchingTopCutAt part) s v = matchingCutGroupEntry part forest v := by
  classical
  let B := part.blocks.block v
  have role : expansionRepRole s v.val = alternatingRoleCode (forest.role v) := (dual.roles v).1
  have node : s.nm (s.nr 74+v.val) = if part.representative v = v ∧ B.card ≠ 1 then dual.node B else 0 := dual.top v
  by_cases active : part.representative v = v ∧ B.card ≠ 1
  · have present := part.blocks.cut_mem (Finset.mem_univ v) active.2
    have nonzero := dual.nodeNonzero B present
    have value := dual.cutValues B present
    have dict : matchingTopCutAt part v = B := by simp [matchingTopCutAt,active.1,B]
    have nonsingle : (part.blocks.block v).card ≠ 1 := active.2
    have atNode : s.nm (s.nr 74+v.val) = dual.node B := node.trans (if_pos active)
    cases kind : forest.role v <;>
      simp [expansionCutRowValue, matchingCutGroupEntry, atNode, active.1, nonsingle, role, kind,
        alternatingRoleCode, nonzero, value, dict, B]
  · have disabled : ¬ (part.representative v = v ∧ (part.blocks.block v).card ≠ 1 ∧ ∃ p, forest.role v = .inner p) :=
      fun h => active ⟨h.1,h.2.1⟩
    simp only [expansionCutRowValue,matchingCutGroupEntry,node,if_neg active,or_true,if_true,if_neg disabled]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionDictionary

/-! matching/MatchingExpansionCutSweep.lean -/
section RppSource_MatchingExpansionCutSweep
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096



private structure ExpansionCutRowsScan {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    (s : ArithmeticState) (seen : ℕ) (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  live : m.halted = false
  index : m.nr 7 = seen
  fixed : ∀ r, r ∉ [0,6,7,10,15,16,18,19,28] → m.nr r = s.nr r
  memory : ExpansionCutMemoryFrame s m
  valid : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt m i
  lower : ∀ i < 2*k, readMatchingCandidate cutAt m i = readMatchingCandidate cutAt s i
  cuts : ∀ v : Fin k, readMatchingCandidate cutAt m (2*k+v.val) =
    if v.val < seen ∧ expansionChildOf s v.val = v.val then expansionCutRowValue cutAt s v
    else readMatchingCandidate cutAt s (2*k+v.val)

/-- Restore the selected child cut rows, keeping the two edge-row ranges
and all normalized original-pair buckets untouched. -/
theorem restoreExpansionCuts_rows {k : ℕ} {s : ArithmeticState} (cutAt : Fin k → Finset (Fin k))
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (layout : MatchingCacheLayout k s) (space : ExpansionCutReadLayout k s)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i) :
    ∃ t ticks, BlockRuns restoreExpansionCuts ticks s t ∧ t.halted = false ∧ ticks ≤ 35*k+2 ∧
      ExpansionCutMemoryFrame s t ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i) ∧
      (∀ i < 2*k, readMatchingCandidate cutAt t i = readMatchingCandidate cutAt s i) ∧
      (∀ v : Fin k, readMatchingCandidate cutAt t (2*k+v.val) =
        if expansionChildOf s v.val = v.val then expansionCutRowValue cutAt s v
        else readMatchingCandidate cutAt s (2*k+v.val)) ∧
      (∀ i, MatchingPairBucketValid k t i = MatchingPairBucketValid k s i ∧
        readMatchingPairBucket (k := k) t i = readMatchingPairBucket (k := k) s i) := by
  let inv := ExpansionCutRowsScan cutAt s
  let z := {s with pc := 0, nr := Function.update s.nr 7 0}
  have zReg (r : ℕ) (away : r ≠ 7) : z.nr r = s.nr r := Function.update_of_ne away _ _
  have zTables (r : ℕ) (h : r ∈ matchingRefreshTableRegisters) : z.nr r = s.nr r :=
    zReg r (by simp [matchingRefreshTableRegisters] at h; omega)
  have stable := (matchingCacheReads_unchanged cutAt (m := s) (t := z) rfl rfl zTables).1
  have start : inv 0 z := by
    refine ⟨rfl, running, by simp [z], fun r away => zReg r (by simp at away; omega),
      ⟨fun _ _ => rfl, fun _ _ => rfl⟩, fun i hi => (stable i).1.symm ▸ rows i hi,
      fun i _ => (stable i).2, fun v => ?_⟩
    simpa using (stable (2*k+v.val)).2
  have next (j : ℕ) (hj : j < k) (m : ArithmeticState) (h : inv j m) :
      ∃ t ticks, ticks ≤ 32 ∧ BlockRuns restoreExpansionCutCell ticks m t ∧ t.halted = false ∧
        inv (j+1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7+t.nr 9)} := by
    let u : Fin k := ⟨j,hj⟩
    have keep (r : ℕ) (safe : r ∉ [0,6,7,10,15,16,18,19,28] := by decide) := h.fixed r safe
    have current := layout.keeps (fun r high => keep r (by simp; omega))
    have unit := (keep 9).trans one
    obtain ⟨t, ticks, run, live, short, writes, fixed, result⟩ :=
      restoreExpansionCutCell_rows cutAt current h.entry h.live unit ((keep 14).trans zero) u h.index
        (fun i hi => h.valid i (keep 61 ▸ hi))
    let n := {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7+t.nr 9)}
    have nReg (r : ℕ) (away : r ≠ 7) : n.nr r = t.nr r := Function.update_of_ne away _ _
    have tables (r : ℕ) (used : r ∈ matchingRefreshTableRegisters) : n.nr r = t.nr r :=
      nReg r (by simp [matchingRefreshTableRegisters] at used; omega)
    have after := (matchingCacheReads_unchanged cutAt (m := t) (t := n) rfl rfl tables).1
    have owners (v : Fin k) : expansionChildOf m v.val = expansionChildOf s v.val := by
      rw [expansionChildOf, expansionChildOf, keep 79]
      exact h.memory.natural _ (.inr (by have room := space.owners; omega))
    have outputs (v : Fin k) : expansionCutRowValue cutAt m v = expansionCutRowValue cutAt s v := by
      have vh := v.isLt
      have role : expansionRepRole m v.val = expansionRepRole s v.val := by
        rw [expansionRepRole, expansionRepRole, keep 51]
        exact h.memory.natural _ (.inl (by have room := space.roles; omega))
      have id : m.nm (s.nr 74+v.val) = s.nm (s.nr 74+v.val) :=
        h.memory.natural _ (.inr (by have room := space.nodes; omega))
      have value : m.rm (s.nr 75+s.nm (s.nr 74+v.val)) = s.rm (s.nr 75+s.nm (s.nr 74+v.val)) :=
        h.memory.real _ (.inr (by have room := space.duals; omega))
      simp only [expansionCutRowValue, role, keep 74, keep 75, id, value]
    refine ⟨t, ticks, short, run, live, ⟨rfl, live, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simp [fixed 7 (by decide), fixed 9 (by decide), h.index, unit]
    · intro r safe
      exact (nReg r (by simp at safe; omega)).trans ((fixed r (by simp at safe ⊢; omega)).trans (keep r safe))
    · exact ⟨fun a outside => (writes.natural a (by rwa [keep 58, keep 65])).trans (h.memory.natural a outside),
        fun a outside => (writes.real a (by rwa [keep 59, keep 66])).trans (h.memory.real a outside)⟩
    · intro i hi
      exact (after i).1.symm ▸ (result i ((keep 61).symm ▸ hi)).1
    · intro i low
      have fits : i < m.nr 61 := by rw [current.rows]; omega
      have miss : i ≠ 2*k+u.val := by omega
      exact (after i).2.trans (((result i fits).2.trans (if_neg (fun c => miss c.1))).trans (h.lower i low))
    · intro v
      have fits : 2*k+v.val < m.nr 61 := by rw [current.rows]; have range := v.isLt; omega
      change readMatchingCandidate cutAt n (2*k+v.val) = _
      rw [(after _).2, (result _ fits).2, owners u, outputs u, h.cuts v]
      by_cases same : v = u
      · subst v
        simp [u]
      · have distinct : v.val ≠ j := fun eq => same (Fin.ext eq)
        have slots : 2*k+v.val ≠ 2*k+u.val := by change 2*k+v.val ≠ 2*k+j; omega
        have less : v.val < j+1 ↔ v.val < j := by omega
        have skip : ¬ (2*k+v.val = 2*k+u.val ∧ expansionChildOf s u.val = u.val) := fun c => slots c.1
        simp only [if_neg skip, less]
  obtain ⟨last, ticks, out, short, run⟩ := countedLoopFromZero_bounded 9 7 55 k 32 restoreExpansionCutCell inv
    entry running start (fun _ _ h => ⟨h.entry, h.live, h.index, (h.fixed 55 (by decide)).trans layout.dimension⟩) next
  refine ⟨_, ticks, run, out.live, by omega, ⟨out.memory.natural, out.memory.real⟩, out.valid, out.lower, ?_, ?_⟩
  · intro v
    change readMatchingCandidate cutAt last (2*k+v.val) = _
    simpa only [v.isLt, true_and] using out.cuts v
  · exact fun i => out.memory.pair (out.fixed 65 (by decide)) (out.fixed 66 (by decide)) i

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionCutSweep

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

/-- Retagging the cut dictionary only changes occupied cells at the split.
All such cells are overwritten there. The untouched cells already contain
the surviving cut entry under the new dictionary. -/
theorem MatchingExpansionChildPorts.cutSeed {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {B : Finset (Fin k)} (ports : MatchingExpansionChildPorts state B)
    (chosen : B ∈ Finset.univ.image part.blocks.block) (present : B ∈ state.cuts) (zero : state.cutDual B = 0)
    (internal : state.InternalCuts) (external : ∀ p ∈ ports.ports, ∀ w, state.partialMate p = some w → w ∉ ports.block p)
    {forest : AlternatingForestState (Fin k)} {source base : Fin k} (children : List (Fin k)) (entry : ℕ)
    (cycle : ports.ports = (base :: children).toFinset) (baseFixed : part.representative base = base)
    (baseBlock : part.blocks.block base = B) {positive : 0 < k} {s : ArithmeticState}
    (owners : ∀ v : Fin k, expansionChildOf s v.val = if v ∈ B then (ports.owner v).val else k)
    (v : Fin k)
    (oldEntry : readMatchingCandidate (matchingTopCutAt part) s (2*k+v.val) = matchingCutGroupEntry part forest v) :
    let opened := part.openZeroCut chosen present zero (ports.toExpansionChildren internal external)
    let after := forest.expandBlossom source base children entry
    ∀ dual : MatchingSearchDualMemory opened after s,
      (if expansionChildOf s v.val = v.val then expansionCutRowValue (matchingTopCutAt opened) s v
        else readMatchingCandidate (matchingTopCutAt opened) s (2*k+v.val)) = matchingCutGroupEntry opened after v := by
  classical
  intro opened after dual
  by_cases writes : expansionChildOf s v.val = v.val
  · rw [if_pos writes]
    exact expansionCutRowValue_eq_group dual v
  rw [if_neg writes]
  have basePort : base ∈ ports.ports := cycle.symm ▸ List.mem_toFinset.mpr List.mem_cons_self
  have outsidePort : v ∉ ports.ports := by
    intro port
    have self := ports.containsPort v port
    exact writes (by rw [owners,if_pos (ports.subset v port self),ports.unique v port v self])
  have oldNew : matchingCutGroupEntry opened after v = matchingCutGroupEntry part forest v := by
    by_cases inside : v ∈ B
    · have notFixed : part.representative v ≠ v := by
        have atBase := (part.same_block.mpr (((part.block_eq_iff_member chosen v).mpr inside).trans baseBlock.symm)).trans baseFixed
        exact fun eq => outsidePort ((atBase.symm.trans eq) ▸ basePort)
      have noPort : opened.representative v ≠ v := by
        change (if v ∈ B then ports.owner v else part.representative v) ≠ v
        rw [if_pos inside]
        exact fun eq => outsidePort (eq ▸ (ports.covered _ inside).1)
      simp [matchingCutGroupEntry,noPort,notFixed]
    · have rep : opened.representative v = part.representative v := by
        change (if v ∈ B then ports.owner v else part.representative v) = _; rw [if_neg inside]
      have block : opened.blocks.block v = part.blocks.block v :=
        (part.openZeroCut_block chosen present zero _ v).trans (if_neg inside)
      have away : v ∉ base :: children := fun hit => outsidePort (cycle.symm ▸ List.mem_toFinset.mpr hit)
      have role : after.role v = forest.role v := forest.expandAlong_keeps_role source base v _
        (not_on_blossom_expansion entry away) (fun eq => away (eq.symm ▸ List.mem_cons_self))
      have cuts : (state.eraseZeroCut present zero).cutDual = state.cutDual := rfl
      simp only [matchingCutGroupEntry,rep,block,role,cuts]
  rw [oldNew,← oldEntry]
  apply matchingCandidate_changeCutMap
  intro p slack rate hit
  have active : part.representative v = v ∧ matchingTopCutAt part p = part.blocks.block v := by
    rw [oldEntry,matchingCutGroupEntry] at hit
    split at hit
    · rename_i enabled
      exact ⟨enabled.1,(MatchingDualEvent.cut.inj (congrArg DualSlack.event (Option.some.inj hit))).symm⟩
    · cases hit
  have full : (part.blocks.block v).Nonempty := ⟨v,part.blocks.self_mem v (Finset.mem_univ v)⟩
  have location := matchingTopCutAt_port part positive full active.2
  have eq := location.2.2.symm.trans ((part.representativeOf_block positive v).trans active.1)
  subst p
  have outside : v ∉ B := by
    intro inside
    have atBase := (part.same_block.mpr (((part.block_eq_iff_member chosen v).mpr inside).trans baseBlock.symm)).trans baseFixed
    exact outsidePort ((atBase.symm.trans active.1) ▸ basePort)
  have stable : opened.representative v = v := by
    exact (if_neg outside).trans active.1
  rw [matchingTopCutAt,if_pos stable,matchingTopCutAt,if_pos active.1]
  exact (part.openZeroCut_block chosen present zero _ v).trans (if_neg outside)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionCutMeaning

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

def expansionIncomingRoleAt (s : ArithmeticState) (role slot : ℕ) : Prop :=
  ∃ v < s.nr 55, slot = s.nr 55 + v ∧ expansionOriginalHasRole s role v

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

open Classical in
/-- Clearing and rerating incoming rows preserve their event dictionary. A
rerated row keeps its original minimum witness and raw slack. -/
theorem expansionIncomingRates_rows {k : ℕ} {s t : ArithmeticState}
    (cutAt : Fin k → Finset (Fin k)) (layout : MatchingCacheLayout k s)
    (natural : ∀ a, t.nm a = expansionIncomingNat s (s.nr 55) a)
    (real : ∀ a, t.rm a = expansionIncomingReal s (s.nr 55) a)
    (fixed : ∀ r ≥ 50, t.nr r = s.nr r)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i) :
    ∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧
      readMatchingCandidate cutAt t i =
        if expansionIncomingRoleAt s 1 i then none else
          (readMatchingCandidate cutAt s i).map (fun d =>
            {d with rate := if expansionIncomingRoleAt s 0 i then 1 else d.rate}) := by
  classical
  have idsBefore := layout.idsBefore
  have slacksBefore := layout.slacksBefore
  have size := layout.rows
  have dim := layout.dimension
  have identifier (i : ℕ) : t.nm (t.nr 58 + i) =
      if expansionIncomingRoleAt s 1 i then 0 else s.nm (s.nr 58 + i) := by
    rw [fixed 58 (by decide), natural]
    simp only [expansionIncomingNat, expansionIncomingRoleAt, Nat.add_left_cancel_iff, Nat.add_assoc]
    split <;> simp_all
  have dict (a : ℕ) (after : s.nr 54 ≤ a) : t.nm a = s.nm a := by
    rw [natural, expansionIncomingNat, if_neg]
    rintro ⟨v, within, eq, _⟩
    omega
  have decode (id : ℕ) : decodeMatchingDictionaryEvent k cutAt t id = decodeMatchingDictionaryEvent k cutAt s id := by
    unfold decodeMatchingDictionaryEvent
    rw [fixed 54 (by decide)]
    simp only [dict (s.nr 54 + (id - 1 + (id - 1))) (by omega),
      dict (s.nr 54 + (id - 1 + (id - 1)) + 1) (by omega)]
  have slack (i : ℕ) (within : i < s.nr 61) : t.rm (t.nr 59 + i) = s.rm (s.nr 59 + i) := by
    rw [fixed 59 (by decide), real, expansionIncomingReal, if_neg]
    rintro ⟨v, hv, eq, _⟩
    omega
  have rate (i : ℕ) : t.rm (t.nr 60 + i) =
      if expansionIncomingRoleAt s 0 i then 1 else s.rm (s.nr 60 + i) := by
    rw [fixed 60 (by decide), real]
    simp only [expansionIncomingReal, expansionIncomingRoleAt, Nat.add_left_cancel_iff, Nat.add_assoc]
    split <;> simp_all
  intro i within
  by_cases clears : expansionIncomingRoleAt s 1 i
  · have missing := (identifier i).trans (if_pos clears)
    exact ⟨Or.inl missing, by simp [readMatchingCandidate, missing, clears, decodeMatchingDictionaryEvent]⟩
  · have sameId := (identifier i).trans (if_neg clears)
    constructor
    · simpa only [MatchingCandidateRowValid, sameId, decode] using rows i within
    · simp [readMatchingCandidate, clears, sameId, decode, slack i within, rate, Option.map_map, Function.comp_def]









end VehicleRoutingSurvey.Routing
end RppSource_ExpansionIncomingRows

/-! matching/MatchingExpansionIncomingSeed.lean -/
section RppSource_MatchingExpansionIncomingSeed
namespace VehicleRoutingSurvey.Routing

open Classical in
noncomputable def matchingExpansionIncomingSeed {k : ℕ} (s : ArithmeticState) (v : Fin k)
    (cached : Option (DualSlack (MatchingDualEvent k))) :=
  if expansionOriginalHasRole s 1 v.val then none else cached.map fun d =>
    {d with rate := if expansionOriginalHasRole s 0 v.val then 1 else d.rate}

theorem matchingExpansionIncomingSeed_eq {k : ℕ} {s : ArithmeticState} {v : Fin k} {old new : ℕ}
    (cached : Option (DualSlack (MatchingDualEvent k))) (inside : Prop) [Decidable inside]
    (inRegion : ∀ role, expansionOriginalHasRole s role v.val ↔ inside ∧ new = role)
    (oldInner : inside → old = 2) (same : ¬inside → new = old)
    (sound : ∀ d, cached = some d → old ≠ 1 ∧ d.rate = if old = 0 then 1 else 0) :
    matchingExpansionIncomingSeed s v cached =
      if new = 1 then none else cached.map fun d => {d with rate := if new = 0 then 1 else 0} := by
  classical
  by_cases present : inside
  · have prior := oldInner present
    cases h : cached with
    | none => simp [matchingExpansionIncomingSeed,inRegion,present]
    | some d =>
      have rate := (sound d h).2
      norm_num [prior] at rate
      simp [matchingExpansionIncomingSeed,inRegion,present,rate]
  · have agree := same present
    cases h : cached with
    | none => simp [matchingExpansionIncomingSeed,inRegion,present]
    | some d =>
      obtain ⟨off,rate⟩ := sound d h
      simp [matchingExpansionIncomingSeed,inRegion,present,agree,off,rate]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionIncomingSeed

/-! matching/MatchingExpansionCollectTables.lean -/
section RppSource_MatchingExpansionCollectTables
namespace VehicleRoutingSurvey.Routing



theorem matchingExpansionFreshSources_mem {k : ℕ} {s : ArithmeticState} (v : Fin k) :
    v ∈ matchingExpansionFreshSources k s ↔ expansionOriginalHasRole s 1 v.val := by
  simp [matchingExpansionFreshSources,expansionOriginalHasRole]

theorem matchingExpansionFreshSources_values {k : ℕ} {s : ArithmeticState} (size : s.nr 55 = k) :
    freshExpansionOriginals s (s.nr 55) = (matchingExpansionFreshSources k s).map Fin.val := by
  let pick (v : ℕ) := decide (expansionChildOf s v < s.nr 55) &&
    decide (expansionRepRole s (expansionChildOf s v) = 1)
  have range : (List.finRange k).map Fin.val = List.range k := by
    apply List.ext_getElem <;> simp
  change (List.range (s.nr 55)).filter pick = _
  rw [size,← range,List.filter_map]
  rfl

/-- The collector writes only its compact work list. All incoming rows,
normalized outer buckets and fixed refresh reads survive. -/
theorem collectExpansionOuterOriginals_tables {k : ℕ} {s : ArithmeticState}
    {rep : Fin k → Fin k} {role : Fin k → ℕ} {cost : Fin k → Fin k → ℝ} {eff : Fin k → ℝ}
    (cutAt : Fin k → Finset (Fin k)) (entry : s.pc = 0) (running : s.halted = false) (unit : s.nr 9 = 1)
    (input : MatchingRefreshInput s rep role cost eff) (after : s.nr 65+2*(k*k) ≤ s.nr 88)
    (mapAbove : s.nr 88+s.nr 55 ≤ s.nr 79) (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i) :
    let fresh := matchingExpansionFreshSources k s
    ∃ t ticks, BlockRuns collectExpansionOuterOriginals ticks s t ∧ t.halted = false ∧ ticks ≤ 14*k+3 ∧
      t.nr 99 = fresh.length ∧ (∀ i : Fin fresh.length, t.nm (t.nr 88+i.val) = (fresh.get i).val) ∧
      MatchingRefreshInput t rep role cost eff ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i = readMatchingCandidate cutAt s i) ∧
      (∀ i < k*k, MatchingPairBucketValid k t i = MatchingPairBucketValid k s i ∧
        readMatchingPairBucket (k := k) t i = readMatchingPairBucket (k := k) s i) ∧
      (∀ a, a < s.nr 88 ∨ s.nr 88+s.nr 55 ≤ a → t.nm a = s.nm a) ∧ t.rm = s.rm ∧
      ∀ r, r ∉ [0,6,7,10,19,99] → t.nr r = s.nr r := by
  intro fresh
  have layout := input.layout
  have size := layout.dimension
  have roles := input.rolesBefore
  have ids := layout.idsBefore
  have records := layout.recordsBefore
  obtain ⟨t,ticks,run,live,budget,count,words,nat,real,fixed⟩ := collectExpansionOuterOriginals_spec
    entry running unit (by omega) mapAbove
  have tables (r : ℕ) (h : r ∈ matchingRefreshTableRegisters) : t.nr r = s.nr r :=
    fixed r (by simp [matchingRefreshTableRegisters] at h; simp; omega)
  have result := matchingCacheRegionReads layout (fun r h => fixed r (by simp at h; simp; omega))
    (fun a _ hi => nat a (.inl (hi.trans_le after))) (fun _ _ _ => congrFun real _) cutAt rows
  have values := matchingExpansionFreshSources_values size
  refine ⟨t,ticks,run,live,size ▸ budget,?_,?_,?_,result.1,result.2,nat,real,fixed⟩
  · simpa only [fresh,values,List.length_map] using count
  · intro i
    rw [fixed 88 (by decide)]
    have within : i.val < (freshExpansionOriginals s (s.nr 55)).length := by
      simpa only [fresh,values,List.length_map] using i.isLt
    simpa only [fresh,values,List.getElem_map,List.get_eq_getElem] using words i.val within
  · exact input.keeps ⟨fun a h => nat a (.inl (by omega)),fun _ _ _ _ => congrFun real _⟩ tables

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionCollectTables

/-! matching/MatchingExpansionRerateTables.lean -/
section RppSource_MatchingExpansionRerateTables
namespace VehicleRoutingSurvey.Routing

open Classical in
/-- The incoming-rate sweep touches its own identifiers and rates. Its
normalized outer buckets and all refresh inputs remain available. -/
theorem restoreExpansionIncomingRates_tables {k : ℕ} {s : ArithmeticState}
    {rep : Fin k → Fin k} {role : Fin k → ℕ} {cost : Fin k → Fin k → ℝ} {eff : Fin k → ℝ}
    (cutAt : Fin k → Finset (Fin k)) (entry : s.pc = 0) (running : s.halted = false)
    (unit : s.nr 9 = 1) (zero : s.nr 14 = 0) (input : MatchingRefreshInput s rep role cost eff)
    (mapAbove : s.nr 58+2*s.nr 55 ≤ s.nr 79) (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i) :
    ∃ t ticks, BlockRuns restoreExpansionIncomingRates ticks s t ∧ t.halted = false ∧ ticks ≤ 14*k+2 ∧
      MatchingRefreshInput t rep role cost eff ∧ ExpansionCutMemoryFrame s t ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i =
        if expansionIncomingRoleAt s 1 i then none else (readMatchingCandidate cutAt s i).map
          (fun d => {d with rate := if expansionIncomingRoleAt s 0 i then 1 else d.rate})) ∧
      (∀ i, MatchingPairBucketValid k t i = MatchingPairBucketValid k s i ∧
        readMatchingPairBucket (k := k) t i = readMatchingPairBucket (k := k) s i) ∧
      ∀ r, r ∉ [0,6,7,10,11,19] → t.nr r = s.nr r := by
  classical
  have size := input.layout.dimension
  obtain ⟨t,ticks,run,live,budget,nat,real,fixed⟩ := restoreExpansionIncomingRates_spec entry running unit zero
    (by rw [size]; exact input.rolesBefore) mapAbove
  have ids := input.layout.idsBefore
  have records := input.layout.recordsBefore
  have slacks := input.layout.slacksBefore
  have rates := input.layout.ratesBefore
  have n := input.layout.rows
  have frame : ExpansionCutMemoryFrame s t := by
    constructor
    · intro a outside
      rw [nat,expansionIncomingNat,if_neg]
      rintro ⟨j,hj,eq,_⟩
      omega
    · intro a outside
      rw [real,expansionIncomingReal,if_neg]
      rintro ⟨j,hj,eq,_⟩
      omega
  have tables (r : ℕ) (h : r ∈ matchingRefreshTableRegisters) := fixed r (by simp [matchingRefreshTableRegisters] at h; simp; omega)
  refine ⟨t,ticks,run,live,size ▸ budget,?_,frame,?_,frame.pair (fixed 65 (by decide)) (fixed 66 (by decide)),fixed⟩
  · exact input.keeps ⟨fun a h => frame.natural a (.inl h),fun a h _ _ => frame.real a (.inl h)⟩ tables
  · exact expansionIncomingRates_rows cutAt input.layout nat real (fun r hr => fixed r (by simp; omega)) rows

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionRerateTables

/-! matching/MatchingExpansionCacheSeeds.lean -/
section RppSource_MatchingExpansionCacheSeeds
namespace VehicleRoutingSurvey.Routing

open Classical in
noncomputable def expansionGroupSeed {k : ℕ} (cutAt : Fin k → Finset (Fin k)) (s : ArithmeticState) :
    MatchingCandidateGroup k → Option (DualSlack (MatchingDualEvent k))
  | .outer p => readMatchingCandidate cutAt s p.val
  | .incoming v => matchingExpansionIncomingSeed s v (readMatchingCandidate cutAt s (k+v.val))
  | .cut v => if expansionChildOf s v.val = v.val then expansionCutRowValue cutAt s v
      else readMatchingCandidate cutAt s (2*k+v.val)

private theorem expansionIncomingRole_ether {k : ℕ} {s : ArithmeticState} (size : s.nr 55 = k)
    (r : ℕ) (g : MatchingCandidateGroup k) :
    expansionIncomingRoleAt s r g.slot ↔
      match g with
      | .incoming v => expansionOriginalHasRole s r v.val
      | _ => False := by
  cases g with
  | outer p =>
    change (∃ w < s.nr 55, p.val = s.nr 55+w ∧ _) ↔ False
    rw [size]
    have bound := p.isLt
    constructor
    · rintro ⟨_,_,eq,_⟩
      omega
    · exact False.elim
  | incoming v =>
    change (∃ w < s.nr 55, k+v.val = s.nr 55+w ∧ _) ↔ expansionOriginalHasRole s r v.val
    rw [size]
    constructor
    · rintro ⟨w,_,eq,h⟩
      exact (Nat.add_left_cancel eq).symm ▸ h
    · exact fun h => ⟨v.val,v.isLt,rfl,h⟩
  | cut p =>
    change (∃ w < s.nr 55, 2*k+p.val = s.nr 55+w ∧ _) ↔ False
    rw [size]
    constructor
    · rintro ⟨_,_,eq,_⟩
      omega
    · exact False.elim

open Classical in
theorem expansionGroupSeed_of_passes {k : ℕ} {cutAt : Fin k → Finset (Fin k)} {s incoming cuts : ArithmeticState}
    (size : s.nr 55 = k)
    (rates : ∀ g : MatchingCandidateGroup k, readMatchingCandidate cutAt incoming g.slot =
      if expansionIncomingRoleAt s 1 g.slot then none else
        (readMatchingCandidate cutAt s g.slot).map (fun d =>
          {d with rate := if expansionIncomingRoleAt s 0 g.slot then 1 else d.rate}))
    (lower : ∀ i < 2*k, readMatchingCandidate cutAt cuts i = readMatchingCandidate cutAt incoming i)
    (top : ∀ v : Fin k, readMatchingCandidate cutAt cuts (2*k+v.val) =
      if expansionChildOf s v.val = v.val then expansionCutRowValue cutAt s v else readMatchingCandidate cutAt incoming (2*k+v.val)) :
    ∀ g : MatchingCandidateGroup k, readMatchingCandidate cutAt cuts g.slot = expansionGroupSeed cutAt s g := by
  intro g
  have atRate := rates g
  simp only [expansionIncomingRole_ether size] at atRate
  cases g with
  | outer p =>
    have limit := p.isLt
    change readMatchingCandidate cutAt cuts p.val = readMatchingCandidate cutAt s p.val
    rw [lower _ (by omega)]
    simpa [MatchingCandidateGroup.slot] using atRate
  | incoming v =>
    have limit := v.isLt
    change readMatchingCandidate cutAt cuts (k+v.val) = matchingExpansionIncomingSeed s v _
    rw [lower _ (by omega)]
    exact atRate
  | cut v =>
    have old : readMatchingCandidate cutAt incoming (2*k+v.val) = readMatchingCandidate cutAt s (2*k+v.val) := by
      simpa [MatchingCandidateGroup.slot] using atRate
    simpa only [expansionGroupSeed,MatchingCandidateGroup.slot,old] using top v

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionCacheSeeds

/-! matching/MatchingExpansionCachePrefix.lean -/
section RppSource_MatchingExpansionCachePrefix
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 8192

/-- Collect the new outer originals and reinstall all incoming and cut seeds.
The resulting state is the actual input of the final all-neighbor sweep. -/
theorem matchingExpansionCachePrefix {k : ℕ} {s : ArithmeticState} {rep : Fin k → Fin k} {role : Fin k → ℕ}
    {cost : Fin k → Fin k → ℝ} {eff : Fin k → ℝ} (cutAt : Fin k → Finset (Fin k))
    (entry : s.pc = 0) (running : s.halted = false) (work : ExpansionCacheFrame s)
    (input : MatchingRefreshInput s rep role cost eff) (above : s.nr 65+2*(k*k) ≤ s.nr 88)
    (nodeBefore : s.nr 74+k ≤ s.nr 88) (space : ExpansionCutReadLayout k s)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i) :
    let fresh := matchingExpansionFreshSources k s
    ∃ a b c ac bc cc, BlockRuns collectExpansionOuterOriginals ac s a ∧ a.halted = false ∧
      BlockRuns restoreExpansionIncomingRates bc {a with pc := 0} b ∧ b.halted = false ∧
      BlockRuns restoreExpansionCuts cc {b with pc := 0} c ∧ c.halted = false ∧ ac+bc+cc ≤ 63*k+7 ∧
      c.nr 99 = fresh.length ∧ (∀ i : Fin fresh.length, c.nm (c.nr 88+i.val) = (fresh.get i).val) ∧
      MatchingRefreshInput c rep role cost eff ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt c i) ∧
      (∀ g : MatchingCandidateGroup k, readMatchingCandidate cutAt c g.slot = expansionGroupSeed cutAt s g) ∧
      (∀ i < k*k, MatchingPairBucketValid k c i = MatchingPairBucketValid k s i ∧
        readMatchingPairBucket (k := k) c i = readMatchingPairBucket (k := k) s i) ∧
      (∀ r, r ∉ [0,6,7,10,11,15,16,18,19,28,99] → c.nr r = s.nr r) ∧ c.rr 15 = s.rr 15 := by
  classical
  intro fresh
  have size := input.layout.dimension
  have rowsAt := input.layout.rows
  obtain ⟨a,ac,ar,al,acost,alen,awords,ain,aval,apair,amem,areal,afix⟩ :=
    collectExpansionOuterOriginals_tables cutAt entry running work.one input above work.workListBelowMembers rows
  let a0 := {a with pc := 0}
  have ak (r : ℕ) (h : r ∉ [0,6,7,10,19,99] := by decide) : a0.nr r = s.nr r := afix r h
  have aInput := ain.keeps (t := a0) ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
  obtain ⟨b,bc,br,bl,bcost,bin,bframe,bval,bpair,bfix⟩ := restoreExpansionIncomingRates_tables
    (s := a0) cutAt rfl al ((ak 9).trans work.one) ((ak 14).trans work.zero) aInput
    (by rw [ak 58,ak 55,ak 79]; exact work.incomingBelowMembers)
    (fun i hi => (aval i (ak 61 ▸ hi)).1)
  let b0 := {b with pc := 0}
  have bk (r : ℕ) (h : r ∉ [0,6,7,10,11,19,99] := by decide) : b0.nr r = s.nr r :=
    (bfix r (by simp at h; simp; omega)).trans (ak r (by simp at h; simp; omega))
  obtain ⟨sRole,sOwn,sNode,sDual⟩ := space
  have bspace : ExpansionCutReadLayout k b0 := by
    refine ⟨?_,?_,?_,?_⟩ <;> simp only [bk 51,bk 58,bk 65,bk 79,bk 74,bk 66,bk 75] <;> assumption
  have bInput := bin.keeps (t := b0) ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
  obtain ⟨c,cc,cr,cl,ccost,cframe,cval,clow,ccut,cpair⟩ :=
    restoreExpansionCuts_rows (s := b0) cutAt rfl bl ((bk 9).trans work.one) ((bk 14).trans work.zero)
      bInput.layout bspace (fun i hi => (bval i (by rw [ak 61]; exact bk 61 ▸ hi)).1)
  have ck (r : ℕ) (h : r ∉ [0,6,7,10,15,16,18,19,28] := by decide) : c.nr r = b0.nr r := by
    rw [← cr.run]
    exact arithmeticRun_keeps_from_destination_list _ (by decide) h b0 cc
  have tables (r : ℕ) (h : r ∈ matchingRefreshTableRegisters) := ck r (by simp [matchingRefreshTableRegisters] at h; simp; omega)
  have cinput := bInput.keeps (t := c) ⟨fun a h => cframe.natural a (.inl h),fun a h _ _ => cframe.real a (.inl h)⟩ tables
  have aOwner (v : ℕ) : expansionChildOf a0 v = expansionChildOf s v := by
    rw [expansionChildOf,expansionChildOf,ak 79]
    exact amem _ (.inr (by have bound := work.workListBelowMembers; omega))
  have aRole (v : ℕ) (hi : v < s.nr 55) : expansionRepRole a0 v = expansionRepRole s v := by
    rw [expansionRepRole,expansionRepRole,ak 51]
    exact amem _ (.inl (by have bound := work.rolesBelowIncoming; have bound' := work.cacheBelowWorkList; omega))
  have tested (r i : ℕ) : expansionIncomingRoleAt a0 r i ↔ expansionIncomingRoleAt s r i := by
    have check (v : ℕ) : expansionOriginalHasRole a0 r v ↔ expansionOriginalHasRole s r v := by
      unfold expansionOriginalHasRole
      rw [aOwner,ak 55]
      constructor <;> rintro ⟨bound,code⟩
      · exact ⟨bound,(aRole _ bound).symm.trans code⟩
      · exact ⟨bound,(aRole _ bound).trans code⟩
    simp only [expansionIncomingRoleAt,ak 55,check]
  have bOwner (v : Fin k) : expansionChildOf b0 v.val = expansionChildOf s v.val := by
    rw [← aOwner,expansionChildOf,expansionChildOf,bfix 79 (by decide)]
    exact bframe.natural _ (.inr (by rw [ak 65,ak 79]; omega))
  have cutValue (v : Fin k) : expansionCutRowValue cutAt b0 v = expansionCutRowValue cutAt s v := by
    have within := v.isLt
    have idA : a0.nm (s.nr 74+v.val) = s.nm (s.nr 74+v.val) := amem _ (.inl (by omega))
    have idB : b0.nm (s.nr 74+v.val) = a0.nm (s.nr 74+v.val) :=
      bframe.natural _ (.inr (by rw [ak 65]; omega))
    have roleB : b0.nm (s.nr 51+v.val) = a0.nm (s.nr 51+v.val) :=
      bframe.natural _ (.inl (by rw [ak 58]; omega))
    have dualB : b0.rm (s.nr 75+s.nm (s.nr 74+v.val)) = a0.rm (s.nr 75+s.nm (s.nr 74+v.val)) :=
      bframe.real _ (.inr (by rw [ak 66]; omega))
    have roleA : a0.nm (s.nr 51+v.val) = s.nm (s.nr 51+v.val) :=
      amem _ (.inl (by have bound := work.cacheBelowWorkList; omega))
    have dualA : a0.rm = s.rm := areal
    by_cases empty : s.nm (s.nr 51+v.val) ≤ 1 ∨ s.nm (s.nr 74+v.val) = 0 <;>
      simp only [expansionCutRowValue,expansionRepRole,bk 51,bk 74,bk 75,roleB,roleA,idB,idA,dualB,dualA,empty,if_true,if_false]
  have seed := expansionGroupSeed_of_passes (incoming := b0) (cuts := c) size (fun g => by
    have fits : g.slot < s.nr 61 := rowsAt.symm ▸ g.slot_lt
    have value := (bval g.slot ((ak 61).symm ▸ fits)).2
    have prior : readMatchingCandidate cutAt a0 g.slot = readMatchingCandidate cutAt s g.slot := (aval _ fits).2
    have bReads := matchingCacheReads_unchanged cutAt (m := b) (t := b0) rfl rfl (fun _ _ => rfl)
    simpa only [tested,prior,(bReads.1 g.slot).2] using value) clow
    (fun v => by simpa only [bOwner,cutValue] using ccut v)
  refine ⟨a,b,c,ac,bc,cc,ar,al,br,bl,cr,cl,by omega,?_,?_,cinput,?_,seed,?_,?_,?_⟩
  · exact (ck 99).trans ((bfix 99 (by decide)).trans alen)
  · intro i
    rw [ck 88,bk 88,← ak 88]
    exact (cframe.natural _ (.inr (by rw [bk 65,ak 88]; omega))).trans
      ((bframe.natural _ (.inr (by rw [ak 65,ak 88]; omega))).trans (awords i))
  · intro i hi
    exact cval i ((bk 61).symm ▸ hi)
  · intro i hi
    exact ⟨(cpair i).1.trans ((bpair i).1.trans (apair i hi).1),
      (cpair i).2.trans ((bpair i).2.trans (apair i hi).2)⟩
  · intro r h
    exact (ck r (by simp at h; simp; omega)).trans (bk r (by simp at h; simp; omega))
  · have aTime : a.rr 15 = s.rr 15 := by
      rw [← ar.run]
      exact arithmeticRun_keeps_real_from_destination_list [0] (by decide) (by decide) s ac
    have bTime : b.rr 15 = a0.rr 15 := by
      rw [← br.run]
      exact arithmeticRun_keeps_real_from_destination_list [0,2] (by decide) (by decide) a0 bc
    have cTime : c.rr 15 = b0.rr 15 := by
      rw [← cr.run]
      exact arithmeticRun_keeps_real_from_destination_list [0,2,3,4,5] (by decide) (by decide) b0 cc
    exact cTime.trans (bTime.trans aTime)

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionCachePrefix

/-! matching/MatchingExpansionFreshRows.lean -/
section RppSource_MatchingExpansionFreshRows
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

/-- Each expanded source loads its own published representative before the
neighbor scan, since two newly outer sources may belong to different children. -/
theorem refreshExpansionOuterCell_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} {rep : Fin k → Fin k} {role : Fin k → ℕ}
    {cost : Fin k → Fin k → ℝ} {effective : Fin k → ℝ} {u : Fin k}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (input : MatchingRefreshInput s rep role cost effective) (word : s.nm (s.nr 88 + s.nr 24) = u.val)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k*k, MatchingPairBucketValid k s i) :
    ∃ t steps, steps ≤ 98*k+6 ∧ BlockRuns refreshExpansionOuterCell steps s t ∧ t.halted = false ∧
      t.rr 15 = s.rr 15 ∧ MatchingRefreshInput t rep role cost effective ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i =
        insertSlackCandidates ((List.finRange k).filterMap (fun v => outerRefreshRowInput rep role cost effective u v i))
          (readMatchingCandidate cutAt s i)) ∧
      (∀ i < k*k, MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i =
        insertSlackCandidates ((List.finRange k).filterMap (fun v => outerRefreshPairInput rep role cost effective (s.rr 15) u v i))
          (readMatchingPairBucket (k := k) s i)) ∧
      MatchingCacheFootprint k s t ∧
      (∀ r, r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 25, 26] → t.nr r = s.nr r) := by
  let addr := s.nr 88 + s.nr 24
  let repAddr := s.nr 57 + u.val
  let loaded := Function.update (Function.update (Function.update s.nr 6 addr) 15 u.val) 6 repAddr
  let a := { s with pc := 0, nr := Function.update loaded 26 (rep u).val }
  have loads : BlockRuns readExpansionOuterOriginal 4 s {a with pc := 4} := by
    apply BlockRuns.of_running_exit
    · simp [a, loaded, addr, repAddr, readExpansionOuterOriginal, arithmeticStep, entry, running, word,
        input.representatives u, Function.iterate_succ_apply']
    · exact running
    · rfl
  have fixed (r : ℕ) (safe : r ∉ [6, 15, 26] := by decide) : a.nr r = s.nr r := by
    have no6 : r ≠ 6 := by simp at safe; omega
    have no15 : r ≠ 15 := by simp at safe; omega
    have no26 : r ≠ 26 := by simp at safe; omega
    simp [a, loaded, Function.update_of_ne no6, Function.update_of_ne no15, Function.update_of_ne no26]
  have ports (r : ℕ) (h : r ∈ matchingRefreshTableRegisters) : a.nr r = s.nr r :=
    fixed r (by simp [matchingRefreshTableRegisters] at h ⊢; omega)
  have aInput := input.keeps (t := a) ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ ports
  obtain ⟨row, pair⟩ := matchingCacheReads_unchanged cutAt (m := s) (t := a) rfl rfl ports
  have aRows (i : ℕ) (hi : i < a.nr 61) : MatchingCandidateRowValid cutAt a i := by
    rw [(row i).1]
    exact rows i (fixed 61 ▸ hi)
  have aPairs (i : ℕ) (hi : i < k*k) : MatchingPairBucketValid k a i := (pair i).1.symm ▸ buckets i hi
  obtain ⟨t, steps, budget, scan, live, _, time, after, updatedRows, updatedPairs⟩ :=
    refreshSelectedOuterVertex_rows cutAt (s := a) (u := u) rfl running ((fixed 9).trans one)
      ((fixed 14).trans zero) aInput (by simp [a, loaded]) (by simp [a]) aRows aPairs
  have run : BlockRuns refreshExpansionOuterCell (4 + steps) s _ := loads.append scan
  have offsets : MatchingCacheOffsets k s := ⟨fun i hi => by have h := input.offsetsBefore; omega,
    fun i hi => input.offsets ⟨i, hi⟩⟩
  have reps : MatchingCacheRepresentatives k s := ⟨fun i hi => by have h := input.representativesBefore; omega,
    fun i hi => by rw [input.representatives ⟨i, hi⟩]; exact (rep ⟨i, hi⟩).isLt⟩
  obtain ⟨b, _, other, _, _, footprint, kept⟩ := refreshExpansionOuterCell_footprint entry running one zero
    input.layout offsets reps (word.symm ▸ u.isLt)
  have same := (other.same_exit run).2
  subst b
  refine ⟨_, _, by omega, run, live, time, ?_, ?_, ?_, footprint, kept⟩
  · exact after.keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
  · intro i hi
    change MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i = _
    simpa only [(row i).2] using updatedRows i ((fixed 61).symm ▸ hi)
  · intro i hi
    change MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i = _
    simpa only [(pair i).2, show a.rr 15 = s.rr 15 from rfl] using updatedPairs i hi

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionFreshRows

/-! matching/MatchingExpansionFreshSweep.lean -/
section RppSource_MatchingExpansionFreshSweep
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096

private theorem expansionSource_prefix {α Event : Type*} (fresh : List α)
    (inputs : α → List (DualSlack Event)) (old : Option (DualSlack Event)) (j : ℕ) (hj : j < fresh.length) :
    insertSlackCandidates ((fresh.take (j+1)).flatMap inputs) old =
      insertSlackCandidates (inputs (fresh.get ⟨j, hj⟩)) (insertSlackCandidates ((fresh.take j).flatMap inputs) old) := by
  rw [List.take_succ_eq_append_getElem hj, List.flatMap_append]
  simp [insertSlackCandidates, List.foldl_append]

private structure ExpansionSourceScan {k : ℕ} (cutAt : Fin k → Finset (Fin k)) (s : ArithmeticState)
    (rep : Fin k → Fin k) (role : Fin k → ℕ) (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ)
    (rowSources pairSources : ℕ → Fin k → List (DualSlack (MatchingDualEvent k)))
    (fresh : List (Fin k)) (j : ℕ) (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  live : m.halted = false
  index : m.nr 24 = j
  time : m.rr 15 = s.rr 15
  fixed : ∀ r, r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 26] → m.nr r = s.nr r
  input : MatchingRefreshInput m rep role cost effective
  footprint : MatchingCacheFootprint k s m
  rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt m i ∧ readMatchingCandidate cutAt m i =
    insertSlackCandidates ((fresh.take j).flatMap (rowSources i)) (readMatchingCandidate cutAt s i)
  pairs : ∀ i < k*k, MatchingPairBucketValid k m i ∧ readMatchingPairBucket (k := k) m i =
    insertSlackCandidates ((fresh.take j).flatMap (pairSources i)) (readMatchingPairBucket (k := k) s i)

/-- Insert all entries supplied by the newly outer originals, preserving the
order of the fresh list and the original-endpoint sweep used to break ties. -/
theorem refreshExpansionOuterOriginals_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s : ArithmeticState} {rep : Fin k → Fin k} {role : Fin k → ℕ}
    {cost : Fin k → Fin k → ℝ} {effective : Fin k → ℝ}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (input : MatchingRefreshInput s rep role cost effective) (fresh : List (Fin k))
    (lengthAt : s.nr 99 = fresh.length) (words : ∀ i : Fin fresh.length, s.nm (s.nr 88+i.val) = (fresh.get i).val)
    (freshAfter : s.nr 65 + 2*(k*k) ≤ s.nr 88)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i)
    (buckets : ∀ i < k*k, MatchingPairBucketValid k s i) :
    let rowSources := fun (i : ℕ) (u : Fin k) => (List.finRange k).filterMap
      (fun v => outerRefreshRowInput rep role cost effective u v i)
    let pairSources := fun (i : ℕ) (u : Fin k) => (List.finRange k).filterMap
      (fun v => outerRefreshPairInput rep role cost effective (s.rr 15) u v i)
    ∃ t ticks, ticks ≤ fresh.length * (98*k+9) + 2 ∧ BlockRuns refreshExpansionOuterOriginals ticks s t ∧
      t.halted = false ∧ t.rr 15 = s.rr 15 ∧ MatchingRefreshInput t rep role cost effective ∧
      MatchingCacheFootprint k s t ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ∧ readMatchingCandidate cutAt t i =
        insertSlackCandidates (fresh.flatMap (rowSources i)) (readMatchingCandidate cutAt s i)) ∧
      (∀ i < k*k, MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i =
        insertSlackCandidates (fresh.flatMap (pairSources i)) (readMatchingPairBucket (k := k) s i)) := by
  intro rowSources pairSources
  let inv := ExpansionSourceScan cutAt s rep role cost effective rowSources pairSources fresh
  let z := {s with pc := 0, nr := Function.update s.nr 24 0}
  have ports (r : ℕ) (h : r ∈ matchingRefreshTableRegisters) : z.nr r = s.nr r :=
    Function.update_of_ne (by simp [matchingRefreshTableRegisters] at h; omega) _ _
  obtain ⟨stableRows, stablePairs⟩ := matchingCacheReads_unchanged cutAt (m := s) (t := z) rfl rfl ports
  have start : inv 0 z := by
    refine ⟨rfl, running, by simp [z], rfl, fun r safe => Function.update_of_ne (by simp at safe; omega) _ _,
      input.keeps (t := z) ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ ports, .unchanged rfl rfl, ?_, ?_⟩
    · intro i hi
      exact ⟨(stableRows i).1.symm ▸ rows i hi, by simpa [insertSlackCandidates] using (stableRows i).2⟩
    · intro i hi
      exact ⟨(stablePairs i).1.symm ▸ buckets i hi, by simpa [insertSlackCandidates] using (stablePairs i).2⟩
  have next (j : ℕ) (hj : j < fresh.length) (m : ArithmeticState) (h : inv j m) :
      ∃ t ticks, ticks ≤ 98*k+6 ∧ BlockRuns refreshExpansionOuterCell ticks m t ∧ t.halted = false ∧
        inv (j+1) {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24+t.nr 9)} := by
    let u := fresh.get ⟨j, hj⟩
    have keep (r : ℕ) (safe : r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 26] := by decide) := h.fixed r safe
    have unit := (keep 9).trans one
    have word : m.nm (m.nr 88+m.nr 24) = u.val := by
      rw [keep 88, h.index, h.footprint.natural _ (.inr (by omega))]
      exact words ⟨j, hj⟩
    obtain ⟨t, ticks, short, run, live, time, after, newRows, newPairs, footprint, fixed⟩ :=
      refreshExpansionOuterCell_rows cutAt h.entry h.live unit ((keep 14).trans zero) h.input word
        (fun i hi => (h.rows i (keep 61 ▸ hi)).1) (fun i hi => (h.pairs i hi).1)
    let n := {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24+t.nr 9)}
    have nextReg (r : ℕ) (away : r ≠ 24) : n.nr r = t.nr r := Function.update_of_ne away _ _
    have nextTables (r : ℕ) (used : r ∈ matchingRefreshTableRegisters) : n.nr r = t.nr r :=
      nextReg r (by simp [matchingRefreshTableRegisters] at used; omega)
    obtain ⟨sameRows, samePairs⟩ := matchingCacheReads_unchanged cutAt (m := t) (t := n) rfl rfl nextTables
    have total := h.footprint.chain footprint (fun r listed => keep r (by simp at listed ⊢; omega))
    refine ⟨t, ticks, short, run, live, ⟨rfl, live, ?_, time.trans h.time, ?_,
      after.keeps (t := n) ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ nextTables,
      ⟨total.natural, total.real⟩, ?_, ?_⟩⟩
    · simp [fixed 24 (by decide), fixed 9 (by decide), h.index, unit]
    · intro r safe
      exact (nextReg r (by simp at safe; omega)).trans ((fixed r (by simp at safe ⊢; omega)).trans (keep r safe))
    · intro i hi
      obtain ⟨valid, eq⟩ := newRows i ((keep 61).symm ▸ hi)
      change MatchingCandidateRowValid cutAt n i ∧ readMatchingCandidate cutAt n i = _
      exact ⟨(sameRows i).1.symm ▸ valid, by
        rw [(sameRows i).2, eq, (h.rows i hi).2, expansionSource_prefix fresh (rowSources i) _ j hj]⟩
    · intro i hi
      obtain ⟨valid, eq⟩ := newPairs i hi
      change MatchingPairBucketValid k n i ∧ readMatchingPairBucket (k := k) n i = _
      exact ⟨(samePairs i).1.symm ▸ valid, by
        rw [(samePairs i).2, eq, h.time, (h.pairs i hi).2, expansionSource_prefix fresh (pairSources i) _ j hj]⟩
  obtain ⟨last, ticks, out, short, run⟩ := countedLoopFromZero_bounded 9 24 99 fresh.length (98*k+6)
    refreshExpansionOuterCell inv entry running start
    (fun _ _ h => ⟨h.entry, h.live, h.index, (h.fixed 99 (by decide)).trans lengthAt⟩) next
  have all : fresh.take fresh.length = fresh := List.take_of_length_le le_rfl
  refine ⟨_, ticks, ?_, run, out.live, out.time, ?_, ⟨out.footprint.natural, out.footprint.real⟩, ?_, ?_⟩
  · rw [show 98*k+6+3 = 98*k+9 by omega] at short
    omega
  · exact out.input.keeps ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
  · intro i hi
    change MatchingCandidateRowValid cutAt last i ∧ readMatchingCandidate cutAt last i = _
    simpa only [all] using out.rows i hi
  · intro i hi
    change MatchingPairBucketValid k last i ∧ readMatchingPairBucket (k := k) last i = _
    simpa only [all] using out.pairs i hi

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionFreshSweep

/-! matching/MatchingExpansionPairMeaning.lean -/
section RppSource_MatchingExpansionPairMeaning
namespace VehicleRoutingSurvey.Routing

/-- The physical fresh-source sweep offers original edges in both directed
pair slots. The old source and target representatives may differ from the new ones. -/
noncomputable def expansionPairOffers {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (time : ℝ) (fresh : List (Fin k)) (i : ℕ) :=
  fresh.flatMap (fun u => (List.finRange k).filterMap (fun v => outerRefreshPairInput rep role cost effective time u v i))

theorem expansionPairOffers_mem {k : ℕ} (rep : Fin k → Fin k) (role : Fin k → ℕ)
    (cost : Fin k → Fin k → ℝ) (effective : Fin k → ℝ) (time : ℝ) (fresh : List (Fin k))
    (a b : Fin k) (d : DualSlack (MatchingDualEvent k)) :
    d ∈ expansionPairOffers rep role cost effective time fresh (k*a.val+b.val) ↔
      ∃ u ∈ fresh, ∃ v : Fin k, rep u ≠ rep v ∧ (role (rep v) = 1 ∧
        ((a = rep u ∧ b = rep v) ∨ (a = rep v ∧ b = rep u))) ∧ normalizedOuterEdge cost effective time u v = d := by
  simp only [expansionPairOffers, List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and,
    outerRefreshPairInput_some_iff]

/-- Splitting an inner blossom retains each old outer source and its
representative. Every new outer edge with a fresh endpoint is inserted by
the recorded scan, while nonouter pair cells remain empty. -/
theorem MatchingSearchOuterBuckets.expand {k : ℕ} {s t : ArithmeticState} {oldRep rep : Fin k → Fin k}
    {old role : Fin k → ℕ} {cost : Fin k → Fin k → ℝ} {effective : Fin k → ℝ}
    (cached : MatchingSearchOuterBuckets s oldRep old cost effective) (symmetric : ∀ u v, cost u v = cost v u)
    (oldIdem : ∀ v, oldRep (oldRep v) = oldRep v) (idem : ∀ v, rep (rep v) = rep v)
    (fixed : ∀ p, role p = 1 → rep p = p)
    (stays : ∀ v, old (oldRep v) = 1 → rep v = oldRep v ∧ role (rep v) = 1)
    (fresh : List (Fin k)) (membership : ∀ v, v ∈ fresh ↔ old (oldRep v) ≠ 1 ∧ role (rep v) = 1)
    (time : t.rr 15 = s.rr 15)
    (stored : ∀ i < k*k, MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i =
      insertSlackCandidates (expansionPairOffers rep role cost effective (s.rr 15) fresh i)
        (readMatchingPairBucket (k := k) s i)) : MatchingSearchOuterBuckets t rep role cost effective := by
  let datum := normalizedOuterEdge cost effective (s.rr 15)
  let offers (a b : Fin k) := expansionPairOffers rep role cost effective (s.rr 15) fresh (k*a.val+b.val)
  have mem := expansionPairOffers_mem rep role cost effective (s.rr 15) fresh
  refine ⟨fun i hi => (stored i hi).1, ?_, ?_⟩
  · intro a b separate left right
    let baseline := if old (oldRep a) = 1 ∧ old (oldRep b) = 1 then
      normalizedOuterPairEntries oldRep cost effective (s.rr 15) a b else []
    have prior : LeastSlackEntry baseline (readMatchingPairBucket (k := k) s (k*a.val+b.val)) := by
      by_cases both : old (oldRep a) = 1 ∧ old (oldRep b) = 1
      · have aOld : oldRep a = a := (stays a both.1).1.symm.trans (fixed a left)
        have bOld : oldRep b = b := (stays b both.2).1.symm.trans (fixed b right)
        simpa only [baseline, if_pos both] using cached.least a b separate (aOld ▸ both.1) (bOld ▸ both.2)
      · have empty := cached.inactive a b (not_and_or.mp both)
        simp only [baseline, if_neg both, empty]
        constructor <;> simp
    have least := prior.insert_many (offers a b)
    have priorFits (d : DualSlack (MatchingDualEvent k)) (h : d ∈ baseline) :
        d ∈ normalizedOuterPairEntries rep cost effective (s.rr 15) a b := by
      by_cases both : old (oldRep a) = 1 ∧ old (oldRep b) = 1
      · simp only [baseline, if_pos both, normalizedOuterPairEntries_mem] at h
        obtain ⟨u,v,hu,hv,value⟩ := h
        have aOld := (stays a both.1).1.symm.trans (fixed a left)
        have bOld := (stays b both.2).1.symm.trans (fixed b right)
        have uOn : old (oldRep u) = 1 := by rw [hu, ← aOld]; exact both.1
        have vOn : old (oldRep v) = 1 := by rw [hv, ← bOld]; exact both.2
        exact normalizedOuterPairEntries_mem.mpr ⟨u,v,(stays u uOn).1.trans hu,(stays v vOn).1.trans hv,value⟩
      · simp [baseline, both] at h
    have exactEntries (d : DualSlack (MatchingDualEvent k)) :
        d ∈ (offers a b).reverse ++ baseline ↔ d ∈ normalizedOuterPairEntries rep cost effective (s.rr 15) a b := by
      rw [List.mem_append, List.mem_reverse]
      constructor
      · rintro (offered | oldEntry)
        · obtain ⟨u,_,v,_,⟨_,coords⟩,value⟩ := (mem a b d).mp offered
          rcases coords with ⟨ha,hb⟩ | ⟨ha,hb⟩
          · exact normalizedOuterPairEntries_mem.mpr ⟨u,v,ha.symm,hb.symm,value⟩
          · exact normalizedOuterPairEntries_mem.mpr ⟨v,u,ha.symm,hb.symm,(normalizedOuterEdge_swap symmetric effective _ v u).trans value⟩
        · exact priorFits d oldEntry
      · intro present
        obtain ⟨u,v,hu,hv,value⟩ := normalizedOuterPairEntries_mem.mp present
        have uNow : role (rep u) = 1 := hu.symm ▸ left
        have vNow : role (rep v) = 1 := hv.symm ▸ right
        by_cases uOld : old (oldRep u) = 1
        · by_cases vOld : old (oldRep v) = 1
          · have ou : oldRep u = a := (stays u uOld).1.symm.trans hu
            have ov : oldRep v = b := (stays v vOld).1.symm.trans hv
            have both : old (oldRep a) = 1 ∧ old (oldRep b) = 1 := by
              rw [← ou, ← ov, oldIdem, oldIdem]
              exact ⟨uOld,vOld⟩
            exact Or.inr (by simp only [baseline, if_pos both, normalizedOuterPairEntries_mem]; exact ⟨u,v,ou,ov,value⟩)
          · exact Or.inl ((mem a b d).mpr ⟨v,(membership v).mpr ⟨vOld,vNow⟩,u,
              by rw [hu,hv]; exact separate.symm, ⟨uNow, Or.inr ⟨hu.symm,hv.symm⟩⟩,
              (normalizedOuterEdge_swap symmetric effective _ v u).trans value⟩)
        · exact Or.inl ((mem a b d).mpr ⟨u,(membership u).mpr ⟨uOld,uNow⟩,v,
            by rwa [hu,hv], ⟨vNow, Or.inl ⟨hu.symm,hv.symm⟩⟩, value⟩)
    rw [time, (stored _ (matchingPairSlot_lt a b)).2]
    exact ⟨fun chosen => (exactEntries _).mp (least.sound chosen), fun d h => least.covers d ((exactEntries d).mpr h)⟩
  · intro a b off
    have oldOff := off.imp (fun h on => h (stays a on).2) (fun h on => h (stays b on).2)
    have noOffers : offers a b = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro d given
      obtain ⟨u,hu,v,_,⟨on,coords⟩,_⟩ := (mem a b d).mp given
      have uOn := ((membership u).mp hu).2
      rcases coords with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [idem, uOn, on] at off
    rw [(stored _ (matchingPairSlot_lt a b)).2, cached.inactive a b oldOff]
    change insertSlackCandidates (offers a b) none = none
    rw [noOffers]; rfl

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionPairMeaning

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

/-! matching/MatchingExpansionCacheRestore.lean -/
section RppSource_MatchingExpansionCacheRestore
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 8192

/-- All four cache passes and the selector reset at the actual expansion
exit. Each grouped row and each normalized bucket reports the ordered offers
inserted into its own seed. -/
theorem restoreExpansionCacheBlock_tables {k : ℕ} {s : ArithmeticState} {rep : Fin k → Fin k} {role : Fin k → ℕ}
    {cost : Fin k → Fin k → ℝ} {eff : Fin k → ℝ} (cutAt : Fin k → Finset (Fin k))
    (entry : s.pc = 0) (running : s.halted = false) (work : ExpansionCacheFrame s)
    (input : MatchingRefreshInput s rep role cost eff) (above : s.nr 65+2*(k*k) ≤ s.nr 88)
    (nodeBefore : s.nr 74+k ≤ s.nr 88) (space : ExpansionCutReadLayout k s)
    (rows : ∀ i < s.nr 61, MatchingCandidateRowValid cutAt s i) (pairs : ∀ i < k*k, MatchingPairBucketValid k s i) :
    let fresh := matchingExpansionFreshSources k s
    ∃ t ticks, BlockRuns restoreExpansionCacheBlock ticks s t ∧ t.halted = false ∧
      ticks ≤ 63*k+(98*k+9)*fresh.length+14 ∧ ExpansionCacheRestored s t ∧
      MatchingRefreshInput t rep role cost eff ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i) ∧
      (∀ g : MatchingCandidateGroup k, readMatchingCandidate cutAt t g.slot =
        insertSlackCandidates (expansionRowOffers rep role cost eff fresh g.slot) (expansionGroupSeed cutAt s g)) ∧
      ∀ i < k*k, MatchingPairBucketValid k t i ∧ readMatchingPairBucket (k := k) t i =
        insertSlackCandidates (expansionPairOffers rep role cost eff (s.rr 15) fresh i) (readMatchingPairBucket (k := k) s i) := by
  intro fresh
  obtain ⟨a,b,c,ac,bc,cc,ar,al,br,bl,cr,cl,costPrefix,len,words,cInput,cRows,cSeeds,cPairs,cFixed,cTime⟩ :=
    matchingExpansionCachePrefix cutAt entry running work input above nodeBefore space rows
  let c0 := {c with pc := 0}
  have ck (r : ℕ) (h : r ∉ [0,6,7,10,11,15,16,18,19,28,99] := by decide) : c0.nr r = s.nr r := cFixed r h
  have c0Input := cInput.keeps (t := c0) ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
  obtain ⟨d,dc,dcost,dr,dl,dTime,dInput,_,dRows,dPairs⟩ := refreshExpansionOuterOriginals_rows (s := c0)
    cutAt rfl cl ((ck 9).trans work.one) ((ck 14).trans work.zero) c0Input fresh len words
    (by rwa [ck 65,ck 88]) (fun i hi => cRows i (ck 61 ▸ hi))
    (fun i hi => (cPairs i hi).1.symm ▸ pairs i hi)
  let d0 := {d with pc := 0}
  have dk (r : ℕ) (h : r ∉ [0,6,10,11,15,16,17,18,19,24,25,26] := by decide) : d0.nr r = c0.nr r := by
    change d.nr r = _
    rw [← dr.run]
    exact arithmeticRun_keeps_from_destination_list _ (by decide) h c0 dc
  obtain ⟨last,reset,live,nat,real,_,_,_,_,_⟩ :=
    resetMatchingSelector_spec d0 rfl dl ((dk 14).trans ((ck 14).trans work.zero))
  have tables (r : ℕ) (h : r ∈ matchingRefreshTableRegisters) : last.nr r = d0.nr r := by
    rw [← reset.run]
    exact arithmeticRun_keeps_from_destination_list [0,1,3,4,5,8] (by decide)
      (by simp [matchingRefreshTableRegisters] at h; simp; omega) d0 5
  obtain ⟨finalRows,finalPairs⟩ := matchingCacheReads_unchanged cutAt nat real tables
  have lastInput := dInput.keeps (t := last) ⟨fun _ _ => congrFun nat _, fun _ _ _ _ => congrFun real _⟩ tables
  let ticks := ac+(bc+(cc+(dc+5)))
  let final := relocateState collectExpansionOuterOriginals.length
    (relocateState restoreExpansionIncomingRates.length (relocateState restoreExpansionCuts.length
      (relocateState refreshExpansionOuterOriginals.length last)))
  have full : BlockRuns restoreExpansionCacheBlock ticks s final := ar.append (br.append (cr.append (dr.append reset)))
  obtain ⟨other,_,observed,_,_,restored⟩ := restoreExpansionCacheBlock_spec entry running work
  have eq := (observed.same_exit full).2
  subst other
  refine ⟨final,ticks,full,live,?_,restored,?_,?_,?_,?_⟩
  · have permute := Nat.mul_comm fresh.length (98*k+9)
    change dc ≤ fresh.length*(98*k+9)+2 at dcost
    dsimp only [ticks]
    omega
  · exact lastInput.keeps (t := final) ⟨fun _ _ => rfl,fun _ _ _ _ => rfl⟩ (fun _ _ => rfl)
  · intro i hi
    exact (finalRows i).1.symm ▸ (dRows i ((ck 61).symm ▸ hi)).1
  · intro g
    have within : g.slot < c0.nr 61 := by rw [ck 61,input.layout.rows]; exact g.slot_lt
    exact (finalRows g.slot).2.trans ((dRows g.slot within).2.trans
      (congrArg (insertSlackCandidates (expansionRowOffers rep role cost eff fresh g.slot)) (cSeeds g)))
  · intro i hi
    obtain ⟨valid,result⟩ := dPairs i hi
    refine ⟨(finalPairs i).1.symm ▸ valid, (finalPairs i).2.trans ?_⟩
    change readMatchingPairBucket (k := k) d i = _
    rw [result]
    change insertSlackCandidates (expansionPairOffers rep role cost eff (c.rr 15) fresh i) _ = _
    rw [cTime]
    exact congrArg (insertSlackCandidates (expansionPairOffers rep role cost eff (s.rr 15) fresh i)) (cPairs i hi).2

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionCacheRestore

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

/-! matching/MatchingExpansionRowMeaning.lean -/
section RppSource_MatchingExpansionRowMeaning
namespace VehicleRoutingSurvey.Routing

/-- For every selector range the values restored by a split form the exact
group minimum after the fresh-source sweep. -/
theorem MatchingExpansionChildPorts.rowMinimum {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state} {B : Finset (Fin k)}
    (registry : MatchingExpansionChildPorts state B) {forest : AlternatingForestState (Fin k)}
    {positive : 0 < k} {chosen s : ArithmeticState} (event : MatchingSelectedExpansion part forest positive chosen B)
    (zero : state.cutDual B = 0) (internal : state.InternalCuts)
    (external : ∀ p ∈ registry.ports, ∀ w, state.partialMate p = some w → w ∉ registry.block p)
    (children : List (Fin k)) (entry : ℕ) (ports : registry.ports = (event.base :: children).toFinset)
    (size : s.nr 55 = k) (encoding : AlternatingForestMemory (forest.expandBlossom event.parent event.base children entry) (s.nr 51) s.nm)
    (owners : ∀ v : Fin k, expansionChildOf s v.val = if v ∈ B then (registry.owner v).val else k)
    (symmetric : ∀ u v, cost u v = cost v u)
    (nested : ∀ C ∈ state.cuts, ∀ u ∈ C, ∀ v ∈ C, part.blocks.block u = part.blocks.block v)
    (descendants : ∀ C ∈ state.cuts.erase B, C ⊆ B → ∃ p ∈ registry.ports, C ⊆ registry.block p)
    (fresh : List (Fin k)) (freshSpec : ∀ v : Fin k, v ∈ fresh ↔ expansionOriginalHasRole s 1 v.val)
    (group : MatchingCandidateGroup k) (cached : Option (DualSlack (MatchingDualEvent k)))
    (before : LeastSlackEntry ((matchingSearchSlacks part forest positive).filter fun d =>
      @decide _ (Classical.propDecidable (group.admits part.blocks forest (part.representativeOf positive) d))) cached) :
    let opened := part.openZeroCut event.top event.present zero (registry.toExpansionChildren internal external)
    let after := forest.expandBlossom event.parent event.base children entry
    let role := fun v => alternatingRoleCode (after.role v)
    let eff := effectiveVertexPotential state.cuts state.potential state.cutDual
    let seed := match group with
      | .outer _ => cached
      | .incoming v => matchingExpansionIncomingSeed s v cached
      | .cut v => matchingCutGroupEntry opened after v
    LeastSlackEntry ((matchingSearchSlacks opened after positive).filter fun d =>
      @decide _ (Classical.propDecidable (group.admits opened.blocks after (opened.representativeOf positive) d)))
      (insertSlackCandidates (expansionRowOffers opened.representative role cost eff fresh group.slot) seed) := by
  intro opened after role eff seed
  let next := state.eraseZeroCut event.present zero
  have stable : effectiveVertexPotential next.cuts next.potential next.cutDual =
      effectiveVertexPotential state.cuts state.potential state.cutDual :=
    funext (effectiveVertexPotential_erase_zero _ event.present _ _ zero)
  have within := registry.nestedAfter event.top event.present zero internal external nested descendants
  have labels := registry.outerOriginals event.top event.present zero internal external children entry event.block
    event.active event.inner ports size encoding owners
  have freshIff (v : Fin k) := (freshSpec v).trans (labels.2 v)
  cases group with
  | outer p =>
    apply expansionOuterRow_least (oldRep := part.representative) (old := fun v => alternatingRoleCode (forest.role v))
      (rep := opened.representative) (role := role) symmetric labels.1 fresh freshIff p before
      (matchingSearchOuterGroup_mem_iff part forest positive symmetric nested p)
    intro d
    rw [← stable]
    exact matchingSearchOuterGroup_mem_iff opened after positive symmetric within p d
  | incoming v =>
    let old := alternatingRoleCode (forest.role (part.representative v))
    let new := role (opened.representative v)
    have atOwner (r : ℕ) : expansionOriginalHasRole s r v.val ↔ v ∈ B ∧ new = r := by
      by_cases h : v ∈ B
      · have rep : opened.representative v = registry.owner v := by
          change (if v ∈ B then registry.owner v else part.representative v) = registry.owner v
          rw [if_pos h]
        simp only [expansionOriginalHasRole,owners,if_true,size,(registry.owner v).isLt,true_and,expansionRepRole,
          (encoding (registry.owner v)).1,h,new,role,after,rep]
      · simp [expansionOriginalHasRole,owners,h,size]
    have prior (h : v ∈ B) : old = 2 := by
      have eq := (part.same_block.mpr (((part.block_eq_iff_member event.top v).mpr h).trans event.block.symm)).trans event.active
      simp only [old,eq,event.inner,alternatingRoleCode]
    have same (h : v ∉ B) : new = old := congrArg alternatingRoleCode
      (registry.keepsOutsideRoles event.top event.present zero internal external forest event.parent event.base children entry ports v h).2
    have oldGroup := matchingSearchIncomingGroup_mem_iff part forest positive symmetric nested v
    have value := matchingExpansionIncomingSeed_eq cached (v ∈ B) atOwner prior same (fun d hd => by
      obtain ⟨_,_,_,off,raw⟩ := (oldGroup d).mp (before.sound hd)
      exact ⟨off,congrArg DualSlack.rate raw.symm⟩)
    change LeastSlackEntry _ (insertSlackCandidates (expansionRowOffers _ _ _ _ fresh (k+v.val)) (matchingExpansionIncomingSeed s v cached))
    rw [value]
    apply expansionIncomingRow_least (oldRep := part.representative) (old := fun v => alternatingRoleCode (forest.role v))
      (rep := opened.representative) (role := role) (fun w on => (labels.1 w on).2) fresh freshIff v before oldGroup
    intro d
    rw [← stable]
    exact matchingSearchIncomingGroup_mem_iff opened after positive symmetric within v d
  | cut p =>
    change LeastSlackEntry _ (insertSlackCandidates (expansionRowOffers _ _ _ _ fresh (2*k+p.val)) (matchingCutGroupEntry opened after p))
    rw [expansionCutOffers_empty]
    exact matchingCutGroupEntry_least opened after positive p

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionRowMeaning

/-! matching/MatchingExpansionSearchRows.lean -/
section RppSource_MatchingExpansionSearchRows
namespace VehicleRoutingSurvey.Routing

/-- The real cache repair restores the selector and every normalized
outer-pair minimum for the opened partition and its relabelled forest. -/
theorem MatchingExpansionChildPorts.searchRows {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state} {B : Finset (Fin k)}
    (ports : MatchingExpansionChildPorts state B) {forest : AlternatingForestState (Fin k)}
    {positive : 0 < k} {chosen s : ArithmeticState} (event : MatchingSelectedExpansion part forest positive chosen B)
    (zero : state.cutDual B = 0) (internal : state.InternalCuts)
    (external : ∀ p ∈ ports.ports, ∀ w, state.partialMate p = some w → w ∉ ports.block p)
    (children : List (Fin k)) (entry : ℕ) (cycle : ports.ports = (event.base :: children).toFinset)
    (oldLinks : ∀ v, part.representative v ≠ v → forest.role v = .unlabelled)
    (owners : ∀ v : Fin k, expansionChildOf s v.val = if v ∈ B then (ports.owner v).val else k)
    (symmetric : ∀ u v, cost u v = cost v u)
    (nested : ∀ C ∈ state.cuts, ∀ u ∈ C, ∀ v ∈ C, part.blocks.block u = part.blocks.block v)
    (descend : ∀ C ∈ state.cuts.erase B, C ⊆ B → ∃ p ∈ ports.ports, C ⊆ ports.block p)
    (pc : s.pc = 0) (running : s.halted = false) (work : ExpansionCacheFrame s)
    (above : s.nr 65+2*(k*k) ≤ s.nr 88) (nodeBefore : s.nr 74+k ≤ s.nr 88) (space : ExpansionCutReadLayout k s)
    (priorValid : ∀ i < s.nr 61, MatchingCandidateRowValid (matchingTopCutAt part) s i)
    (prior : ∀ group : MatchingCandidateGroup k, LeastSlackEntry ((matchingSearchSlacks part forest positive).filter fun d =>
      @decide _ (Classical.propDecidable (group.admits part.blocks forest (part.representativeOf positive) d)))
      (readMatchingCandidate (matchingTopCutAt part) s group.slot))
    (priorPairs : MatchingSearchOuterBuckets s part.representative (fun v => alternatingRoleCode (forest.role v)) cost
      (effectiveVertexPotential state.cuts state.potential state.cutDual)) :
    let next := state.eraseZeroCut event.present zero
    let opened := part.openZeroCut event.top event.present zero (ports.toExpansionChildren internal external)
    let after := forest.expandBlossom event.parent event.base children entry
    let role := fun v => alternatingRoleCode (after.role v)
    let eff := effectiveVertexPotential next.cuts next.potential next.cutDual
    ∀ (dual : MatchingSearchDualMemory opened after s) (input : MatchingRefreshInput s opened.representative role cost eff),
      ∃ t ticks, BlockRuns restoreExpansionCacheBlock ticks s t ∧ t.halted = false ∧
        ticks ≤ 63*k+(98*k+9)*(matchingExpansionFreshSources k s).length+14 ∧ ExpansionCacheRestored s t ∧
        MatchingSearchRows opened after positive (matchingTopCutAt opened) t ∧
        MatchingSearchOuterBuckets t opened.representative role cost eff ∧ MatchingRefreshInput t opened.representative role cost eff := by
  intro next opened after role eff dual input
  let oldCut := matchingTopCutAt part
  let newCut := matchingTopCutAt opened
  let beforeEff := effectiveVertexPotential state.cuts state.potential state.cutDual
  let fresh := matchingExpansionFreshSources k s
  have sameEff : eff = beforeEff := funext (effectiveVertexPotential_erase_zero _ event.present _ _ zero)
  obtain ⟨t,ticks,run,live,budget,restored,reads,valid,raw,pairs⟩ :=
    restoreExpansionCacheBlock_tables newCut pc running work input above nodeBefore space
      (fun i h => MatchingCandidateRowValid.changeCutMap oldCut newCut (priorValid i h)) priorPairs.valid
  have size := dual.dimension
  have labels := ports.outerOriginals event.top event.present zero internal external children entry event.block
    event.active event.inner cycle size dual.roles owners
  have freshIff (v : Fin k) := (matchingExpansionFreshSources_mem (s := s) v).trans (labels.2 v)
  have keep (r : ℕ) (hr : 50 ≤ r := by decide) (away : r ≠ 99 := by decide) := restored.fixed r hr away
  have search : MatchingSearchRows opened after positive newCut t := by
    refine ⟨reads.layout,restored.rows.trans (keep 61).symm,restored.identifiers.trans (keep 58).symm,
      restored.slacks.trans (keep 59).symm,restored.rates.trans (keep 60).symm,?_,?_⟩
    · intro i hi; exact valid i (keep 61 ▸ hi)
    · intro g
      rw [raw g,sameEff]
      have minimum := ports.rowMinimum event zero internal external children entry cycle size dual.roles owners
        symmetric nested descend fresh (matchingExpansionFreshSources_mem (s := s)) g
        (readMatchingCandidate oldCut s g.slot) (prior g)
      cases g with
      | outer v =>
        have eq := matchingCandidate_changeCutMap_of_edgeGroup oldCut newCut (.outer v) (fun _ h => by cases h) (prior (.outer v))
        change readMatchingCandidate newCut s v.val = readMatchingCandidate oldCut s v.val at eq
        simpa only [expansionGroupSeed,MatchingCandidateGroup.slot,eq] using minimum
      | incoming v =>
        have eq := matchingCandidate_changeCutMap_of_edgeGroup oldCut newCut (.incoming v) (fun _ h => by cases h) (prior (.incoming v))
        change readMatchingCandidate newCut s (k+v.val) = readMatchingCandidate oldCut s (k+v.val) at eq
        simpa only [expansionGroupSeed,MatchingCandidateGroup.slot,eq] using minimum
      | cut v =>
        have seed := ports.cutSeed event.top event.present zero internal external children entry cycle event.active
          event.block (positive := positive) owners v (matchingCutGroupEntry_of_least (prior (.cut v))) dual
        change LeastSlackEntry _ (insertSlackCandidates _ (if expansionChildOf s v.val = v.val then
          expansionCutRowValue newCut s v else readMatchingCandidate newCut s (2*k+v.val)))
        rw [seed]
        exact minimum
  have inactive := ports.inactiveAfter event.top event.present zero internal external (source := event.parent)
    children entry event.active event.block cycle oldLinks
  have active (p : Fin k) (on : role p = 1) : opened.representative p = p := by
    by_contra hidden
    have dormant := inactive p hidden
    change alternatingRoleCode (after.role p) = 1 at on
    rw [dormant] at on
    exact (by decide : (0 : ℕ) ≠ 1) on
  have oldPairs : MatchingSearchOuterBuckets s part.representative (fun v => alternatingRoleCode (forest.role v)) cost eff :=
    sameEff.symm ▸ priorPairs
  exact ⟨t,ticks,run,live,budget,restored,search,
    oldPairs.expand symmetric part.representative_idem opened.representative_idem active labels.1 fresh freshIff restored.time pairs,reads⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionSearchRows

open VehicleRoutingSurvey.Routing SupplyChainTheory in
theorem solution : (fun {P : Prop} (_ : P) => P) (@VehicleRoutingSurvey.Routing.MatchingExpansionChildPorts.searchRows) :=
  @VehicleRoutingSurvey.Routing.MatchingExpansionChildPorts.searchRows
