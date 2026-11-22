-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.MatchingChosenStage.contractionDualSnapshot
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T16:16:29.764621+00:00
-- url     : https://prove2.me/submissions/e95469c8-456b-4014-8d52-516ee037cc9c

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_ContractionArm

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









































end VehicleRoutingSurvey.Routing
end RppSource_WeightedReadDeltaRAM

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

open VehicleRoutingSurvey.Routing SupplyChainTheory in
theorem solution : (fun {P : Prop} (_ : P) => P) (@VehicleRoutingSurvey.Routing.MatchingChosenStage.contractionDualSnapshot) :=
  @VehicleRoutingSurvey.Routing.MatchingChosenStage.contractionDualSnapshot
