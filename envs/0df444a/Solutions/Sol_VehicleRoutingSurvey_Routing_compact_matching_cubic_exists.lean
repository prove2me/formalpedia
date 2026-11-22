-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.compact_matching_cubic_exists
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T16:08:26.848708+00:00
-- url     : https://prove2.me/submissions/0489e098-845e-4c2d-8329-a2b89c47bffa

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces
import Theorems.Thm_VehicleRoutingSurvey_Routing_MatchingDispatchState_augment
import Theorems.Thm_VehicleRoutingSurvey_Routing_MatchingDispatchState_contract
import Theorems.Thm_VehicleRoutingSurvey_Routing_MatchingDispatchState_expand
import Theorems.Thm_VehicleRoutingSurvey_Routing_MatchingDispatchState_grow
import Theorems.Thm_VehicleRoutingSurvey_Routing_MatchingBetweenStages_prepare
import Theorems.Thm_VehicleRoutingSurvey_Routing_weightedBlossomMatchingBlock_spec_at_entry
import Batteries.Tactic.OpenPrivate

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





private noncomputable def DualSlack.limit {Event : Type*} (constraint : DualSlack Event) :
    Option (DualBound Event) :=
  if 0 < constraint.rate then some ⟨constraint.event, constraint.slack / constraint.rate⟩
  else none

/-- Scan the positive-rate constraints for the first event reached along the direction. -/
noncomputable def nextDualBound {Event : Type*} (slacks : List (DualSlack Event)) :
    Option (DualBound Event) :=
  (slacks.filterMap DualSlack.limit).minOn? DualBound.amount



/-- If no event bounds the step, every constraint has nonincreasing demand. -/
theorem nextDualBound_eq_none {Event : Type*} (slacks : List (DualSlack Event)) :
    nextDualBound slacks = none ↔ ∀ c ∈ slacks, c.rate ≤ 0 := by
  have minNone : (slacks.filterMap DualSlack.limit).minOn? DualBound.amount = none ↔
      slacks.filterMap DualSlack.limit = [] := by
    cases slacks.filterMap DualSlack.limit <;> simp [List.minOn?_cons_eq_some_minOn]
  rw [nextDualBound, minNone, List.filterMap_eq_nil_iff]
  constructor
  · intro noEvent c hc
    have none := noEvent c hc
    by_contra bad
    simp [DualSlack.limit, lt_of_not_ge bad] at none
  · intro noIncrease c hc
    simp [DualSlack.limit, not_lt_of_ge (noIncrease c hc)]









theorem oddCutDualEdgeValue_shift {n : ℕ} (cuts : Finset (Finset (Fin n)))
    (potential direction : Fin n → ℝ) (cutDual cutDirection : Finset (Fin n) → ℝ)
    (δ : ℝ) (e : Sym2 (Fin n)) :
    oddCutDualEdgeValue cuts (fun v => potential v + δ * direction v)
      (fun S => cutDual S + δ * cutDirection S) e =
    oddCutDualEdgeValue cuts potential cutDual e + δ * oddCutDualEdgeValue cuts direction cutDirection e := by
  simp only [oddCutDualEdgeValue, Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
  abel

theorem matchingDualSlacks_nonnegative {n : ℕ} {c : Fin n → Fin n → ℝ}
    {edges : List (Sym2 (Fin n))} {cuts : Finset (Finset (Fin n))}
    {potential direction : Fin n → ℝ} {cutDual cutDirection : Finset (Fin n) → ℝ}
    (feasible : ∀ e ∈ edges, oddCutDualEdgeValue cuts potential cutDual e ≤ edgeCost c e)
    (nonnegative : ∀ S ∈ cuts, 0 ≤ cutDual S) :
    ∀ d ∈ matchingDualSlacks c edges cuts potential direction cutDual cutDirection, 0 ≤ d.slack := by
  intro d hd
  simp only [matchingDualSlacks, List.mem_append, List.mem_map, Finset.mem_toList] at hd
  rcases hd with ⟨e, he, rfl⟩ | ⟨S, hS, rfl⟩
  · exact sub_nonneg.mpr (feasible e he)
  · exact nonnegative S hS



/-- Translate the selected slack constraint into an edge or blossom event and certify the
updated dual variables. The selection can come from a full scan or a checked cache. -/
theorem matchingDualAdjustment_of_slacks {n : ℕ} {c : Fin n → Fin n → ℝ}
    {edges : List (Sym2 (Fin n))} {cuts : Finset (Finset (Fin n))}
    {potential direction : Fin n → ℝ} {cutDual cutDirection : Finset (Fin n) → ℝ}
    {bound : DualBound (MatchingDualEvent n)}
    (chosen : let slacks := matchingDualSlacks c edges cuts potential direction cutDual cutDirection
      0 ≤ bound.amount ∧
        (∃ d ∈ slacks, d.event = bound.event ∧ 0 < d.rate ∧ bound.amount * d.rate = d.slack) ∧
        ∀ d ∈ slacks, bound.amount * d.rate ≤ d.slack) :
    MatchingDualAdjustment c edges cuts potential direction cutDual cutDirection bound := by
  dsimp only [MatchingDualAdjustment]
  obtain ⟨stepNonneg, ⟨d, hd, sameEvent, positive, hit⟩, safe⟩ := chosen
  refine ⟨stepNonneg, ?_, ?_, ?_⟩
  · intro e he
    have member : matchingEdgeSlack c cuts potential direction cutDual cutDirection e ∈
        matchingDualSlacks c edges cuts potential direction cutDual cutDirection :=
      List.mem_append_left _ (List.mem_map_of_mem he)
    have stays := safe _ member
    dsimp only [matchingEdgeSlack] at stays
    rw [oddCutDualEdgeValue_shift]
    linarith only [stays]
  · intro S hS
    have member : matchingCutSlack cutDual cutDirection S ∈
        matchingDualSlacks c edges cuts potential direction cutDual cutDirection :=
      List.mem_append_right _ (List.mem_map_of_mem (Finset.mem_toList.mpr hS))
    have stays := safe _ member
    dsimp only [matchingCutSlack] at stays
    rw [mul_neg] at stays
    linarith only [stays]
  · rw [← sameEvent]
    simp only [matchingDualSlacks, List.mem_append, List.mem_map, Finset.mem_toList] at hd
    rcases hd with ⟨e, he, rfl⟩ | ⟨S, hS, rfl⟩
    · refine ⟨he, positive, ?_⟩
      dsimp only [matchingEdgeSlack] at hit
      rw [oddCutDualEdgeValue_shift]
      linarith only [hit]
    · refine ⟨hS, neg_pos.mp positive, ?_⟩
      dsimp only [matchingCutSlack] at hit
      rw [mul_neg] at hit
      linarith only [hit]



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

/-- An incomplete matching on an even vertex set leaves at least two exposed vertices. -/
theorem two_exposed_vertices {n : ℕ} {O covered : Finset (Fin n)}
    {M : Finset (Sym2 (Fin n))} (matched : IsPerfectMatchingOn covered M)
    (subset : covered ⊆ O) (even : Even O.card) (incomplete : covered ≠ O) :
    ∃ u v, u ∈ O \ covered ∧ v ∈ O \ covered ∧ u ≠ v := by
  apply Finset.one_lt_card_iff.mp
  rw [Finset.card_sdiff_of_subset subset, perfectMatching_card_twice matched]
  have smaller : covered.card < O.card := by
    by_contra bad
    exact incomplete (Finset.eq_of_subset_of_card_le subset (le_of_not_gt bad))
  rw [perfectMatching_card_twice matched] at smaller
  obtain ⟨half, cardEven⟩ := even
  omega

/-- The search on a complete graph cannot run out of dual events while exposed roots
exist. The edge between two roots in distinct outer blocks has positive slope. -/
theorem matchingDualBound_exists_of_incomplete {n : ℕ} {O covered : Finset (Fin n)}
    {M : Finset (Sym2 (Fin n))} (matched : IsPerfectMatchingOn covered M)
    (subset : covered ⊆ O) (even : Even O.card) (incomplete : covered ≠ O)
    (c : Fin n → Fin n → ℝ) (edges : List (Sym2 (Fin n)))
    (complete : ∀ u ∈ O, ∀ v ∈ O, u ≠ v → s(u, v) ∈ edges)
    (cuts : Finset (Finset (Fin n))) (blocks : TopLevelMatchingBlocks O cuts)
    (label : Finset (Fin n) → ℝ) (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ)
    (rootOuter : ∀ v ∈ O \ covered, label (blocks.block v) = 1)
    (blockBase : ∀ S ∈ O.image blocks.block,
      ∃ base, ∀ v ∈ S, v ≠ base → v ∈ covered) :
    ∃ bound, nextDualBound (matchingDualSlacks c edges cuts potential
      (forestVertexDirection blocks label) cutDual (forestCutDirection blocks label)) = some bound := by
  obtain ⟨u, v, hu, hv, distinct⟩ := two_exposed_vertices matched subset even incomplete
  obtain ⟨uIn, uFree⟩ := Finset.mem_sdiff.mp hu
  obtain ⟨vIn, vFree⟩ := Finset.mem_sdiff.mp hv
  have separate : blocks.block u ≠ blocks.block v := by
    intro equal
    obtain ⟨base, coveredAway⟩ := blockBase (blocks.block v) (Finset.mem_image_of_mem _ vIn)
    have uIsBase : u = base := by
      by_contra different
      exact uFree (coveredAway u (equal ▸ blocks.self_mem u uIn) different)
    have vIsBase : v = base := by
      by_contra different
      exact vFree (coveredAway v (blocks.self_mem v vIn) different)
    exact distinct (uIsBase.trans vIsBase.symm)
  let direction := forestVertexDirection blocks label
  let cutDirection := forestCutDirection blocks label
  let slacks := matchingDualSlacks c edges cuts potential direction cutDual cutDirection
  let edge := s(u, v)
  let constraint : DualSlack (MatchingDualEvent n) :=
    ⟨.edge edge, edgeCost c edge - oddCutDualEdgeValue cuts potential cutDual edge,
      oddCutDualEdgeValue cuts direction cutDirection edge⟩
  have member : constraint ∈ slacks := by
    dsimp only [slacks, matchingDualSlacks]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨edge, complete u uIn v vIn distinct, rfl⟩)
  have rising : 0 < constraint.rate := by
    dsimp only [constraint, edge, direction, cutDirection]
    rw [forest_edge_slope blocks label uIn vIn distinct, if_neg separate, rootOuter u hu, rootOuter v hv]
    norm_num
  change ∃ bound, nextDualBound slacks = some bound
  cases found : nextDualBound slacks with
  | none => exact ((not_le_of_gt rising) ((nextDualBound_eq_none slacks).mp found constraint member)).elim
  | some bound => exact ⟨bound, rfl⟩

end VehicleRoutingSurvey.Routing
end RppSource_WeightedRootEvent

/-! matching/MatchingTerminalState.lean -/
section RppSource_MatchingTerminalState
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory







noncomputable def initialCompactMatchingPrimalDual {k : ℕ} (cost : Fin k → Fin k → ℝ)
    (nonnegative : ∀ u v, 0 ≤ cost u v) (symmetric : ∀ u v, cost u v = cost v u) :
    CompactMatchingPrimalDual k cost where
  covered := ∅
  edges := ∅
  perfect := by simp [IsPerfectMatchingOn]
  cuts := ∅
  potential := fun _ => 0
  cutDual := fun _ => 0
  cutValid := by simp
  feasible := by
    intro e legal
    induction e using Sym2.inductionOn with
    | hf u v =>
      have distinct : u ≠ v := fun same => legal (Sym2.mk_isDiag_iff.mpr same)
      rw [oddCutDualEdgeValue_mk _ _ _ distinct, edgeCost_eq_of_symmetric cost symmetric]
      simpa using nonnegative u v
  tight := by simp
  internal := by simp

/-- After `k/2` augmentations the primal state covers all `k` originals.
The array already contains the total involution used by the publishing block. -/
theorem CompactMatchingPrimalDual.toTerminal {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {original result : ArithmeticState}
    (data : CompactMatchingPrimalDualMemory state original result)
    (even : k % 2 = 0) (size : state.edges.card = k / 2) :
    Nonempty (MatchingTerminalCertificate k cost original result) := by
  have counted := perfectMatching_card_twice state.perfect
  have coveredCard : state.covered.card = k := by omega
  have full : state.covered = (Finset.univ : Finset (Fin k)) := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa using coveredCard.ge
  let mate := mateOfMatching state.perfect
  have mates : ∀ v : Fin k, result.nm (result.nr 50 + v.val) = (mate v).val := by
    intro v
    have included : v ∈ state.covered := by simp [full]
    simpa only [if_pos included, mate] using data.mate v
  have isTable : MateTableOn Finset.univ mate := by
    rw [← full]
    exact mateOfMatching_valid state.perfect
  have exactEdges : mateEdgeSet Finset.univ mate = state.edges := by
    rw [← full]
    exact mateEdgeSet_mateOfMatching state.perfect
  refine ⟨⟨mate, state.cuts, state.potential, state.cutDual, data.dimension, data.oddMap,
    data.mateAbove, mates, isTable, data.saved, data.natural, data.real, state.cutValid, state.feasible, ?_, ?_⟩⟩
  · rw [exactEdges]
    exact state.tight
  · rw [exactEdges]
    exact state.internal


end VehicleRoutingSurvey.Routing
end RppSource_MatchingTerminalState

/-! matching/MatchingPartitionView.lean -/
section RppSource_MatchingPartitionView
namespace VehicleRoutingSurvey.Routing







theorem CompactMatchingPartition.blockBase {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    {S : Finset (Fin k)} (top : S ∈ Finset.univ.image part.blocks.block) :
    ∃ base ∈ S, ∀ v ∈ S, v ≠ base → v ∈ state.covered := by
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp top
  exact ⟨part.representative u, part.inside u, part.coveredAway u⟩





theorem CompactMatchingPartition.representativeOf_block {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (positive : 0 < k)
    (v : Fin k) : part.representativeOf positive (part.blocks.block v) = part.representative v := by
  have members : (part.blocks.block v).Nonempty := ⟨v, part.blocks.self_mem v (Finset.mem_univ v)⟩
  rw [CompactMatchingPartition.representativeOf, dif_pos members]
  exact part.constant _ _ (part.blocks.same_of_mem (Finset.mem_univ v) members.choose_spec)

noncomputable def initialCompactMatchingPartition {k : ℕ} (cost : Fin k → Fin k → ℝ)
    (nonnegative : ∀ u v, 0 ≤ cost u v) (symmetric : ∀ u v, cost u v = cost v u) :
    CompactMatchingPartition (initialCompactMatchingPrimalDual cost nonnegative symmetric) where
  blocks := ⟨fun v => {v}, by simp, by
    intro v w _ member
    simp only [Finset.mem_singleton] at member
    rw [member], by simp⟩
  representative := id
  inside := by simp
  constant := by simp
  coveredAway := by
    intro v w member different
    exact (different (Finset.mem_singleton.mp member)).elim


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













end VehicleRoutingSurvey.Routing
end RppSource_MatchingCacheWriteRAM

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

/-! matching/AlternatingStageRoots.lean -/
section RppSource_AlternatingStageRoots
namespace VehicleRoutingSurvey.Routing



/-- Start the next augmenting search with exactly the exposed active nodes as roots. -/
def resetAlternatingForest {α : Type*} [DecidableEq α] (active : Finset α) (mate : α → Option α) :
    AlternatingForestState α where
  role v := if v ∈ active ∧ mate v = none then .outer none else .unlabelled
  depth _ := 0







end VehicleRoutingSurvey.Routing
end RppSource_AlternatingStageRoots

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













theorem allocateMatchingForestWitnessArray_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (zero : s.nr 14 = 0) :
    ∃ t, BlockRuns allocateMatchingForestWitnessArray 3 s t ∧ t.halted = false ∧
      t.nr 90 = s.nr 68 ∧ t.nr 68 = s.nr 68 + 2 * s.nr 55 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
  let t := (arithmeticStep allocateMatchingForestWitnessArray)^[3] s
  have exit : t.pc = allocateMatchingForestWitnessArray.length ∧ t.halted = false := by
    simp [t, allocateMatchingForestWitnessArray, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl exit.2 exit.1, exit.2, ?_⟩
  simp [t, allocateMatchingForestWitnessArray, arithmeticStep, entry, running, zero, Function.iterate_succ_apply',
    Nat.two_mul, Nat.add_assoc]





























end VehicleRoutingSurvey.Routing
end RppSource_MatchingForestWitnessRAM

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

/-! matching/WeightedDualCache.lean -/
section RppSource_WeightedDualCache
namespace VehicleRoutingSurvey.Routing

/-- Keep actual constraints as representatives. A positive-rate constraint can be omitted only
when the cache has a constraint of the same rate and no more slack. -/
structure DualSlackCache {Event : Type*} (full cache : List (DualSlack Event)) : Prop where
  sound : ∀ {c}, c ∈ cache → c ∈ full
  covers : ∀ c ∈ full, 0 < c.rate →
    ∃ r ∈ cache, r.rate = c.rate ∧ r.slack ≤ c.slack









noncomputable def DualSlack.advance {Event : Type*} (δ : ℝ) (c : DualSlack Event) : DualSlack Event :=
  { c with slack := c.slack - δ * c.rate }







end VehicleRoutingSurvey.Routing
end RppSource_WeightedDualCache

/-! matching/MatchingCacheInsertion.lean -/
section RppSource_MatchingCacheInsertion
namespace VehicleRoutingSurvey.Routing











/-- The cached raw slack remains minimal during a uniform-rate dual shift. This also
applies to dormant incoming rows whose stored rate is zero. -/
theorem LeastSlackEntry.advance {Event : Type*} {full : List (DualSlack Event)}
    {cached : Option (DualSlack Event)} (before : LeastSlackEntry full cached)
    (uniform : ∀ x ∈ full, ∀ y ∈ full, x.rate = y.rate) (δ : ℝ) :
    LeastSlackEntry (full.map (DualSlack.advance δ)) (cached.map (DualSlack.advance δ)) where
  sound chosen := by
    cases cached with
    | none => simp at chosen
    | some old =>
      have value := Option.some.inj chosen
      rw [← value]
      exact List.mem_map_of_mem (before.sound rfl)
  covers x present := by
    obtain ⟨old, original, rfl⟩ := List.mem_map.mp present
    obtain ⟨prior, represented, least⟩ := before.covers old original
    have same := uniform prior (before.sound represented) old original
    have dominates : (prior.advance δ).slack ≤ (old.advance δ).slack := by
      simpa only [DualSlack.advance, same] using sub_le_sub_right least (δ * old.rate)
    exact ⟨prior.advance δ, congrArg (Option.map (DualSlack.advance δ)) represented, dominates⟩

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

/-! matching/WeightedDeltaPhaseRAM.lean -/
section RppSource_WeightedDeltaPhaseRAM
namespace VehicleRoutingSurvey.Routing







/-- The selector changes scratch registers and the slack array. The selected ID travels
in natural register 1, while the dual step travels in real register 1. -/
theorem selectAndAdvanceDualSlackBlock_keeps_registers {s t : ArithmeticState} {steps : ℕ}
    (run : BlockRuns selectAndAdvanceDualSlackBlock steps s t) :
    (∀ r, r ∉ [0, 1, 2, 6, 7, 10, 11] → t.nr r = s.nr r) ∧
    ∀ r, r ∉ [0, 1, 2, 3, 4] → t.rr r = s.rr r := by
  rw [← run.run]
  exact ⟨fun _ away => arithmeticRun_keeps_from_destination_list _ (by decide) away s steps,
    fun _ away => arithmeticRun_keeps_real_from_destination_list _ (by decide) away s steps⟩



end VehicleRoutingSurvey.Routing
end RppSource_WeightedDeltaPhaseRAM

/-! matching/MatchingEventMemory.lean -/
section RppSource_MatchingEventMemory
namespace VehicleRoutingSurvey.Routing





theorem decodeMatchingDictionaryEvent_record {k : ℕ} {cutAt : Fin k → Finset (Fin k)}
    {s : ArithmeticState} {event : MatchingDualEvent k}
    (decoded : decodeMatchingDictionaryEvent k cutAt s (s.nr 1) = some event) :
    s.nr 1 ≠ 0 ∧ MatchingEventRecord cutAt (matchingOriginalGrowthEvent s) event := by
  let address := s.nr 54 + ((s.nr 1 - 1) + (s.nr 1 - 1))
  let a := s.nm address
  let b := s.nm (address + 1)
  have live : s.nr 1 ≠ 0 := by
    intro empty
    simp [decodeMatchingDictionaryEvent, empty] at decoded
  refine ⟨live, ?_⟩
  by_cases first : a < k
  · by_cases second : b < k
    · have typed : MatchingDualEvent.edge s(⟨a, first⟩, ⟨b, second⟩) = event := by
        apply Option.some.inj
        simpa only [decodeMatchingDictionaryEvent, if_neg live, dif_pos first, dif_pos second,
          a, b, address] using decoded
      rw [← typed]
      exact ⟨⟨a, first⟩, ⟨b, second⟩, rfl, rfl⟩
    · by_cases atCut : b = k
      · have typed : MatchingDualEvent.cut (cutAt ⟨a, first⟩) = event := by
          apply Option.some.inj
          simpa only [decodeMatchingDictionaryEvent, if_neg live, dif_pos first, dif_neg second,
            if_pos atCut, a, b, address] using decoded
        rw [← typed]
        exact ⟨⟨a, first⟩, Prod.ext rfl atCut, rfl⟩
      · simp [decodeMatchingDictionaryEvent, live, first, second, atCut, a, b, address] at decoded
  · simp [decodeMatchingDictionaryEvent, live, first, a, address] at decoded

/-- Selection advances only the slacks. The winning dictionary bytes in the selected
machine state still encode the event proved safe against the original constraints. -/
theorem chosenMatchingEvent_record {k : ℕ} {cutAt : Fin k → Finset (Fin k)}
    {s chosen : ArithmeticState} {steps : ℕ} {event : MatchingDualEvent k}
    (run : BlockRuns selectAndAdvanceDualSlackBlock steps s chosen) (natural : chosen.nm = s.nm)
    (decoded : decodeMatchingDictionaryEvent k cutAt s (chosen.nr 1) = some event) :
    chosen.nr 1 ≠ 0 ∧ MatchingEventRecord cutAt (matchingOriginalGrowthEvent chosen) event := by
  have base := (selectAndAdvanceDualSlackBlock_keeps_registers run).1 54 (by decide)
  apply decodeMatchingDictionaryEvent_record (s := chosen)
  simpa only [decodeMatchingDictionaryEvent, base, natural] using decoded


end VehicleRoutingSurvey.Routing
end RppSource_MatchingEventMemory

/-! matching/WeightedDeltaTable.lean -/
section RppSource_WeightedDeltaTable
namespace VehicleRoutingSurvey.Routing

/-- Cached constraints occupy three arrays. Only the identifier is read for an empty row. -/
structure DualBoundTable {Event : Type*} (initial : ArithmeticState)
    (rows : List (Option (DualSlack Event))) (decode : ℕ → Option Event) : Prop where
  length : initial.nr 8 = rows.length
  entries : ∀ i (within : i < rows.length), match rows[i] with
    | none => dualBoundIdentifier initial i = 0
    | some constraint => dualBoundIdentifier initial i ≠ 0 ∧
        decode (dualBoundIdentifier initial i) = some constraint.event ∧
        initial.rm (initial.nr 4 + i) = constraint.slack ∧
        initial.rm (initial.nr 5 + i) = constraint.rate

private theorem DualBoundTable.row_of_present {Event : Type*} {initial : ArithmeticState}
    {rows : List (Option (DualSlack Event))} {decode : ℕ → Option Event}
    (table : DualBoundTable initial rows decode) {i : ℕ} (within : i < initial.nr 8)
    (present : dualBoundPresent initial i) :
    ∃ constraint ∈ rows.filterMap id,
      0 < constraint.rate ∧ dualBoundRatio initial i = constraint.slack / constraint.rate ∧
      decode (dualBoundIdentifier initial i) = some constraint.event := by
  have rowIndex : i < rows.length := table.length ▸ within
  have data := table.entries i rowIndex
  cases atRow : rows[i] with
  | none =>
    rw [atRow] at data
    exact (present.1 data).elim
  | some constraint =>
    rw [atRow] at data
    obtain ⟨_, event, slack, rate⟩ := data
    exact ⟨constraint, List.mem_filterMap.mpr
        ⟨some constraint, atRow ▸ List.getElem_mem rowIndex, rfl⟩,
      by simpa only [rate] using present.2,
      by simp only [dualBoundRatio, slack, rate], event⟩

private theorem DualBoundTable.present_of_row {Event : Type*} {initial : ArithmeticState}
    {rows : List (Option (DualSlack Event))} {decode : ℕ → Option Event}
    (table : DualBoundTable initial rows decode) {constraint : DualSlack Event}
    (member : constraint ∈ rows.filterMap id) (rising : 0 < constraint.rate) :
    ∃ i < initial.nr 8, dualBoundPresent initial i ∧ dualBoundRatio initial i = constraint.slack / constraint.rate := by
  obtain ⟨slot, inRows, holds⟩ := List.mem_filterMap.mp member
  change slot = some constraint at holds
  have found : some constraint ∈ rows := holds ▸ inRows
  obtain ⟨i, within, atRow⟩ := List.mem_iff_getElem.mp found
  have data := table.entries i within
  rw [atRow] at data
  obtain ⟨nonzero, _, slack, rate⟩ := data
  exact ⟨i, table.length.symm ▸ within, ⟨nonzero, rate.symm ▸ rising⟩,
    by simp only [dualBoundRatio, slack, rate]⟩

/-- The minimum returned by the RAM scan makes a real constraint tight and is safe for
the full system, including constraints represented by a cached minimum. -/
theorem dualBoundMinimum_safe {Event : Type*} {initial result : ArithmeticState}
    {rows : List (Option (DualSlack Event))} {decode : ℕ → Option Event} {full : List (DualSlack Event)}
    (table : DualBoundTable initial rows decode) (cache : DualSlackCache full (rows.filterMap id))
    (initially : ∀ c ∈ full, 0 ≤ c.slack) (computed : DualBoundMinimum initial (initial.nr 8) result)
    (selected : result.nr 1 ≠ 0) :
    0 ≤ result.rr 1 ∧
      (∃ c ∈ full, decode (result.nr 1) = some c.event ∧ 0 < c.rate ∧ result.rr 1 * c.rate = c.slack) ∧
      ∀ c ∈ full, result.rr 1 * c.rate ≤ c.slack := by
  obtain ⟨i, within, present, identifier, delta⟩ := computed.1 selected
  obtain ⟨chosen, member, rising, ratio, event⟩ := table.row_of_present within present
  have chosenIn := cache.sound member
  have amount := delta.trans ratio
  have nonneg : 0 ≤ result.rr 1 := amount.symm ▸ div_nonneg (initially chosen chosenIn) rising.le
  refine ⟨nonneg, ⟨chosen, chosenIn, identifier.symm ▸ event, rising, ?_⟩, ?_⟩
  · rw [amount, div_mul_cancel₀ _ rising.ne']
  · intro c hc
    by_cases increases : 0 < c.rate
    · obtain ⟨r, hr, sameRate, smaller⟩ := cache.covers c hc increases
      have rRising : 0 < r.rate := sameRate.symm ▸ increases
      obtain ⟨j, jWithin, jPresent, jRatio⟩ := table.present_of_row hr rRising
      have lower := (computed.2 j jWithin jPresent).2.trans_eq jRatio
      have safeRepresentative : result.rr 1 * c.rate ≤ r.slack := by
        simpa only [sameRate] using (le_div_iff₀ rRising).mp lower
      exact safeRepresentative.trans smaller
    · exact (mul_nonpos_of_nonneg_of_nonpos nonneg (le_of_not_gt increases)).trans (initially c hc)

theorem dualBoundMinimum_empty_iff {Event : Type*} {initial result : ArithmeticState}
    {rows : List (Option (DualSlack Event))} {decode : ℕ → Option Event} {full : List (DualSlack Event)}
    (table : DualBoundTable initial rows decode) (cache : DualSlackCache full (rows.filterMap id))
    (computed : DualBoundMinimum initial (initial.nr 8) result) :
    result.nr 1 = 0 ↔ ∀ c ∈ full, c.rate ≤ 0 := by
  constructor
  · intro empty c hc
    by_contra bad
    have rising : 0 < c.rate := lt_of_not_ge bad
    obtain ⟨r, hr, rate, _⟩ := cache.covers c hc rising
    obtain ⟨j, within, present, _⟩ := table.present_of_row hr (rate.symm ▸ rising)
    exact (computed.2 j within present).1 empty
  · intro noEvents
    by_contra nonempty
    obtain ⟨i, within, present, _, _⟩ := computed.1 nonempty
    obtain ⟨c, hc, rising, _, _⟩ := table.row_of_present within present
    exact (not_le_of_gt rising) (noEvents c (cache.sound hc))

end VehicleRoutingSurvey.Routing
end RppSource_WeightedDeltaTable

/-! matching/MatchingCandidateMemory.lean -/
section RppSource_MatchingCandidateMemory
namespace VehicleRoutingSurvey.Routing





private theorem readMatchingCandidate_empty {k i : ℕ} {cutAt : Fin k → Finset (Fin k)}
    {s : ArithmeticState} (empty : s.nm (s.nr 58 + i) = 0) :
    readMatchingCandidate cutAt s i = none := by
  simp [readMatchingCandidate, empty, decodeMatchingDictionaryEvent]

/-- The decoded rows supply the physical table read by the delta selector. -/
theorem readMatchingCandidates_table {k : ℕ} (cutAt : Fin k → Finset (Fin k)) (s : ArithmeticState)
    (idBase : s.nr 3 = s.nr 58) (slackBase : s.nr 4 = s.nr 59) (rateBase : s.nr 5 = s.nr 60)
    (valid : ∀ i < s.nr 8, MatchingCandidateRowValid cutAt s i) :
    DualBoundTable s (List.ofFn (fun i : Fin (s.nr 8) => readMatchingCandidate cutAt s i))
      (decodeMatchingDictionaryEvent k cutAt s) := by
  constructor
  · simp
  · intro i within
    have inside : i < s.nr 8 := by simpa using within
    have h := valid i inside
    change s.nm (s.nr 58 + i) = 0 ∨ _ at h
    rcases h with empty | ⟨sameId, event, decoded⟩
    · simp [readMatchingCandidate_empty (cutAt := cutAt) empty, dualBoundIdentifier, idBase, empty]
    · change decodeMatchingDictionaryEvent k cutAt s (s.nm (s.nr 58 + i)) = some event at decoded
      have nonzero : s.nm (s.nr 58 + i) ≠ 0 := by rw [sameId]; omega
      simp only [List.getElem_ofFn, readMatchingCandidate, decoded, Option.map_some]
      simpa only [dualBoundIdentifier, idBase, slackBase, rateBase] using
        (show s.nm (s.nr 58 + i) ≠ 0 ∧
          decodeMatchingDictionaryEvent k cutAt s (s.nm (s.nr 58 + i)) = some event ∧
          s.rm (s.nr 59 + i) = s.rm (s.nr 59 + i) ∧ s.rm (s.nr 60 + i) = s.rm (s.nr 60 + i) from
          ⟨nonzero, decoded, rfl, rfl⟩)




end VehicleRoutingSurvey.Routing
end RppSource_MatchingCandidateMemory

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

/-! matching/MatchingCacheGroups.lean -/
section RppSource_MatchingCacheGroups
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



def MatchingCandidateGroup.all (n : ℕ) : List (MatchingCandidateGroup n) :=
  (List.finRange n).map .outer ++ (List.finRange n).map .incoming ++ (List.finRange n).map .cut

@[simp] theorem MatchingCandidateGroup.mem_all {n : ℕ} (g : MatchingCandidateGroup n) :
    g ∈ MatchingCandidateGroup.all n := by
  cases g <;> simp [MatchingCandidateGroup.all]







theorem MatchingCandidateGroup.admits_same_rate {n : ℕ} {cuts : Finset (Finset (Fin n))}
    {blocks : TopLevelMatchingBlocks Finset.univ cuts} {forest : AlternatingForestState (Fin n)}
    {rep : Finset (Fin n) → Fin n} {x y : DualSlack (MatchingDualEvent n)}
    (g : MatchingCandidateGroup n) (hx : g.admits blocks forest rep x) (hy : g.admits blocks forest rep y) :
    x.rate = y.rate := by
  cases g <;> exact hx.1.trans hy.1.symm

/-- Every positive-rate constraint is represented in one of the three candidate ranges. -/
theorem matchingCandidateGroup_for_positive {n : ℕ} {cuts : Finset (Finset (Fin n))}
    (blocks : TopLevelMatchingBlocks Finset.univ cuts) (forest : AlternatingForestState (Fin n))
    (rep : Finset (Fin n) → Fin n) (c : Fin n → Fin n → ℝ)
    (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ) {d : DualSlack (MatchingDualEvent n)}
    (present : let label := fun B => (forest.role (rep B)).dualDirection
      d ∈ matchingDualSlacks c (compactMatchingEdges n) cuts potential (forestVertexDirection blocks label)
        cutDual (forestCutDirection blocks label))
    (positive : 0 < d.rate) : ∃ g : MatchingCandidateGroup n, g.admits blocks forest rep d := by
  let role := fun B : Finset (Fin n) => forest.role (rep B)
  let label := fun B : Finset (Fin n) => (role B).dualDirection
  change d ∈ matchingDualSlacks c (compactMatchingEdges n) cuts potential (forestVertexDirection blocks label)
    cutDual (forestCutDirection blocks label) at present
  rcases List.mem_append.mp present with edgePresent | cutPresent
  · obtain ⟨e, edge, rfl⟩ := List.mem_map.mp edgePresent
    induction e using Sym2.inductionOn with
    | hf u v =>
      have distinct : u ≠ v := fun equal => (mem_compactMatchingEdges_iff.mp edge) (Sym2.mk_isDiag_iff.mpr equal)
      have slope := forest_edge_slope blocks label (Finset.mem_univ u) (Finset.mem_univ v) distinct
      have separated : blocks.block u ≠ blocks.block v := by
        intro same
        simp only [matchingEdgeSlack, slope, if_pos same, lt_self_iff_false] at positive
      simp only [matchingEdgeSlack, slope, if_neg separated] at positive
      have classification := (risingForestEdge_iff (role (blocks.block u)) (role (blocks.block v))).mp positive
      rcases classification with ⟨⟨p, firstOuter⟩, ⟨q, secondOuter⟩ | secondIdle⟩ | ⟨firstIdle, q, secondOuter⟩
      · refine ⟨.outer (rep (blocks.block u)), ?_, u, v, rfl, rfl⟩
        change oddCutDualEdgeValue cuts (forestVertexDirection blocks label) (forestCutDirection blocks label) s(u, v) = 2
        rw [slope, if_neg separated]
        change (role (blocks.block u)).dualDirection + (role (blocks.block v)).dualDirection = 2
        rw [firstOuter, secondOuter] <;> norm_num [AlternatingForestRole.dualDirection]
      · refine ⟨.incoming v, ?_, u, rfl, separated, ⟨p, firstOuter⟩, Or.inl secondIdle⟩
        change oddCutDualEdgeValue cuts (forestVertexDirection blocks label) (forestCutDirection blocks label) s(u, v) =
          incomingCandidateRate (role (blocks.block v))
        rw [slope, if_neg separated]
        change (role (blocks.block u)).dualDirection + (role (blocks.block v)).dualDirection =
          incomingCandidateRate (role (blocks.block v))
        rw [firstOuter, secondIdle] <;> simp [AlternatingForestRole.dualDirection, incomingCandidateRate]
      · refine ⟨.incoming u, ?_, v, ?_, separated.symm, ⟨q, secondOuter⟩, Or.inl firstIdle⟩
        · change oddCutDualEdgeValue cuts (forestVertexDirection blocks label) (forestCutDirection blocks label) s(u, v) =
            incomingCandidateRate (role (blocks.block u))
          rw [slope, if_neg separated]
          change (role (blocks.block u)).dualDirection + (role (blocks.block v)).dualDirection =
            incomingCandidateRate (role (blocks.block u))
          rw [firstIdle, secondOuter] <;> simp [AlternatingForestRole.dualDirection, incomingCandidateRate]
        · exact congrArg MatchingDualEvent.edge Sym2.eq_swap
  · obtain ⟨S, _, rfl⟩ := List.mem_map.mp cutPresent
    have decreases : forestCutDirection blocks label S < 0 := neg_pos.mp positive
    obtain ⟨active, parent, inner⟩ := (forestCutDirection_negative_iff blocks role S).mp decreases
    refine ⟨.cut (rep S), ?_, S, rfl, rfl⟩
    change -(forestCutDirection blocks label S) = 1
    rw [forestCutDirection, if_pos active]
    simp [label, inner, AlternatingForestRole.dualDirection]

/-- The three exact per-row minima imply the cache contract required by the selector. -/
theorem matchingCandidateGroups_cache {n : ℕ} {cuts : Finset (Finset (Fin n))}
    (blocks : TopLevelMatchingBlocks Finset.univ cuts) (forest : AlternatingForestState (Fin n))
    (rep : Finset (Fin n) → Fin n) (c : Fin n → Fin n → ℝ)
    (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ)
    (cached : MatchingCandidateGroup n → Option (DualSlack (MatchingDualEvent n)))
    (least : let label := fun B => (forest.role (rep B)).dualDirection
      let full := matchingDualSlacks c (compactMatchingEdges n) cuts potential (forestVertexDirection blocks label)
        cutDual (forestCutDirection blocks label)
      ∀ g, LeastSlackEntry (full.filter fun d => @decide _ (Classical.propDecidable (g.admits blocks forest rep d))) (cached g)) :
    let label := fun B => (forest.role (rep B)).dualDirection
    DualSlackCache (matchingDualSlacks c (compactMatchingEdges n) cuts potential (forestVertexDirection blocks label)
      cutDual (forestCutDirection blocks label)) ((MatchingCandidateGroup.all n).filterMap cached) := by
  classical
  dsimp only at least ⊢
  constructor
  · intro d present
    obtain ⟨g, _, encoded⟩ := List.mem_filterMap.mp present
    exact (List.mem_filter.mp ((least g).sound encoded)).1
  · intro d present positive
    obtain ⟨g, belongs⟩ := matchingCandidateGroup_for_positive blocks forest rep c potential cutDual present positive
    let label := fun B => (forest.role (rep B)).dualDirection
    let full := matchingDualSlacks c (compactMatchingEdges n) cuts potential (forestVertexDirection blocks label)
      cutDual (forestCutDirection blocks label)
    have member : d ∈ full.filter (fun x => @decide _ (Classical.propDecidable (g.admits blocks forest rep x))) :=
      List.mem_filter.mpr ⟨present, decide_eq_true belongs⟩
    obtain ⟨candidate, represented, lower⟩ := (least g).covers d member
    have candidateMember := List.mem_filter.mp ((least g).sound represented)
    have admissible : g.admits blocks forest rep candidate := of_decide_eq_true candidateMember.2
    exact ⟨candidate, List.mem_filterMap.mpr ⟨g, g.mem_all, represented⟩, g.admits_same_rate admissible belongs, lower⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingCacheGroups

/-! matching/MatchingSelectedEvent.lean -/
section RppSource_MatchingSelectedEvent
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The cached selector of an incomplete search must return a real event. Its RAM result
provides a safe dual adjustment and a tight decoded edge or an exhausted cut. -/
theorem selectedMatchingEvent_of_incomplete {k : ℕ} {c : Fin k → Fin k → ℝ}
    {covered : Finset (Fin k)} {matching : Finset (Sym2 (Fin k))}
    (matched : IsPerfectMatchingOn covered matching) (even : Even k) (incomplete : covered ≠ Finset.univ)
    {cuts : Finset (Finset (Fin k))} (blocks : TopLevelMatchingBlocks Finset.univ cuts)
    (label : Finset (Fin k) → ℝ) (potential : Fin k → ℝ) (cutDual : Finset (Fin k) → ℝ)
    (rootOuter : ∀ v ∈ Finset.univ \ covered, label (blocks.block v) = 1)
    (blockBase : ∀ S ∈ Finset.univ.image blocks.block, ∃ base, ∀ v ∈ S, v ≠ base → v ∈ covered)
    (feasible : ∀ e ∈ compactMatchingEdges k, oddCutDualEdgeValue cuts potential cutDual e ≤ edgeCost c e)
    (nonnegative : ∀ S ∈ cuts, 0 ≤ cutDual S)
    {s chosen : ArithmeticState} {rows : List (Option (DualSlack (MatchingDualEvent k)))}
    {decode : ℕ → Option (MatchingDualEvent k)} (table : DualBoundTable s rows decode)
    (cache : DualSlackCache (matchingDualSlacks c (compactMatchingEdges k) cuts potential
      (forestVertexDirection blocks label) cutDual (forestCutDirection blocks label)) (rows.filterMap id))
    (selected : DualBoundMinimum s (s.nr 8) chosen) :
    chosen.nr 1 ≠ 0 ∧ ∃ event, decode (chosen.nr 1) = some event ∧
      MatchingDualAdjustment c (compactMatchingEdges k) cuts potential (forestVertexDirection blocks label)
        cutDual (forestCutDirection blocks label) ⟨event, chosen.rr 1⟩ := by
  have evenCard : Even (Finset.univ : Finset (Fin k)).card := by simpa using even
  obtain ⟨bound, found⟩ := matchingDualBound_exists_of_incomplete matched (Finset.subset_univ _)
    evenCard incomplete c (compactMatchingEdges k) (fun _ _ _ _ h => mem_compactMatchingEdges_mk h)
    cuts blocks label potential cutDual rootOuter blockBase
  have present : chosen.nr 1 ≠ 0 := by
    intro empty
    have none := (nextDualBound_eq_none _).mpr ((dualBoundMinimum_empty_iff table cache selected).mp empty)
    rw [found] at none
    cases none
  obtain ⟨nonneg, ⟨constraint, member, event, increasing, tight⟩, safe⟩ :=
    dualBoundMinimum_safe table cache (matchingDualSlacks_nonnegative feasible nonnegative) selected present
  exact ⟨present, constraint.event, event, matchingDualAdjustment_of_slacks
    ⟨nonneg, ⟨constraint, member, rfl, increasing, tight⟩, safe⟩⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingSelectedEvent

/-! matching/MatchingActiveSelection.lean -/
section RppSource_MatchingActiveSelection
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



theorem MatchingCandidateGroup.slot_lt {k : ℕ} (g : MatchingCandidateGroup k) : g.slot < 3 * k := by
  cases g with
  | outer u | incoming u | cut u => have := u.isLt; simp [MatchingCandidateGroup.slot] <;> omega

theorem MatchingCandidateGroup.exists_slot {k i : ℕ} (inside : i < 3 * k) :
    ∃ g : MatchingCandidateGroup k, g.slot = i := by
  by_cases outer : i < k
  · exact ⟨.outer ⟨i, outer⟩, rfl⟩
  by_cases incoming : i < 2 * k
  · exact ⟨.incoming ⟨i - k, by omega⟩, by simp [MatchingCandidateGroup.slot] <;> omega⟩
  · exact ⟨.cut ⟨i - 2 * k, by omega⟩, by simp [MatchingCandidateGroup.slot] <;> omega⟩

private theorem cacheSlotMem_iff {k : ℕ} {cutAt : Fin k → Finset (Fin k)} {s : ArithmeticState}
    (count : s.nr 8 = 3 * k) (entry : DualSlack (MatchingDualEvent k)) :
    entry ∈ (List.ofFn (fun i : Fin (s.nr 8) => readMatchingCandidate cutAt s i)).filterMap id ↔
      entry ∈ (MatchingCandidateGroup.all k).filterMap (fun g => readMatchingCandidate cutAt s g.slot) := by
  constructor
  · intro mem
    obtain ⟨row, inRows, found⟩ := List.mem_filterMap.mp mem
    obtain ⟨i, atIndex, same⟩ := List.mem_iff_getElem.mp inRows
    have inside : i < 3 * k := by simpa only [List.length_ofFn, count] using atIndex
    obtain ⟨g, position⟩ := MatchingCandidateGroup.exists_slot inside
    refine List.mem_filterMap.mpr ⟨g, g.mem_all, ?_⟩
    rw [position]
    have equal : readMatchingCandidate cutAt s i = row := by simpa only [List.getElem_ofFn] using same
    exact equal.trans found
  · intro mem
    obtain ⟨g, _, chosen⟩ := List.mem_filterMap.mp mem
    have inside : g.slot < s.nr 8 := count.symm ▸ g.slot_lt
    let i : Fin (s.nr 8) := ⟨g.slot, inside⟩
    refine List.mem_filterMap.mpr ⟨readMatchingCandidate cutAt s i, ?_, chosen⟩
    apply List.mem_iff_getElem.mpr
    exact ⟨g.slot, by simpa using inside, by simp [i]⟩

/-- Once each candidate group is exact, the physical rows form the selector's
dual-slack cache and its chosen event is safe for the full system. -/
theorem selectedMatchingCacheEvent {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) (even : Even k) (incomplete : state.covered ≠ Finset.univ)
    (blocks : TopLevelMatchingBlocks Finset.univ state.cuts) (forest : AlternatingForestState (Fin k))
    (rep : Finset (Fin k) → Fin k)
    (rootOuter : ∀ v ∈ Finset.univ \ state.covered, (forest.role (rep (blocks.block v))).dualDirection = 1)
    (blockBase : ∀ S ∈ Finset.univ.image blocks.block, ∃ base, ∀ v ∈ S, v ≠ base → v ∈ state.covered)
    (cutAt : Fin k → Finset (Fin k)) {s chosen : ArithmeticState}
    (count : s.nr 8 = 3 * k) (ids : s.nr 3 = s.nr 58) (slacks : s.nr 4 = s.nr 59) (rates : s.nr 5 = s.nr 60)
    (valid : ∀ i < s.nr 8, MatchingCandidateRowValid cutAt s i)
    (least : let label := fun B => (forest.role (rep B)).dualDirection
      let all := matchingDualSlacks cost (compactMatchingEdges k) state.cuts state.potential
        (forestVertexDirection blocks label) state.cutDual (forestCutDirection blocks label)
      ∀ g : MatchingCandidateGroup k,
        LeastSlackEntry (all.filter fun d => @decide _ (Classical.propDecidable (g.admits blocks forest rep d)))
          (readMatchingCandidate cutAt s g.slot))
    (selected : DualBoundMinimum s (s.nr 8) chosen) :
    let label := fun B => (forest.role (rep B)).dualDirection
    chosen.nr 1 ≠ 0 ∧ ∃ event, decodeMatchingDictionaryEvent k cutAt s (chosen.nr 1) = some event ∧
      MatchingDualAdjustment cost (compactMatchingEdges k) state.cuts state.potential
        (forestVertexDirection blocks label) state.cutDual (forestCutDirection blocks label) ⟨event, chosen.rr 1⟩ := by
  intro label
  let rows := List.ofFn (fun i : Fin (s.nr 8) => readMatchingCandidate cutAt s i)
  let full := matchingDualSlacks cost (compactMatchingEdges k) state.cuts state.potential
    (forestVertexDirection blocks label) state.cutDual (forestCutDirection blocks label)
  have grouped := matchingCandidateGroups_cache blocks forest rep cost state.potential state.cutDual
    (fun g => readMatchingCandidate cutAt s g.slot) least
  have exactRows : DualSlackCache full (rows.filterMap id) := by
    constructor
    · intro d mem
      exact grouped.sound ((cacheSlotMem_iff count d).mp mem)
    · intro d mem rising
      obtain ⟨best, belongs, rate, lower⟩ := grouped.covers d mem rising
      exact ⟨best, (cacheSlotMem_iff count best).mpr belongs, rate, lower⟩
  have feasibility (e : Sym2 (Fin k)) (present : e ∈ compactMatchingEdges k) :=
    state.feasible e (mem_compactMatchingEdges_iff.mp present)
  exact selectedMatchingEvent_of_incomplete state.perfect even incomplete blocks label state.potential state.cutDual
    rootOuter blockBase feasibility (fun B present => (state.cutValid B present).2)
    (readMatchingCandidates_table cutAt s ids slacks rates valid) exactRows selected


end VehicleRoutingSurvey.Routing
end RppSource_MatchingActiveSelection

/-! matching/MatchingSelectedRows.lean -/
section RppSource_MatchingSelectedRows
namespace VehicleRoutingSurvey.Routing

/-- During the selector's slack pass, no dictionary, rate, or normalized
outer-pair score is changed. Every decoded row advances by its own rate. -/
theorem selectAndAdvanceDualSlackBlock_rows {k : ℕ} (cutAt : Fin k → Finset (Fin k))
    {s t : ArithmeticState} {steps : ℕ} (run : BlockRuns selectAndAdvanceDualSlackBlock steps s t)
    (nonzero : t.nr 1 ≠ 0) (layout : MatchingCacheLayout k s)
    (count : s.nr 8 = s.nr 61) (slacks : s.nr 4 = s.nr 59) (rates : s.nr 5 = s.nr 60)
    (natural : t.nm = s.nm)
    (real : ∀ a, t.rm a = if t.nr 1 ≠ 0 ∧ s.nr 4 ≤ a ∧ a < s.nr 4 + s.nr 8 then
      s.rm a - t.rr 1 * s.rm (s.nr 5 + (a - s.nr 4)) else s.rm a) :
    (∀ i < s.nr 61, MatchingCandidateRowValid cutAt t i ↔ MatchingCandidateRowValid cutAt s i) ∧
    (∀ i < s.nr 61, readMatchingCandidate cutAt t i =
      (readMatchingCandidate cutAt s i).map (DualSlack.advance (t.rr 1))) ∧
    ∀ i, readMatchingPairBucket (k := k) t i = readMatchingPairBucket s i := by
  have fixed (r : ℕ) (unchanged : r ∉ [0, 1, 2, 6, 7, 10, 11] := by decide) : t.nr r = s.nr r :=
    (selectAndAdvanceDualSlackBlock_keeps_registers run).1 r unchanged
  have decoded (id : ℕ) : decodeMatchingDictionaryEvent k cutAt t id = decodeMatchingDictionaryEvent k cutAt s id := by
    simp only [decodeMatchingDictionaryEvent, fixed 54, natural]
  have ratesAbove := layout.slacksBefore
  have keysAbove := layout.ratesBefore
  have unchanged (a : ℕ) (above : s.nr 59 + s.nr 61 ≤ a) : t.rm a = s.rm a := by
    rw [real, if_neg]
    intro h
    apply (not_lt_of_ge above)
    simpa only [slacks, count] using h.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro i _
    simp only [MatchingCandidateRowValid, fixed 58, natural, decoded]
  · intro i within
    have active : t.nr 1 ≠ 0 ∧ s.nr 4 ≤ s.nr 59 + i ∧ s.nr 59 + i < s.nr 4 + s.nr 8 := by
      rw [slacks, count]
      omega
    have shifted : t.rm (s.nr 59 + i) = s.rm (s.nr 59 + i) - t.rr 1 * s.rm (s.nr 60 + i) := by
      rw [real, if_pos active, slacks, rates, Nat.add_sub_cancel_left]
    have fixedRate := unchanged (s.nr 60 + i) (by omega)
    simp only [readMatchingCandidate, fixed 58, fixed 59, fixed 60, natural, decoded, shifted, fixedRate]
    cases (decodeMatchingDictionaryEvent k cutAt s (s.nm (s.nr 58 + i))) <;> rfl
  · intro i
    have fixedKey := unchanged (s.nr 66 + i) (by omega)
    simp only [readMatchingPairBucket, fixed 65, fixed 66, natural, fixedKey]

/-- A dual step subtracts its rate times the step size from every mathematical
constraint. Its event and rate are unchanged until the forest changes. -/
theorem matchingDualSlacks_shift {k : ℕ} (cost : Fin k → Fin k → ℝ)
    (edges : List (Sym2 (Fin k))) (cuts : Finset (Finset (Fin k))) (potential direction : Fin k → ℝ)
    (cutDual cutDirection : Finset (Fin k) → ℝ) (delta : ℝ) :
    matchingDualSlacks cost edges cuts (fun v => potential v + delta * direction v) direction
      (fun S => cutDual S + delta * cutDirection S) cutDirection =
    (matchingDualSlacks cost edges cuts potential direction cutDual cutDirection).map (DualSlack.advance delta) := by
  have edge (e : Sym2 (Fin k)) : matchingEdgeSlack cost cuts (fun v => potential v + delta * direction v)
      direction (fun S => cutDual S + delta * cutDirection S) cutDirection e =
      (matchingEdgeSlack cost cuts potential direction cutDual cutDirection e).advance delta := by
    simp only [matchingEdgeSlack, DualSlack.advance, oddCutDualEdgeValue_shift, sub_add_eq_sub_sub]
  have cut (S : Finset (Fin k)) : matchingCutSlack (fun B => cutDual B + delta * cutDirection B) cutDirection S =
      (matchingCutSlack cutDual cutDirection S).advance delta := by
    simp only [matchingCutSlack, DualSlack.advance, mul_neg, sub_neg_eq_add]
  simp only [matchingDualSlacks, List.map_append, List.map_map, Function.comp_def, funext edge, funext cut]

/-- The mathematical least-entry invariant persists across the same slack
advance as the selector, because each group has a common rate. -/
theorem MatchingCandidateGroup.least_after_dual_step {k : ℕ} {cuts : Finset (Finset (Fin k))}
    (group : MatchingCandidateGroup k) (blocks : TopLevelMatchingBlocks Finset.univ cuts)
    (forest : AlternatingForestState (Fin k)) (rep : Finset (Fin k) → Fin k)
    {full : List (DualSlack (MatchingDualEvent k))} {row : Option (DualSlack (MatchingDualEvent k))}
    (before : LeastSlackEntry (full.filter fun d => @decide _ (Classical.propDecidable (group.admits blocks forest rep d))) row)
    (delta : ℝ) :
    LeastSlackEntry ((full.map (DualSlack.advance delta)).filter fun d =>
      @decide _ (Classical.propDecidable (group.admits blocks forest rep d))) (row.map (DualSlack.advance delta)) := by
  classical
  let key := fun d => @decide _ (Classical.propDecidable (group.admits blocks forest rep d))
  have shared (x : DualSlack (MatchingDualEvent k)) (hx : x ∈ full.filter key)
      (y : DualSlack (MatchingDualEvent k)) (hy : y ∈ full.filter key) : x.rate = y.rate :=
    group.admits_same_rate (of_decide_eq_true (List.mem_filter.mp hx).2) (of_decide_eq_true (List.mem_filter.mp hy).2)
  have advanced := before.advance shared delta
  have member (x : DualSlack (MatchingDualEvent k)) :
      x ∈ (full.map (DualSlack.advance delta)).filter key ↔ x ∈ (full.filter key).map (DualSlack.advance delta) := by
    constructor
    · intro present
      obtain ⟨mapped, admitted⟩ := List.mem_filter.mp present
      obtain ⟨old, inFull, rfl⟩ := List.mem_map.mp mapped
      have same : group.admits blocks forest rep (old.advance delta) ↔ group.admits blocks forest rep old := by
        cases group <;> rfl
      exact List.mem_map_of_mem (List.mem_filter.mpr ⟨inFull, decide_eq_true (same.mp (of_decide_eq_true admitted))⟩)
    · intro present
      obtain ⟨old, inGroup, rfl⟩ := List.mem_map.mp present
      obtain ⟨inFull, admitted⟩ := List.mem_filter.mp inGroup
      have same : group.admits blocks forest rep (old.advance delta) ↔ group.admits blocks forest rep old := by
        cases group <;> rfl
      exact List.mem_filter.mpr ⟨List.mem_map_of_mem inFull, decide_eq_true (same.mpr (of_decide_eq_true admitted))⟩
  exact ⟨fun chosen => (member _).mpr (advanced.sound chosen),
    fun x choices => advanced.covers x ((member x).mp choices)⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingSelectedRows

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

/-! matching/MatchingSearchSelection.lean -/
section RppSource_MatchingSearchSelection
namespace VehicleRoutingSurvey.Routing





theorem MatchingSearchRows.separated {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {cutAt : Fin k → Finset (Fin k)}
    {s : ArithmeticState} (rows : MatchingSearchRows part forest positive cutAt s) :
    ∀ i < s.nr 8, ¬ (s.nr 4 ≤ s.nr 5 + i ∧ s.nr 5 + i < s.nr 4 + s.nr 8) := by
  rw [rows.slacks, rows.rates, rows.count]
  have bound := rows.layout.slacksBefore
  intro i _ range
  omega

/-- The actual selector supplies a correctly classified event and advances all
rows to the same dual point. The next block can change the forest there. -/
theorem selectedMatchingSearch_step {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop}
    {positive : 0 < k} {cutAt : Fin k → Finset (Fin k)} {s chosen : ArithmeticState} {ticks : ℕ}
    (search : CompactMatchingSearchForest part forest mate tight) (even : Even k) (incomplete : state.covered ≠ Finset.univ)
    (table : MatchingSearchRows part forest positive cutAt s)
    (roles : AlternatingForestMemory forest (s.nr 51) s.nm)
    (reps : ∀ v : Fin k, s.nm (s.nr 57 + v.val) = (part.representative v).val)
    (run : BlockRuns selectAndAdvanceDualSlackBlock ticks s chosen)
    (minimum : DualBoundMinimum s (s.nr 8) chosen) (natural : chosen.nm = s.nm)
    (real : ∀ a, chosen.rm a = if chosen.nr 1 ≠ 0 ∧ s.nr 4 ≤ a ∧ a < s.nr 4 + s.nr 8 then
      s.rm a - chosen.rr 1 * s.rm (s.nr 5 + (a - s.nr 4)) else s.rm a) :
    let rep := part.representativeOf positive
    let label := part.dualLabel forest positive
    let direction := forestVertexDirection part.blocks label
    let cutDirection := forestCutDirection part.blocks label
    chosen.nr 1 ≠ 0 ∧
      (∃ event, MatchingEventRecord cutAt (matchingOriginalGrowthEvent chosen) event ∧
        MatchingEventClassView part.blocks forest rep cutAt chosen event ∧
        MatchingDualAdjustment cost (compactMatchingEdges k) state.cuts state.potential direction
          state.cutDual cutDirection ⟨event, chosen.rr 1⟩) ∧
      (∀ i < s.nr 61, MatchingCandidateRowValid cutAt chosen i) ∧
      (∀ group : MatchingCandidateGroup k,
        LeastSlackEntry ((matchingDualSlacks cost (compactMatchingEdges k) state.cuts
            (fun v => state.potential v + chosen.rr 1 * direction v) direction
            (fun B => state.cutDual B + chosen.rr 1 * cutDirection B) cutDirection).filter fun d =>
            @decide _ (Classical.propDecidable (group.admits part.blocks forest rep d)))
          (readMatchingCandidate cutAt chosen group.slot)) ∧
      ∀ i, readMatchingPairBucket (k := k) chosen i = readMatchingPairBucket s i := by
  intro rep label direction cutDirection
  have root (v : Fin k) (member : v ∈ Finset.univ \ state.covered) : (forest.role (rep (part.blocks.block v))).dualDirection = 1 := by
    rw [show rep (part.blocks.block v) = part.representative v from part.representativeOf_block positive v,
      search.exposed v (Finset.mem_sdiff.mp member).2]
    rfl
  have base (S : Finset (Fin k)) (hs : S ∈ Finset.univ.image part.blocks.block) :
      ∃ v, ∀ w ∈ S, w ≠ v → w ∈ state.covered := by
    obtain ⟨v, _, good⟩ := part.blockBase hs
    exact ⟨v, good⟩
  obtain ⟨nonzero, event, decoded, good⟩ := selectedMatchingCacheEvent state even incomplete part.blocks forest rep
    root base cutAt (table.count.trans table.layout.rows) table.ids table.slacks table.rates
    (fun i hi => table.valid i (table.count ▸ hi)) table.least minimum
  have bytes := (chosenMatchingEvent_record run natural decoded).2
  have registers (r : ℕ) (safe : r ∉ [0, 1, 2, 6, 7, 10, 11] := by decide) :=
    (selectAndAdvanceDualSlackBlock_keeps_registers run).1 r safe
  have rolesNow : AlternatingForestMemory forest (chosen.nr 51) chosen.nm := by
    rw [registers 51, natural]
    exact roles
  have repsNow (v : Fin k) : chosen.nm (chosen.nr 57 + v.val) = (rep (part.blocks.block v)).val := by
    rw [registers 57, natural, show rep (part.blocks.block v) = part.representative v from part.representativeOf_block positive v]
    exact reps v
  have kind := matchingEventClass_of_adjustment state part.blocks forest rep cutAt
    ((registers 55).trans table.layout.dimension) rolesNow repsNow bytes good
  obtain ⟨validRows, newRows, keys⟩ := selectAndAdvanceDualSlackBlock_rows cutAt run nonzero table.layout
    table.count table.slacks table.rates natural real
  refine ⟨nonzero, ⟨event, bytes, kind, good⟩, fun i hi => (validRows i hi).mpr (table.valid i hi), ?_, keys⟩
  intro group
  have inside : group.slot < s.nr 61 := table.layout.rows.symm ▸ group.slot_lt
  rw [newRows group.slot inside, matchingDualSlacks_shift]
  exact group.least_after_dual_step part.blocks forest rep (table.least group) (chosen.rr 1)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingSearchSelection

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

/-! matching/MatchingRebaseScratch.lean -/
section RppSource_MatchingRebaseScratch
namespace VehicleRoutingSurvey.Routing



theorem allocateMatchingCycleScratchBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (zero : s.nr 14 = 0) :
    ∃ t, BlockRuns allocateMatchingCycleScratchBlock 5 s t ∧ t.halted = false ∧
      t.nr 79 = s.nr 68 ∧ t.nr 80 = s.nr 68 + s.nr 55 ∧ t.nr 68 = s.nr 68 + 4 * s.nr 55 ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 68, 79, 80] → t.nr r = s.nr r := by
  let t := (arithmeticStep allocateMatchingCycleScratchBlock)^[5] s
  have ready : t.halted = false := by
    simp [t, allocateMatchingCycleScratchBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = allocateMatchingCycleScratchBlock.length := by
    simp [t, allocateMatchingCycleScratchBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [t, allocateMatchingCycleScratchBlock, arithmeticStep, entry, running, zero, Function.iterate_succ_apply']
  · simp [t, allocateMatchingCycleScratchBlock, arithmeticStep, entry, running, zero, Function.iterate_succ_apply']
  · simp [t, allocateMatchingCycleScratchBlock, arithmeticStep, entry, running, zero, Function.iterate_succ_apply'] <;> omega
  · simp [t, allocateMatchingCycleScratchBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [t, allocateMatchingCycleScratchBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [t, allocateMatchingCycleScratchBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · intro r safe
    exact arithmeticRun_keeps_from_destination_list _ (by decide) safe s 5


end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseScratch

/-! matching/MatchingRebaseStack.lean -/
section RppSource_MatchingRebaseStack
namespace VehicleRoutingSurvey.Routing



theorem reserveMatchingRebaseJobsBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns reserveMatchingRebaseJobsBlock 2 s t ∧ t.halted = false ∧
      t.nr 68 = s.nr 68 + 2 * s.nr 55 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 68] → t.nr r = s.nr r := by
  let t := (arithmeticStep reserveMatchingRebaseJobsBlock)^[2] s
  have effect : t.pc = reserveMatchingRebaseJobsBlock.length ∧ t.halted = false ∧
      t.nr 68 = s.nr 68 + 2 * s.nr 55 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr := by
    simp [t, reserveMatchingRebaseJobsBlock, arithmeticStep, entry, running,
      Function.iterate_succ_apply', Nat.two_mul]
  obtain ⟨exit, live, cursor, natural, real, realRegisters⟩ := effect
  exact ⟨t, BlockRuns.of_running_exit rfl live exit, live, cursor, natural, real, realRegisters,
    fun _ safe => arithmeticRun_keeps_from_destination_list _ (by decide) safe s 2⟩












end VehicleRoutingSurvey.Routing
end RppSource_MatchingRebaseStack

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









theorem MatchingCycleRecordOrder.empty {s : ArithmeticState}
    (scratch : matchingRebaseScratchEnd s ≤ s.nr 68) (cursor : s.nr 76 = 1) :
    MatchingCycleRecordOrder s := by
  refine ⟨scratch, by omega, ?_, ?_⟩
  · intro _ _ _
    omega
  · intro _ _ _ _ _
    omega



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







structure MatchingBlossomRegistryPosition (s t : ArithmeticState) : Prop where
  representatives : t.nr 74 = s.nr 68
  duals : t.nr 75 = s.nr 69
  next : t.nr 76 = 1
  recordStarts : t.nr 77 = s.nr 68 + s.nr 55
  recordLengths : t.nr 78 = s.nr 68 + s.nr 55 + matchingBlossomCapacity (s.nr 55)
  naturalEnd : t.nr 68 = s.nr 68 + s.nr 55 + 2 * matchingBlossomCapacity (s.nr 55)
  realEnd : t.nr 69 = s.nr 69 + matchingBlossomCapacity (s.nr 55)
  zero : t.nr 14 = 0
  registers : ∀ r, r ∉ [14, 68, 69, 74, 75, 76, 77, 78, 79, 80] → t.nr r = s.nr r
  natural : t.nm = s.nm
  real : t.rm = s.rm
  realRegisters : t.rr = s.rr

theorem placeMatchingBlossomRegistry_correct (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (pairEnd : s.nr 69 = s.nr 66 + s.nr 55 * s.nr 55) :
    ∃ t, BlockRuns placeMatchingBlossomRegistry 12 s t ∧ t.halted = false ∧
      MatchingBlossomRegistryPosition s t := by
  let t := (arithmeticStep placeMatchingBlossomRegistry)^[12] s
  have computed : t.pc = placeMatchingBlossomRegistry.length ∧ t.halted = false := by
    simp [t, arithmeticStep, placeMatchingBlossomRegistry, Function.iterate_succ_apply', entry, running]
  refine ⟨t, BlockRuns.of_running_exit rfl computed.2 computed.1, computed.2, ?_⟩
  have span : s.nr 69 - s.nr 66 = s.nr 55 * s.nr 55 := by omega
  constructor
  case registers =>
    intro r others
    simp at others
    obtain ⟨r14, r68, r69, r74, r75, r76, r77, r78, r79, r80⟩ := others
    simp [t, arithmeticStep, placeMatchingBlossomRegistry, Function.iterate_succ_apply', entry, running,
      r14, r68, r69, r74, r75, r76, r77, r78, r79, r80]
  all_goals
    simp [t, arithmeticStep, placeMatchingBlossomRegistry, Function.iterate_succ_apply', entry, running,
      span, matchingBlossomCapacity] <;> omega





private def clearedRegistrySources (s : ArithmeticState) (i : ℕ) (m : ArithmeticState) : Prop :=
  m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧
    (∀ r, r ≠ 6 → r ≠ 7 → m.nr r = s.nr r) ∧ m.rm = s.rm ∧ m.rr = s.rr ∧
    ∀ a, m.nm a = if s.nr 74 ≤ a ∧ a < s.nr 74 + i then 0 else s.nm a

/-- Before the first stage every representative is a singleton. Old memory and real
registers are preserved, including the cached metric and pair table. -/
theorem initializeMatchingBlossomRegistry_correct (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (pairEnd : s.nr 69 = s.nr 66 + s.nr 55 * s.nr 55) :
    ∃ t, BlockRuns initializeMatchingBlossomRegistry (12 + (1 + (s.nr 55 * 5 + 1))) s t ∧
      t.halted = false ∧
      t.nr 74 = s.nr 68 ∧ t.nr 75 = s.nr 69 ∧ t.nr 76 = 1 ∧
      t.nr 77 = s.nr 68 + s.nr 55 ∧
      t.nr 78 = s.nr 68 + s.nr 55 + matchingBlossomCapacity (s.nr 55) ∧
      t.nr 68 = s.nr 68 + s.nr 55 + 2 * matchingBlossomCapacity (s.nr 55) ∧
      t.nr 69 = s.nr 69 + matchingBlossomCapacity (s.nr 55) ∧
      t.nr 14 = 0 ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ a, t.nm a = if s.nr 68 ≤ a ∧ a < s.nr 68 + s.nr 55 then 0 else s.nm a := by
  obtain ⟨middle, place, live, positioned⟩ := placeMatchingBlossomRegistry_correct s entry running pairEnd
  let source := {middle with pc := 0}
  have k : source.nr 55 = s.nr 55 := positioned.registers 55 (by decide)
  have initial : clearedRegistrySources source 0 {source with pc := 0, nr := Function.update source.nr 7 0} := by
    refine ⟨rfl, live, by simp, ?_, rfl, rfl, ?_⟩
    · intro r _ other7
      exact Function.update_of_ne other7 0 source.nr
    · intro a
      change source.nm a = if source.nr 74 ≤ a ∧ a < source.nr 74 + 0 then 0 else source.nm a
      rw [if_neg (by omega : ¬ (source.nr 74 ≤ a ∧ a < source.nr 74 + 0))]
  have control (i : ℕ) (m : ArithmeticState) (h : clearedRegistrySources source i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 55 = s.nr 55 :=
    ⟨h.1, h.2.1, h.2.2.1, (h.2.2.2.1 55 (by decide) (by decide)).trans k⟩
  have iterate (i : ℕ) (_ : i < s.nr 55) (m : ArithmeticState) (inv : clearedRegistrySources source i m) :
      ∃ t, BlockRuns clearBlossomRegistryRepresentative 2 m t ∧ t.halted = false ∧
        clearedRegistrySources source (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    obtain ⟨atStart, ready, index, frame, real, realRegs, natural⟩ := inv
    have base : m.nr 74 = source.nr 74 := frame 74 (by decide) (by decide)
    have mOne : m.nr 9 = 1 := (frame 9 (by decide) (by decide)).trans ((positioned.registers 9 (by decide)).trans one)
    have mZero : m.nr 14 = 0 := (frame 14 (by decide) (by decide)).trans positioned.zero
    let t := { m with
      pc := 2
      nr := Function.update m.nr 6 (source.nr 74 + i)
      nm := Function.update m.nm (source.nr 74 + i) 0 }
    have ran : BlockRuns clearBlossomRegistryRepresentative 2 m t := by
      apply BlockRuns.of_running_exit
      · simp [t, arithmeticStep, clearBlossomRegistryRepresentative, Function.iterate_succ_apply',
          atStart, ready, index, base, mZero]
      · exact ready
      · rfl
    refine ⟨t, ran, ready, rfl, ready, by simp [t, index, mOne], ?_, real, realRegs, ?_⟩
    · intro r away6 away7
      simpa [t, Function.update_of_ne away6, Function.update_of_ne away7] using frame r away6 away7
    · intro a
      change Function.update m.nm (source.nr 74 + i) 0 a = _
      by_cases current : a = source.nr 74 + i
      · subst a
        rw [Function.update_self, if_pos (by omega : source.nr 74 ≤ source.nr 74 + i ∧
          source.nr 74 + i < source.nr 74 + (i + 1))]
      · rw [Function.update_of_ne current, natural]
        have old : (source.nr 74 ≤ a ∧ a < source.nr 74 + i) ↔
            source.nr 74 ≤ a ∧ a < source.nr 74 + (i + 1) := by omega
        simp only [old]
  obtain ⟨last, final, loop⟩ := countedLoopFromZero_correct 9 7 55 (s.nr 55) 2
    clearBlossomRegistryRepresentative (clearedRegistrySources source) (s := source) rfl live initial control iterate
  obtain ⟨_, stillLive, _, keep, real, realRegisters, natural⟩ := final
  refine ⟨_, place.append loop, stillLive, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    real.trans positioned.real, realRegisters.trans positioned.realRegisters, ?_⟩
  · exact (keep 74 (by decide) (by decide)).trans positioned.representatives
  · exact (keep 75 (by decide) (by decide)).trans positioned.duals
  · exact (keep 76 (by decide) (by decide)).trans positioned.next
  · exact (keep 77 (by decide) (by decide)).trans positioned.recordStarts
  · exact (keep 78 (by decide) (by decide)).trans positioned.recordLengths
  · exact (keep 68 (by decide) (by decide)).trans positioned.naturalEnd
  · exact (keep 69 (by decide) (by decide)).trans positioned.realEnd
  · exact (keep 14 (by decide) (by decide)).trans positioned.zero
  · intro a
    exact (natural a).trans (by
      have base : source.nr 74 = s.nr 68 := positioned.representatives
      have prior : source.nm a = s.nm a := congrFun positioned.natural a
      rw [base, prior])

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

/-! matching/MatchingLiveCycles.lean -/
section RppSource_MatchingLiveCycles
namespace VehicleRoutingSurvey.Routing



def MatchingLiveCycles.empty {k : ℕ} {cost : Fin k → Fin k → ℝ} {state : CompactMatchingPrimalDual k cost}
    {part : CompactMatchingPartition state} {forest : AlternatingForestState (Fin k)}
    {s : ArithmeticState} {dual : MatchingSearchDualMemory part forest s}
    (registry : MatchingRegistryView dual) (empty : state.cuts = ∅) : MatchingLiveCycles registry := by
  have absent (B : Finset (Fin k)) (h : B ∈ state.cuts) : False := by simp [empty] at h
  exact ⟨fun B h => (absent B h).elim,fun B h => (absent B h).elim,fun _ h => (absent _ h).elim,
    fun B h => (absent B h).elim,fun B h => (absent B h).elim⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingLiveCycles

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

/-! matching/MatchingWorkspace.lean -/
section RppSource_MatchingWorkspace
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

/-- New tables for compact matching. There are (k) vertex slots and
(3k) event slots, each with room for two endpoint words. -/
structure MatchingWorkspace where
  mates : ℕ
  roles : ℕ
  parents : ℕ
  depths : ℕ
  representatives : ℕ
  identifiers : ℕ
  endpoints : ℕ
  potentials : ℕ
  slacks : ℕ
  rates : ℕ
  naturalEnd : ℕ
  realEnd : ℕ

def MatchingWorkspace.allocate (k naturalBase realBase : ℕ) : MatchingWorkspace :=
  let roles := naturalBase + k
  let parents := roles + k
  let depths := parents + k
  let representatives := depths + k
  let identifiers := representatives + k
  let endpoints := identifiers + 3 * k
  let slacks := realBase + k
  let rates := slacks + 3 * k
  ⟨naturalBase, roles, parents, depths, representatives, identifiers, endpoints,
    realBase, slacks, rates, endpoints + 6 * k, rates + 3 * k⟩



structure MatchingWorkspaceRegisters (k : ℕ) (layout : MatchingWorkspace)
    (s : ArithmeticState) : Prop where
  dimension : s.nr 55 = k
  mates : s.nr 50 = layout.mates
  roles : s.nr 51 = layout.roles
  parents : s.nr 52 = layout.parents
  depths : s.nr 53 = layout.depths
  representatives : s.nr 57 = layout.representatives
  identifiers : s.nr 58 = layout.identifiers
  endpoints : s.nr 54 = layout.endpoints
  potentials : s.nr 62 = layout.potentials
  slacks : s.nr 59 = layout.slacks
  rates : s.nr 60 = layout.rates
  naturalEnd : s.nr 68 = layout.naturalEnd
  realEnd : s.nr 69 = layout.realEnd

structure MatchingWorkspaceStart (k : ℕ) (layout : MatchingWorkspace)
    (original next : ArithmeticState) : Prop where
  workspace : MatchingWorkspaceRegisters k layout next
  oddMap : next.nr 56 = original.nr 31
  stageLimit : next.nr 31 = 6 * k + 1
  stageZero : next.nr 32 = 0
  stageActive : next.nr 33 = 1
  stageOne : next.nr 34 = 1
  outerOne : next.nr 41 = 1
  count : next.nr 42 = 0
  parity : next.nr 70 = 0
  zero : next.nr 66 = 0
  candidateCount : next.nr 61 = 3 * k
  selectorCount : next.nr 8 = 3 * k
  selectorBases : next.nr 3 = layout.identifiers ∧ next.nr 4 = layout.slacks ∧ next.nr 5 = layout.rates
  selectorInit : next.nr 1 = 0 ∧ next.nr 9 = 1
  natural : next.nm = original.nm
  real : next.rm = original.rm
  inputReg : ∀ r ∈ [20, 21, 26, 63, 64], next.nr r = original.nr r
  saved : ∀ r ≥ 100, next.nr r = original.nr r

set_option maxHeartbeats 1000000 in
theorem allocateMatchingWorkspaceBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns allocateMatchingWorkspaceBlock 33 s t ∧ t.halted = false ∧
      MatchingWorkspaceStart (s.nr 32) (MatchingWorkspace.allocate (s.nr 32) (s.nr 63) (s.nr 64)) s t := by
  let t := (arithmeticStep allocateMatchingWorkspaceBlock)^[33] s
  have ready : t.halted = false := by
    simp [t, allocateMatchingWorkspaceBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = allocateMatchingWorkspaceBlock.length := by
    simp [t, allocateMatchingWorkspaceBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_⟩
  constructor
  · constructor <;> simp [t, allocateMatchingWorkspaceBlock, MatchingWorkspace.allocate, arithmeticStep,
      entry, running, Function.iterate_succ_apply'] <;> omega
  case inputReg =>
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp [t, allocateMatchingWorkspaceBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  case saved =>
    intro r high
    apply arithmeticRun_keeps_high_register _ s 33
    simp [allocateMatchingWorkspaceBlock, naturalDestination] <;> omega
  all_goals
    simp [t, allocateMatchingWorkspaceBlock, MatchingWorkspace.allocate, arithmeticStep,
      entry, running, Function.iterate_succ_apply'] <;> omega


end VehicleRoutingSurvey.Routing
end RppSource_MatchingWorkspace

/-! matching/MatchingVertexStart.lean -/
section RppSource_MatchingVertexStart
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing





structure MatchingVertexStart (k : ℕ) (layout : MatchingWorkspace)
    (original result : ArithmeticState) : Prop where
  mates : ∀ v : Fin k, result.nm (layout.mates + v.val) = k
  forest : AlternatingForestMemory
    (resetAlternatingForest Finset.univ (fun _ : Fin k => none)) layout.roles result.nm
  representatives : ∀ v : Fin k, result.nm (layout.representatives + v.val) = v.val
  identifiers : ∀ v : Fin k, result.nm (layout.identifiers + v.val) = 0
  potentials : ∀ v : Fin k, result.rm (layout.potentials + v.val) = 0
  count : result.nr 42 = k / 2
  parity : result.nr 70 = k % 2
  register : ∀ r, r ≠ 0 → r ≠ 42 → r ≠ 65 → r ≠ 70 → result.nr r = original.nr r
  natural : ∀ a < layout.mates, result.nm a = original.nm a
  real : ∀ a < layout.potentials, result.rm a = original.rm a

private structure VertexStartInvariant (k natBase realBase : ℕ)
    (original : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  pc : s.pc = 0
  running : s.halted = false
  vertex : s.nr 65 = i
  count : s.nr 42 = i / 2
  parity : s.nr 70 = i % 2
  register : ∀ r, r ≠ 0 → r ≠ 42 → r ≠ 65 → r ≠ 70 → s.nr r = original.nr r
  mates : ∀ j < i, s.nm (natBase + j) = k
  roles : ∀ j < i, s.nm (natBase + k + j) = 1
  parents : ∀ j < i, s.nm (natBase + k + k + j) = k
  depths : ∀ j < i, s.nm (natBase + k + k + k + j) = 0
  representatives : ∀ j < i, s.nm (natBase + k + k + k + k + j) = j
  identifiers : ∀ j < i, s.nm (natBase + k + k + k + k + k + j) = 0
  potentials : ∀ j < i, s.rm (realBase + j) = 0
  natural : ∀ a < natBase, s.nm a = original.nm a
  real : ∀ a < realBase, s.rm a = original.rm a

set_option maxHeartbeats 1300000 in
private theorem initializeMatchingVertexCell_correct {k natBase realBase i : ℕ}
    {original s : ArithmeticState} (hi : i < k)
    (workspace : MatchingWorkspaceRegisters k (MatchingWorkspace.allocate k natBase realBase) original)
    (one : original.nr 34 = 1) (zero : original.nr 66 = 0)
    (before : VertexStartInvariant k natBase realBase original i s) :
    ∃ t, BlockRuns initializeMatchingVertexCell 17 s t ∧ t.halted = false ∧
      VertexStartInvariant k natBase realBase original (i + 1)
        {t with pc := 0, nr := Function.update t.nr 65 (t.nr 65 + t.nr 34)} := by
  have dimension : s.nr 55 = k := (before.register 55 (by decide) (by decide) (by decide) (by decide)).trans workspace.dimension
  have oneAt : s.nr 34 = 1 := (before.register 34 (by decide) (by decide) (by decide) (by decide)).trans one
  have zeroAt : s.nr 66 = 0 := (before.register 66 (by decide) (by decide) (by decide) (by decide)).trans zero
  have mateBase : s.nr 50 = natBase := (before.register 50 (by decide) (by decide) (by decide) (by decide)).trans workspace.mates
  have roleBase : s.nr 51 = natBase + k := (before.register 51 (by decide) (by decide) (by decide) (by decide)).trans workspace.roles
  have parentBase : s.nr 52 = natBase + k + k := (before.register 52 (by decide) (by decide) (by decide) (by decide)).trans workspace.parents
  have depthBase : s.nr 53 = natBase + k + k + k := (before.register 53 (by decide) (by decide) (by decide) (by decide)).trans workspace.depths
  have repBase : s.nr 57 = natBase + k + k + k + k := (before.register 57 (by decide) (by decide) (by decide) (by decide)).trans workspace.representatives
  have idBase : s.nr 58 = natBase + k + k + k + k + k := (before.register 58 (by decide) (by decide) (by decide) (by decide)).trans workspace.identifiers
  have potentialBase : s.nr 62 = realBase := (before.register 62 (by decide) (by decide) (by decide) (by decide)).trans workspace.potentials
  let t := (arithmeticStep initializeMatchingVertexCell)^[17] s
  let next := {t with pc := 0, nr := Function.update t.nr 65 (t.nr 65 + t.nr 34)}
  have ready : t.halted = false := by
    simp [t, initializeMatchingVertexCell, arithmeticStep, before.pc, before.running,
      Function.iterate_succ_apply']
  have exit : t.pc = initializeMatchingVertexCell.length := by
    simp [t, initializeMatchingVertexCell, arithmeticStep, before.pc, before.running,
      Function.iterate_succ_apply']
  have nextCount : i / 2 + i % 2 = (i + 1) / 2 := by omega
  have nextParity : 1 - i % 2 = (i + 1) % 2 := by omega
  have naturalMemory : next.nm = Function.update
      (Function.update (Function.update (Function.update (Function.update
        (Function.update s.nm (natBase + i) k) (natBase + k + i) 1)
        (natBase + k + k + i) k) (natBase + k + k + k + i) 0)
        (natBase + k + k + k + k + i) i) (natBase + k + k + k + k + k + i) 0 := by
    simp [next, t, initializeMatchingVertexCell, arithmeticStep, before.pc, before.running,
      Function.iterate_succ_apply', before.vertex, dimension, oneAt, zeroAt, mateBase, roleBase,
      parentBase, depthBase, repBase, idBase]
  have realMemory : next.rm = Function.update s.rm (realBase + i) 0 := by
    simp [next, t, initializeMatchingVertexCell, arithmeticStep, before.pc, before.running,
      Function.iterate_succ_apply', before.vertex, potentialBase]
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready,
    show VertexStartInvariant k natBase realBase original (i + 1) next from ?_⟩
  constructor
  · rfl
  · exact ready
  · simp [next, t, initializeMatchingVertexCell, arithmeticStep, before.pc, before.running,
      Function.iterate_succ_apply', before.vertex, oneAt]
  · simp [next, t, initializeMatchingVertexCell, arithmeticStep, before.pc, before.running,
      Function.iterate_succ_apply', before.count, before.parity, nextCount]
  · simp [next, t, initializeMatchingVertexCell, arithmeticStep, before.pc, before.running,
      Function.iterate_succ_apply', before.parity, oneAt, nextParity]
  · intro r h0 h42 h65 h70
    simp [next, t, initializeMatchingVertexCell, arithmeticStep, before.pc, before.running,
      Function.iterate_succ_apply', Function.update_apply, h0, h42, h65, h70,
      before.register r h0 h42 h65 h70]
  case mates =>
    intro j hj
    obtain hj | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)
    · simp (disch := omega) [naturalMemory, Function.update_apply, before.mates j hj]
    · simp (disch := omega) [naturalMemory, Function.update_apply]
  case roles =>
    intro j hj
    obtain hj | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)
    · simp (disch := omega) [naturalMemory, Function.update_apply, before.roles j hj]
    · simp (disch := omega) [naturalMemory, Function.update_apply]
  case parents =>
    intro j hj
    obtain hj | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)
    · simp (disch := omega) [naturalMemory, Function.update_apply, before.parents j hj]
    · simp (disch := omega) [naturalMemory, Function.update_apply]
  case depths =>
    intro j hj
    obtain hj | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)
    · simp (disch := omega) [naturalMemory, Function.update_apply, before.depths j hj]
    · simp (disch := omega) [naturalMemory, Function.update_apply]
  case representatives =>
    intro j hj
    obtain hj | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)
    · simp (disch := omega) [naturalMemory, Function.update_apply, before.representatives j hj]
    · simp (disch := omega) [naturalMemory, Function.update_apply]
  case identifiers =>
    intro j hj
    obtain hj | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)
    · simp (disch := omega) [naturalMemory, Function.update_apply, before.identifiers j hj]
    · simp (disch := omega) [naturalMemory, Function.update_apply]
  case potentials =>
    intro j hj
    obtain hj | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)
    · simp (disch := omega) [realMemory, Function.update_apply, before.potentials j hj]
    · simp [realMemory]
  case natural =>
    intro a ha
    simp (disch := omega) [naturalMemory, Function.update_apply, before.natural a ha]
  case real =>
    intro a ha
    simp (disch := omega) [realMemory, Function.update_apply, before.real a ha]

theorem initializeMatchingVerticesBlock_correct {k natBase realBase : ℕ} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false)
    (workspace : MatchingWorkspaceRegisters k (MatchingWorkspace.allocate k natBase realBase) s)
    (one : s.nr 34 = 1) (zero : s.nr 66 = 0) (count : s.nr 42 = 0) (parity : s.nr 70 = 0) :
    ∃ t, BlockRuns initializeMatchingVerticesBlock (20 * k + 2) s t ∧ t.halted = false ∧
      MatchingVertexStart k (MatchingWorkspace.allocate k natBase realBase) s t := by
  let inv := VertexStartInvariant k natBase realBase s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 65 0} := by
    constructor
    · rfl
    · exact running
    · simp
    · simpa using count
    · simpa using parity
    · intro r _ _ different _
      simp [different]
    all_goals simp
  obtain ⟨last, finished, run⟩ := countedLoopFromZero_correct 34 65 55 k 17
    initializeMatchingVertexCell inv entry running initial
    (fun i t h => ⟨h.pc, h.running, h.vertex,
      (h.register 55 (by decide) (by decide) (by decide) (by decide)).trans workspace.dimension⟩)
    (fun _ hi _ h => initializeMatchingVertexCell_correct hi workspace one zero h)
  let final := relocateState 1
    {last with pc := (countedLoop 34 65 55 initializeMatchingVertexCell).length}
  refine ⟨final, ?_, finished.running, ?_⟩
  · simpa [final, initializeMatchingVerticesBlock, Nat.mul_comm 20, Nat.add_comm 1, Nat.add_assoc] using run
  constructor
  · exact fun v => finished.mates v.val v.isLt
  · intro v
    change _ = _ ∧ _ = _ ∧ _ = _
    simp [resetAlternatingForest, MatchingWorkspace.allocate,
      final, relocateState, finished.roles v.val v.isLt, finished.parents v.val v.isLt,
      finished.depths v.val v.isLt]
    exact ⟨rfl, rfl⟩
  · exact fun v => finished.representatives v.val v.isLt
  · exact fun v => finished.identifiers v.val v.isLt
  · exact fun v => finished.potentials v.val v.isLt
  · exact finished.count
  · exact finished.parity
  · exact finished.register
  · exact finished.natural
  · exact finished.real




end VehicleRoutingSurvey.Routing
end RppSource_MatchingVertexStart

/-! matching/MatchingSeedRow.lean -/
section RppSource_MatchingSeedRow
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

/-- Code zero means that the prefix contains only the diagonal or is empty.
Otherwise the code is the column plus one, and the score is its actual cost. -/
def MatchingSeedMinimum (row seen : ℕ) (cost : ℕ → ℝ) (code : ℕ) (score : ℝ) : Prop :=
  (code = 0 ∧ ∀ col < seen, col = row) ∨
  ∃ j, j < seen ∧ j ≠ row ∧ code = j + 1 ∧ score = cost j ∧
    ∀ col < seen, col ≠ row → score ≤ cost col

private theorem MatchingSeedMinimum.extend {row seen oldCode newCode : ℕ}
    {cost : ℕ → ℝ} {oldScore newScore : ℝ}
    (before : MatchingSeedMinimum row seen cost oldCode oldScore)
    (choose : seen ≠ row ∧ (oldCode = 0 ∨ cost seen < oldScore) →
      newCode = seen + 1 ∧ newScore = cost seen)
    (keep : ¬ (seen ≠ row ∧ (oldCode = 0 ∨ cost seen < oldScore)) →
      newCode = oldCode ∧ newScore = oldScore) :
    MatchingSeedMinimum row (seen + 1) cost newCode newScore := by
  classical
  by_cases replace : seen ≠ row ∧ (oldCode = 0 ∨ cost seen < oldScore)
  · obtain ⟨code, score⟩ := choose replace
    refine Or.inr ⟨seen, by omega, replace.1, code, score, ?_⟩
    intro col hcol offDiagonal
    obtain earlier | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hcol)
    · rcases before with ⟨_, none⟩ | ⟨j, _, _, positive, _, least⟩
      · exact False.elim (offDiagonal (none col earlier))
      · have smaller := replace.2.resolve_left (by omega)
        rw [score]
        exact smaller.le.trans (least col earlier offDiagonal)
    · exact score.le
  · obtain ⟨rfl, rfl⟩ := keep replace
    rcases before with ⟨empty, none⟩ | ⟨j, hj, distinct, code, score, least⟩
    · refine Or.inl ⟨empty, fun col hcol => ?_⟩
      obtain earlier | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hcol)
      · exact none col earlier
      · exact not_not.mp (fun different => replace ⟨different, Or.inl empty⟩)
    · refine Or.inr ⟨j, by omega, distinct, code, score, fun col hcol offDiagonal => ?_⟩
      obtain earlier | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hcol)
      · exact least col earlier offDiagonal
      · exact le_of_not_gt (fun better => replace ⟨offDiagonal, Or.inr better⟩)





private theorem loadMatchingSeedCandidate_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 34 = 1) :
    ∃ t steps, steps ≤ 6 ∧ BlockRuns loadMatchingSeedCandidate steps s t ∧ t.halted = false ∧
      t.nr 0 = (if s.nr 73 = s.nr 72 then 0 else s.nr 73 + 1) ∧
      t.nr 1 = s.nr 1 ∧ t.rr 1 = s.rr 1 ∧ t.rr 0 = s.rm (s.nr 71 + s.nr 73) ∧
      t.nm = s.nm ∧ t.rm = s.rm := by
  rcases lt_trichotomy (s.nr 73) (s.nr 72) with below | equal | above
  · let t := (arithmeticStep loadMatchingSeedCandidate)^[4] s
    have no := not_le.mpr below
    have diff := below.ne
    have ready : t.halted = false := by
      simp [t, loadMatchingSeedCandidate, arithmeticStep, entry, running, Function.iterate_succ_apply', no]
    have exit : t.pc = loadMatchingSeedCandidate.length := by
      simp [t, loadMatchingSeedCandidate, arithmeticStep, entry, running, Function.iterate_succ_apply', no]
    refine ⟨t, 4, by decide, BlockRuns.of_running_exit rfl ready exit, ready, ?_⟩
    simp [t, loadMatchingSeedCandidate, arithmeticStep, entry, running, Function.iterate_succ_apply', no, one, diff]
  · let t := (arithmeticStep loadMatchingSeedCandidate)^[6] s
    have ready : t.halted = false := by
      simp [t, loadMatchingSeedCandidate, arithmeticStep, entry, running, Function.iterate_succ_apply', equal]
    have exit : t.pc = loadMatchingSeedCandidate.length := by
      simp [t, loadMatchingSeedCandidate, arithmeticStep, entry, running, Function.iterate_succ_apply', equal]
    refine ⟨t, 6, le_rfl, BlockRuns.of_running_exit rfl ready exit, ready, ?_⟩
    simp [t, loadMatchingSeedCandidate, arithmeticStep, entry, running, Function.iterate_succ_apply', equal]
  · let t := (arithmeticStep loadMatchingSeedCandidate)^[5] s
    have no := not_le.mpr above
    have diff := above.ne'
    have ready : t.halted = false := by
      simp [t, loadMatchingSeedCandidate, arithmeticStep, entry, running, Function.iterate_succ_apply', above.le, no]
    have exit : t.pc = loadMatchingSeedCandidate.length := by
      simp [t, loadMatchingSeedCandidate, arithmeticStep, entry, running, Function.iterate_succ_apply', above.le, no]
    refine ⟨t, 5, by decide, BlockRuns.of_running_exit rfl ready exit, ready, ?_⟩
    simp [t, loadMatchingSeedCandidate, arithmeticStep, entry, running, Function.iterate_succ_apply', above.le, no, one, diff]

private theorem considerMatchingSeedCandidate_keeps {s t : ArithmeticState} {steps : ℕ}
    (run : BlockRuns considerMatchingSeedCandidate steps s t) {r : ℕ} (high : 3 ≤ r) :
    t.nr r = s.nr r := by
  rw [← run.run]
  apply arithmeticRun_keeps_high_register _ s steps
  simp [considerMatchingSeedCandidate, appendBlock, loadMatchingSeedCandidate,
    mergeSlackEntryBlock, relocateInstruction, naturalDestination] <;> omega

private theorem considerMatchingSeedCandidate_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 34 = 1)
    (before : MatchingSeedMinimum (s.nr 72) (s.nr 73) (fun j => s.rm (s.nr 71 + j)) (s.nr 1) (s.rr 1)) :
    ∃ t steps, steps ≤ 13 ∧ BlockRuns considerMatchingSeedCandidate steps s t ∧ t.halted = false ∧
      MatchingSeedMinimum (s.nr 72) (s.nr 73 + 1) (fun j => s.rm (s.nr 71 + j)) (t.nr 1) (t.rr 1) ∧
      t.nm = s.nm ∧ t.rm = s.rm := by
  obtain ⟨middle, loadSteps, loadBound, read, live, code, oldCode, oldScore, score, natural, real⟩ :=
    loadMatchingSeedCandidate_correct entry running one
  let input := {middle with pc := 0}
  obtain ⟨mergeSteps, mergeBound, merge, choose, keep, natMemory, realMemory⟩ :=
    mergeSlackEntryBlock_spec input rfl live
  have liveMerge := no_halt_from_running (s := input) live merge.inside (by simp [mergeSlackEntryBlock])
  have selected : mergeSlackEntryTakesCandidate input ↔
      s.nr 73 ≠ s.nr 72 ∧ (s.nr 1 = 0 ∨ s.rm (s.nr 71 + s.nr 73) < s.rr 1) := by
    by_cases diagonal : s.nr 73 = s.nr 72 <;>
      simp [mergeSlackEntryTakesCandidate, input, code, oldCode, oldScore, score, diagonal]
  refine ⟨_, loadSteps + mergeSteps, by omega, read.append merge, liveMerge,
    before.extend ?_ ?_, natMemory.trans natural, realMemory.trans real⟩
  · intro replacing
    simpa [input, code, replacing.1, score, relocateState] using choose (selected.mpr replacing)
  · intro keeping
    simpa [input, oldCode, oldScore, relocateState] using keep (fun selected' => keeping (selected.mp selected'))

private structure MatchingSeedRowInvariant (base row k : ℕ) (original : ArithmeticState)
    (seen : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  rowBase : s.nr 71 = base
  rowIndex : s.nr 72 = row
  column : s.nr 73 = seen
  dimension : s.nr 55 = k
  one : s.nr 34 = 1
  best : MatchingSeedMinimum row seen (fun j => original.rm (base + j)) (s.nr 1) (s.rr 1)
  registers : ∀ r, 3 ≤ r → r ≠ 73 → s.nr r = original.nr r
  natural : s.nm = original.nm
  real : s.rm = original.rm





theorem findMatchingSeedRowBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 34 = 1) :
    let row := s.nr 72
    let k := s.nr 55
    let base := s.nr 20 + s.nm (s.nr 21 + row)
    ∃ t steps, steps ≤ 16 * k + 6 ∧ BlockRuns findMatchingSeedRowBlock steps s t ∧
      t.halted = false ∧ MatchingSeedMinimum row k (fun j => s.rm (base + j)) (t.nr 1) (t.rr 1) ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧
      ∀ r, 3 ≤ r → r ≠ 71 → r ≠ 73 → t.nr r = s.nr r := by
  intro row k base
  let initialized := (arithmeticStep startMatchingSeedRow)^[4] s
  have initializedResult : initialized = {s with
      pc := 4
      nr := Function.update (Function.update s.nr 71 base) 1 0} := by
    simp [initialized, startMatchingSeedRow, arithmeticStep, entry, running, Function.iterate_succ_apply',
      Function.update_idem, base, row]
  have head : BlockRuns startMatchingSeedRow 4 s initialized :=
    BlockRuns.of_running_exit rfl (by rw [initializedResult]; exact running) (by rw [initializedResult]; rfl)
  let input := {initialized with pc := 0}
  let inv := MatchingSeedRowInvariant base row k input
  have inputLive : input.halted = false := by simp [input, initializedResult, running]
  have initial : inv 0 {input with pc := 0, nr := Function.update input.nr 73 0} := by
    constructor
    · rfl
    · exact inputLive
    · simp [input, initializedResult]
    · simp [input, initializedResult, row]
    · simp
    · simp [input, initializedResult, k]
    · simp [input, initializedResult, one]
    · left
      simp [input, initializedResult]
    · intro r high diff
      simp [diff]
    · rfl
    · rfl
  have iterate (i : ℕ) (_ : i < k) (m : ArithmeticState) (hm : inv i m) :
      ∃ t steps, steps ≤ 13 ∧ BlockRuns considerMatchingSeedCandidate steps m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 73 (t.nr 73 + t.nr 34)} := by
    have best : MatchingSeedMinimum (m.nr 72) (m.nr 73) (fun j => m.rm (m.nr 71 + j)) (m.nr 1) (m.rr 1) := by
      simpa [hm.rowIndex, hm.column, hm.rowBase, hm.real] using hm.best
    obtain ⟨t, steps, bound, run, live, chosen, natural, real⟩ :=
      considerMatchingSeedCandidate_correct hm.entry hm.running hm.one best
    have fixed : ∀ r, 3 ≤ r → t.nr r = m.nr r := fun r high => considerMatchingSeedCandidate_keeps run high
    refine ⟨t, steps, bound, run, live, ?_⟩
    constructor
    · rfl
    · exact live
    · simpa using (fixed 71 (by decide)).trans hm.rowBase
    · simpa using (fixed 72 (by decide)).trans hm.rowIndex
    · simp [fixed 73 (by decide), fixed 34 (by decide), hm.column, hm.one]
    · simpa using (fixed 55 (by decide)).trans hm.dimension
    · simpa using (fixed 34 (by decide)).trans hm.one
    · simpa [hm.rowIndex, hm.column, hm.rowBase, hm.real] using chosen
    · intro r high diff
      simpa [diff] using (fixed r high).trans (hm.registers r high diff)
    · exact natural.trans hm.natural
    · exact real.trans hm.real
  obtain ⟨last, bodySteps, done, bound, loop⟩ := countedLoopFromZero_bounded 34 73 55 k 13
    considerMatchingSeedCandidate inv rfl inputLive initial
    (fun _ _ h => ⟨h.entry, h.running, h.column, h.dimension⟩) iterate
  refine ⟨_, 4 + bodySteps, by omega, head.append loop, done.running, ?_, ?_, ?_, ?_⟩
  · simpa [relocateState, input, initializedResult] using done.best
  · simpa [relocateState, input, initializedResult] using done.natural
  · simpa [relocateState, input, initializedResult] using done.real
  · intro r high notBase notColumn
    have notBest : r ≠ 1 := by omega
    simpa [relocateState, input, initializedResult, notBase, notBest] using done.registers r high notColumn


end VehicleRoutingSurvey.Routing
end RppSource_MatchingSeedRow

/-! matching/MatchingSeedCache.lean -/
section RppSource_MatchingSeedCache
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

private noncomputable def initialSlackRecord {n : ℕ} (c : Fin n → Fin n → ℝ) (e : Sym2 (Fin n)) :
    DualSlack (MatchingDualEvent n) :=
  ⟨.edge e, edgeCost c e - oddCutDualEdgeValue ∅ (fun _ => 0) (fun _ => 0) e,
    oddCutDualEdgeValue ∅ (fun _ => 1) (fun _ => 0) e⟩

private theorem initialSlackRecord_mk {n : ℕ} {c : Fin n → Fin n → ℝ}
    (symmetric : ∀ u v, c u v = c v u) {u v : Fin n} (different : u ≠ v) :
    initialSlackRecord c s(u, v) = ⟨.edge s(u, v), c u v, 2⟩ := by
  have costEq : edgeCost c s(u, v) = c u v := by
    change (c u v + c v u) / 2 = c u v
    rw [symmetric v u]
    ring
  norm_num [initialSlackRecord, oddCutDualEdgeValue_mk, different, costEq]

/-- All singleton roots are outer. One least off-diagonal edge per vertex covers every
positive-rate edge constraint at the first dual step. -/
theorem singletonEdgeSlackCache {n : ℕ} {c : Fin n → Fin n → ℝ}
    (symmetric : ∀ u v, c u v = c v u) (edges : List (Sym2 (Fin n)))
    (proper : ∀ e ∈ edges, ¬ e.IsDiag) (complete : ∀ u v : Fin n, u ≠ v → s(u, v) ∈ edges)
    (other : Fin n → Fin n) (distinct : ∀ u, u ≠ other u)
    (least : ∀ u v, u ≠ v → c u (other u) ≤ c u v) :
    DualSlackCache (matchingDualSlacks c edges ∅ (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ => 0))
      (List.ofFn fun u => (⟨.edge s(u, other u), c u (other u), 2⟩ : DualSlack (MatchingDualEvent n))) := by
  have canonical (u v : Fin n) (different : u ≠ v) :
      (⟨.edge s(u, v), c u v, 2⟩ : DualSlack (MatchingDualEvent n)) ∈
        matchingDualSlacks c edges ∅ (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ => 0) := by
    rw [← initialSlackRecord_mk symmetric different]
    dsimp only [matchingDualSlacks]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨s(u, v), complete u v different, rfl⟩)
  constructor
  · intro row contained
    obtain ⟨u, rfl⟩ := List.mem_ofFn.mp contained
    exact canonical u (other u) (distinct u)
  · intro row contained _
    have input : row ∈ edges.map (initialSlackRecord c) := by
      rw [matchingDualSlacks, Finset.toList_empty, List.map_nil, List.append_nil] at contained
      change row ∈ edges.map (initialSlackRecord c) at contained
      exact contained
    obtain ⟨edge, present, rfl⟩ := List.mem_map.mp input
    induction edge using Sym2.inductionOn with
    | hf u v =>
      have different : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using proper s(u, v) present
      refine ⟨⟨.edge s(u, other u), c u (other u), 2⟩, List.mem_ofFn.mpr ⟨u, rfl⟩, ?_, ?_⟩
      · rw [initialSlackRecord_mk symmetric different]
      · rw [initialSlackRecord_mk symmetric different]
        exact least u v different





theorem storeMatchingSeedRowBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1) :
    let i := s.nr 72
    let address := s.nr 54 + 2 * i
    ∃ t, BlockRuns storeMatchingSeedRowBlock 19 s t ∧ t.halted = false ∧
      t.nm = Function.update (Function.update (Function.update s.nm (s.nr 58 + i) (i + 1))
        address i) (address + 1) (s.nr 1 - 1) ∧
      t.rm = Function.update (Function.update s.rm (s.nr 59 + i) (s.rr 1)) (s.nr 60 + i) 2 ∧
      ∀ r, r ∉ [6, 10, 14, 15, 16, 18] → r ≠ 0 → t.nr r = s.nr r := by
  intro i address
  let ready := {s with
    pc := 7
    nr := Function.update (Function.update (Function.update (Function.update s.nr 14 0)
      18 i) 15 i) 16 (s.nr 1 - 1)
    rr := Function.update (Function.update (Function.update s.rr 3 0) 0 (s.rr 1)) 4 2}
  have head : BlockRuns prepareMatchingSeedStore 7 s ready := by
    refine BlockRuns.of_running_exit ?_ (show ready.halted = false from running) rfl
    simp [ready, prepareMatchingSeedStore, arithmeticStep, entry, running, one, i, Function.iterate_succ_apply']
  let input := {ready with pc := 0}
  have oneAt : input.nr 9 = 1 := by simpa [input, ready] using one
  obtain ⟨write, live, natural, real⟩ := storeMatchingCandidateCell_spec input rfl running oneAt
  have run := head.append write
  refine ⟨_, run, live, ?_, ?_, ?_⟩
  · simpa [input, ready, relocateState, installedMatchingCandidateNat, address, Nat.two_mul] using natural
  · simpa [input, ready, relocateState, installedMatchingCandidateReal] using real
  · intro r away nonzero
    rw [← run.run]
    apply arithmeticRun_keeps_register _ s 19
    simp [storeMatchingSeedRowBlock, appendBlock, prepareMatchingSeedStore,
      storeMatchingCandidateCell, relocateInstruction, naturalDestination] at away ⊢
    omega



/-- An occupied initial event slot contains a minimizer from that vertex's metric row. -/
structure MatchingSeedEntry (k row ids ends slacks rates : ℕ) (cost : ℕ → ℝ)
    (s : ArithmeticState) (column : ℕ) : Prop where
  within : column < k
  distinct : column ≠ row
  least : ∀ j < k, j ≠ row → cost column ≤ cost j
  identifier : s.nm (ids + row) = row + 1
  source : s.nm (ends + 2 * row) = row
  target : s.nm (ends + 2 * row + 1) = column
  slack : s.rm (slacks + row) = cost column
  rate : s.rm (rates + row) = 2

private theorem buildMatchingSeedRow_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 34 = 1) (oneAlt : s.nr 9 = 1)
    (atLeastTwo : 2 ≤ s.nr 55) (rowIn : s.nr 72 < s.nr 55)
    (dictAfter : s.nr 58 + s.nr 55 ≤ s.nr 54) (ratesAfter : s.nr 59 + s.nr 55 ≤ s.nr 60) :
    let row := s.nr 72
    let k := s.nr 55
    let cost := fun j => s.rm (s.nr 20 + s.nm (s.nr 21 + row) + j)
    ∃ t steps col, steps ≤ 16 * k + 25 ∧ BlockRuns buildMatchingSeedRow steps s t ∧ t.halted = false ∧
      MatchingSeedEntry k row (s.nr 58) (s.nr 54) (s.nr 59) (s.nr 60) cost t col ∧
      (∀ r, 3 ≤ r → r ∉ [6, 10, 14, 15, 16, 18, 71, 73] → t.nr r = s.nr r) ∧
      (∀ a, a ≠ s.nr 58 + row → a ≠ s.nr 54 + 2 * row → a ≠ s.nr 54 + 2 * row + 1 → t.nm a = s.nm a) ∧
      ∀ a, a ≠ s.nr 59 + row → a ≠ s.nr 60 + row → t.rm a = s.rm a := by
  intro row k cost
  obtain ⟨m, pickedSteps, pickedBudget, picked, live, best, nm, rm, regs⟩ :=
    findMatchingSeedRowBlock_correct entry running one
  have hit : ∃ col, col < k ∧ col ≠ row ∧ m.nr 1 = col + 1 ∧ m.rr 1 = cost col ∧
      ∀ j < k, j ≠ row → cost col ≤ cost j := by
    rcases best with ⟨_, empty⟩ | ⟨col, within, different, code, score, least⟩
    · by_cases zero : row = 0
      · have impossible := empty 1 (by omega)
        omega
      · exact (zero (empty 0 (by omega)).symm).elim
    · exact ⟨col, within, different, code, score, fun j hj different => by
        simpa only [score] using least j hj different⟩
  obtain ⟨col, within, different, codeAt, scoreAt, least⟩ := hit
  let input := {m with pc := 0}
  have inReg (r : ℕ) (small : 3 ≤ r := by decide) (notBase : r ≠ 71 := by decide)
      (notCol : r ≠ 73 := by decide) : input.nr r = s.nr r := regs r small notBase notCol
  have nextOne : input.nr 9 = 1 := (inReg 9).trans oneAlt
  obtain ⟨last, wrote, ready, writesNat, writesReal, fixed⟩ :=
    storeMatchingSeedRowBlock_correct (s := input) rfl live nextOne
  have rowAt : input.nr 72 = row := inReg 72
  have code : input.nr 1 - 1 = col := by change m.nr 1 - 1 = col; rw [codeAt]; omega
  have score : input.rr 1 = cost col := scoreAt
  simp only [rowAt, inReg 54, inReg 58, inReg 59, inReg 60, code, score] at writesNat writesReal
  rw [show input.nm = s.nm from nm] at writesNat
  rw [show input.rm = s.rm from rm] at writesReal
  let t := relocateState findMatchingSeedRowBlock.length last
  have natMem : t.nm = last.nm := rfl
  have realMem : t.rm = last.rm := rfl
  refine ⟨t, pickedSteps + 19, col, by omega, picked.append wrote, ready, ?_, ?_, ?_, ?_⟩
  · refine ⟨within, different, least, ?_, ?_, ?_, ?_, ?_⟩
    · have first : s.nr 58 + row ≠ s.nr 54 + 2 * row := by omega
      have second : s.nr 58 + row ≠ s.nr 54 + 2 * row + 1 := by omega
      simp [natMem, writesNat, Function.update_apply, first, second]
    · simp (disch := omega) [natMem, writesNat, Function.update_apply]
    · simp [natMem, writesNat]
    · have notRate : s.nr 59 + row ≠ s.nr 60 + row := by omega
      have differentBases : s.nr 59 ≠ s.nr 60 := by omega
      simp [realMem, writesReal, Function.update_apply, notRate, differentBases]
    · simp [realMem, writesReal]
  · intro r large avoid
    have notBase : r ≠ 71 := fun equal => avoid (by simp [equal])
    have notCol : r ≠ 73 := fun equal => avoid (by simp [equal])
    have notWritten : r ∉ [6, 10, 14, 15, 16, 18] :=
      fun hr => avoid (List.mem_append_left [71, 73] hr)
    exact (fixed r notWritten (by omega)).trans (inReg r large notBase notCol)
  · intro a idAddr sourceAddr targetAddr
    simp [natMem, writesNat, Function.update_apply, idAddr, sourceAddr, targetAddr]
  · intro a slackAddr rateAddr
    simp [realMem, writesReal, Function.update_apply, slackAddr, rateAddr]

structure MatchingSeedCacheFrame (scanned : ℕ) (original result : ArithmeticState) : Prop where
  entries : ∀ i < scanned, ∃ j,
    MatchingSeedEntry (original.nr 55) i (original.nr 58) (original.nr 54)
      (original.nr 59) (original.nr 60)
      (fun col => original.rm (original.nr 20 + original.nr 55 * i + col)) result j
  natural : ∀ a, (a < original.nr 58 ∨ original.nr 58 + scanned ≤ a) →
    (a < original.nr 54 ∨ original.nr 54 + 2 * scanned ≤ a) → result.nm a = original.nm a
  real : ∀ a, (a < original.nr 59 ∨ original.nr 59 + scanned ≤ a) →
    (a < original.nr 60 ∨ original.nr 60 + scanned ≤ a) → result.rm a = original.rm a
  regs : ∀ r, 3 ≤ r → r ∉ [6, 10, 14, 15, 16, 18, 71, 72, 73] → result.nr r = original.nr r

private structure MatchingSeedSweepInvariant (original : ArithmeticState) (scanned : ℕ)
    (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  rowIndex : s.nr 72 = scanned
  cache : MatchingSeedCacheFrame scanned original s



set_option maxHeartbeats 650000 in
/-- Fill the first `k` selector rows and leave the remaining `2k` cells available for
later events. Only off-diagonal metric entries participate in the minimum. -/
theorem seedMatchingEventCacheBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 34 = 1) (oneAlt : s.nr 9 = 1)
    (even : s.nr 55 % 2 = 0)
    (offsetsBefore : s.nr 21 + s.nr 55 ≤ s.nr 58)
    (dictAfter : s.nr 58 + s.nr 55 ≤ s.nr 54)
    (costBefore : s.nr 20 + s.nr 55 * s.nr 55 ≤ s.nr 59)
    (ratesAfter : s.nr 59 + s.nr 55 ≤ s.nr 60)
    (offsets : ∀ i < s.nr 55, s.nm (s.nr 21 + i) = s.nr 55 * i) :
    ∃ t steps, steps ≤ s.nr 55 * (16 * s.nr 55 + 28) + 3 ∧
      BlockRuns seedMatchingEventCacheBlock steps s t ∧ t.halted = false ∧ t.nr 1 = 0 ∧
      MatchingSeedCacheFrame (s.nr 55) s t := by
  let k := s.nr 55
  let inv := MatchingSeedSweepInvariant s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 72 0} := by
    refine ⟨rfl, running, by simp, by simp, fun _ _ _ => rfl, fun _ _ _ => rfl, ?_⟩
    intro r _ away
    have different : r ≠ 72 := fun equal => away (by simp [equal])
    simp [different]
  have iterate (i : ℕ) (hi : i < k) (m : ArithmeticState) (hm : inv i m) :
      ∃ t steps, steps ≤ 16 * k + 25 ∧ BlockRuns buildMatchingSeedRow steps m t ∧
        t.halted = false ∧ inv (i + 1)
          {t with pc := 0, nr := Function.update t.nr 72 (t.nr 72 + t.nr 34)} := by
    have fixed (r : ℕ) (large : 3 ≤ r := by decide)
        (away : r ∉ [6, 10, 14, 15, 16, 18, 71, 72, 73] := by decide) := hm.cache.regs r large away
    have evenAt : k % 2 = 0 := even
    have two : 2 ≤ k := by omega
    obtain ⟨t, steps, col, budget, run, live, row, regs, natMem, realMem⟩ :=
      buildMatchingSeedRow_correct hm.entry hm.running ((fixed 34).trans one) ((fixed 9).trans oneAlt)
        (by rw [fixed 55]; exact two) (by rw [hm.rowIndex, fixed 55]; exact hi)
        (by rw [fixed 58, fixed 55, fixed 54]; exact dictAfter)
        (by rw [fixed 59, fixed 55, fixed 60]; exact ratesAfter)
    have beforeIds : s.nr 21 + i < s.nr 58 := by change i < s.nr 55 at hi; omega
    have rowOffset : m.nm (m.nr 21 + m.nr 72) = k * i := by
      rw [fixed 21, hm.rowIndex,
        hm.cache.natural _ (Or.inl beforeIds) (Or.inl (by omega)), offsets i hi]
    have allCosts (j : ℕ) (hj : j < k) :
        m.rm (s.nr 20 + k * i + j) = s.rm (s.nr 20 + k * i + j) := by
      have range := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hi)
      rw [Nat.mul_succ] at range
      have beforeSlack : s.nr 20 + k * i + j < s.nr 59 := by change s.nr 20 + k * k ≤ _ at costBefore; omega
      exact hm.cache.real _ (Or.inl beforeSlack) (Or.inl (by omega))
    rw [fixed 55] at budget
    rw [fixed 55, fixed 58, fixed 54, fixed 59, fixed 60, fixed 20, rowOffset, hm.rowIndex] at row
    rw [fixed 58, fixed 54, hm.rowIndex] at natMem
    rw [fixed 59, fixed 60, hm.rowIndex] at realMem
    let next := {t with pc := 0, nr := Function.update t.nr 72 (t.nr 72 + t.nr 34)}
    refine ⟨t, steps, budget, run, live, show inv (i + 1) next from ?_⟩
    have index := regs 72 (by decide) (by decide)
    have step := regs 34 (by decide) (by decide)
    refine ⟨rfl, live, by simp [next, index, step, hm.rowIndex, fixed 34, one], ?_⟩
    constructor
    · intro v hv
      obtain earlier | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hv)
      · obtain ⟨j, old⟩ := hm.cache.entries v earlier
        refine ⟨j, old.within, old.distinct, old.least, ?_, ?_, ?_, ?_, ?_⟩
        · exact (natMem _ (by omega) (by omega) (by omega)).trans old.identifier
        · exact (natMem _ (by omega) (by omega) (by omega)).trans old.source
        · exact (natMem _ (by omega) (by omega) (by omega)).trans old.target
        · exact (realMem _ (by omega) (by omega)).trans old.slack
        · exact (realMem _ (by omega) (by omega)).trans old.rate
      · refine ⟨col, row.within, row.distinct, ?_, row.identifier, row.source, row.target, ?_, row.rate⟩
        · intro j hj different
          rw [← allCosts col row.within, ← allCosts j hj]
          exact row.least j hj different
        · exact row.slack.trans (allCosts col row.within)
    · intro a ids ends
      exact (natMem _ (by omega) (by omega) (by omega)).trans
        (hm.cache.natural a (by omega) (by omega))
    · intro a slacks rates
      exact (realMem _ (by omega) (by omega)).trans
        (hm.cache.real a (by omega) (by omega))
    · intro r high away
      have notIndex : r ≠ 72 := fun eq => away (by simp [eq])
      have notStore : r ∉ [6, 10, 14, 15, 16, 18, 71, 73] := by
        simp at away ⊢
        omega
      simpa [next, notIndex] using (regs r high notStore).trans (fixed r high away)
  obtain ⟨last, scanSteps, done, cost, ran⟩ := countedLoopFromZero_bounded 34 72 55 k (16 * k + 25)
    buildMatchingSeedRow inv entry running initial
    (fun _ _ h => ⟨h.entry, h.running, h.rowIndex, h.cache.regs 55 (by decide) (by decide)⟩) iterate
  let middle := relocateState 1 {last with pc := (countedLoop 34 72 55 buildMatchingSeedRow).length}
  have reset := zeroRegister_runs 1 {middle with pc := 0} rfl done.running
  refine ⟨_, scanSteps + 1, ?_, ran.append reset, done.running, by simp [relocateState], ?_⟩
  · change scanSteps ≤ 1 + (k * (16 * k + 25 + 3) + 1) at cost
    change scanSteps + 1 ≤ k * (16 * k + 28) + 3
    rw [show 16 * k + 25 + 3 = 16 * k + 28 by omega] at cost
    omega
  · refine ⟨?_, done.cache.natural, done.cache.real, ?_⟩
    · intro i hi
      obtain ⟨j, row⟩ := done.cache.entries i hi
      exact ⟨j, row.within, row.distinct, row.least, row.identifier, row.source,
        row.target, row.slack, row.rate⟩
    · intro r above away
      have avoid : r ≠ 1 := by omega
      simpa [relocateState, middle, avoid] using done.cache.regs r above away

/-- The first search has no contracted blossoms. Its event identifiers decode to
original compact endpoints stored in the dictionary. -/
def decodeInitialMatchingEvent (k : ℕ) (s : ArithmeticState) (id : ℕ) :
    Option (MatchingDualEvent k) :=
  let address := s.nr 54 + 2 * (id - 1)
  if id = 0 then none
  else if u : s.nm address < k then
    if v : s.nm (address + 1) < k then
      some (.edge s(⟨s.nm address, u⟩, ⟨s.nm (address + 1), v⟩))
    else none
  else none

theorem matchingSeedEntries_validSelector {original t : ArithmeticState} {k : ℕ}
    (entries : ∀ i < k, ∃ j,
      MatchingSeedEntry (original.nr 55) i (original.nr 58) (original.nr 54)
        (original.nr 59) (original.nr 60)
        (fun col => original.rm (original.nr 20 + original.nr 55 * i + col)) t j)
    (dimension : original.nr 55 = k)
    (count : t.nr 8 = 3 * k) (idBase : t.nr 3 = original.nr 58)
    (dictionary : t.nr 54 = original.nr 54) (slackBase : t.nr 4 = original.nr 59)
    (rateBase : t.nr 5 = original.nr 60)
    (vacant : ∀ i, k ≤ i → i < 3 * k → t.nm (original.nr 58 + i) = 0) {c : Fin k → Fin k → ℝ}
    (cost : ∀ u v : Fin k, original.rm (original.nr 20 + k * u.val + v.val) = c u v)
    (symmetric : ∀ u v, c u v = c v u) (edges : List (Sym2 (Fin k)))
    (proper : ∀ e ∈ edges, ¬ e.IsDiag) (complete : ∀ u v : Fin k, u ≠ v → s(u, v) ∈ edges) :
    ∃ rows, DualBoundTable t rows (decodeInitialMatchingEvent k t) ∧
      DualSlackCache (matchingDualSlacks c edges ∅ (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ => 0))
        (rows.filterMap id) := by
  classical
  have selected (u : Fin k) : ∃ v : Fin k,
      MatchingSeedEntry k u.val (original.nr 58) (original.nr 54) (original.nr 59) (original.nr 60)
        (fun j => original.rm (original.nr 20 + k * u.val + j)) t v.val := by
    obtain ⟨j, row⟩ := entries u.val u.isLt
    rw [dimension] at row
    exact ⟨⟨j, row.within⟩, row⟩
  choose other stored using selected
  have different (u : Fin k) : u ≠ other u :=
    fun equal => (stored u).distinct (congrArg Fin.val equal.symm)
  have least (u v : Fin k) (offDiagonal : u ≠ v) : c u (other u) ≤ c u v := by
    have valNe : v.val ≠ u.val := fun eq => offDiagonal (Fin.ext eq.symm)
    simpa only [cost] using (stored u).least v.val v.isLt valNe
  let decoded (u : Fin k) : DualSlack (MatchingDualEvent k) := ⟨.edge s(u, other u), c u (other u), 2⟩
  let firstRows := List.ofFn (fun u => some (decoded u))
  let rows := firstRows ++ List.replicate (2 * k) none
  have length : rows.length = 3 * k := by simp [rows, firstRows]; omega
  refine ⟨rows, ⟨count.trans length.symm, ?_⟩, ?_⟩
  · intro i index
    by_cases hi : i < k
    · let u : Fin k := ⟨i, hi⟩
      have atRow : rows[i] = some (decoded u) := by
        change (firstRows ++ _)[i] = _
        rw [List.getElem_append_left (show i < firstRows.length by simpa [firstRows] using hi)]
        simp [firstRows, u]
      rw [atRow]
      have code : dualBoundIdentifier t i = i + 1 := by simpa [u, dualBoundIdentifier, idBase] using (stored u).identifier
      refine ⟨by omega, ?_, ?_, ?_⟩
      · have source : t.nm (t.nr 54 + 2 * i) = i := by simpa [u, dictionary] using (stored u).source
        have target : t.nm (t.nr 54 + 2 * i + 1) = (other u).val := by
          simpa [u, dictionary] using (stored u).target
        simp [decodeInitialMatchingEvent, code, source, target, hi, (other u).isLt, decoded, u]
      · rw [slackBase]
        exact (stored u).slack.trans (cost u (other u))
      · simpa only [decoded, rateBase, u] using (stored u).rate
    · have past : k ≤ i := Nat.le_of_not_gt hi
      have atRow : rows[i] = none := by
        change (firstRows ++ _)[i] = _
        rw [List.getElem_append_right (show firstRows.length ≤ i by simpa [firstRows] using past)]
        simp
      rw [atRow]
      simpa only [dualBoundIdentifier, idBase] using vacant i past (length ▸ index)
  · have flatten : rows.filterMap id = List.ofFn decoded := by
      have empty (n : ℕ) : (List.replicate n (none : Option (DualSlack (MatchingDualEvent k)))).filterMap id = [] := by
        induction n with
        | zero => rfl
        | succ n ih => simp [List.replicate_succ, ih]
      simp only [rows, List.filterMap_append, empty, List.append_nil]
      change (List.ofFn (fun u => some (decoded u))).filterMap id = _
      have mapped : List.ofFn (fun u => some (decoded u)) = (List.ofFn decoded).map some := by
        rw [List.map_ofFn] <;> rfl
      rw [mapped]
      simp [List.filterMap_map, Function.comp_def]
    rw [flatten]
    exact singletonEdgeSlackCache symmetric edges proper complete other different least


end VehicleRoutingSurvey.Routing
end RppSource_MatchingSeedCache

/-! matching/MatchingPairSeed.lean -/
section RppSource_MatchingPairSeed
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing













private def matchingPairCellResult (s : ArithmeticState) (left : ℕ) : ArithmeticState :=
  let addr := s.nr 78 + (s.nr 75 + s.nr 75)
  let score := s.rm (s.nr 77 + s.nr 75)
  let realAddr := s.nr 76 + s.nr 75
  {s with
    pc := 13
    nr := Function.update (Function.update s.nr 80 left) 79 realAddr
    rr := Function.update s.rr 16 score
    nm := Function.update (Function.update s.nm addr left) (addr + 1) (s.nr 75)
    rm := Function.update s.rm realAddr score}

set_option maxHeartbeats 600000 in
private theorem seedMatchingPairCell_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 34 = 1) (zero : s.nr 81 = 0) :
    let t := matchingPairCellResult s (if s.nr 75 = s.nr 74 then s.nr 55 else s.nr 74)
    ∃ steps ≤ 13, BlockRuns seedMatchingPairCell steps s t := by
  intro t
  rcases lt_trichotomy (s.nr 75) (s.nr 74) with below | equal | above
  · refine ⟨11, by decide, BlockRuns.of_running_exit ?_ (show t.halted = false from running) rfl⟩
    simp [t, matchingPairCellResult, seedMatchingPairCell, arithmeticStep, entry, running,
      Function.iterate_succ_apply', Function.update_idem, Function.update_comm (show (79 : ℕ) ≠ 80 by decide),
      one, zero, not_le.mpr below, below.ne]
  · refine ⟨13, le_rfl, BlockRuns.of_running_exit ?_ (show t.halted = false from running) rfl⟩
    simp [t, matchingPairCellResult, seedMatchingPairCell, arithmeticStep, entry, running,
      Function.iterate_succ_apply', Function.update_idem, Function.update_comm (show (79 : ℕ) ≠ 80 by decide),
      one, zero, equal]
  · refine ⟨12, by decide, BlockRuns.of_running_exit ?_ (show t.halted = false from running) rfl⟩
    simp [t, matchingPairCellResult, seedMatchingPairCell, arithmeticStep, entry, running,
      Function.iterate_succ_apply', Function.update_idem, Function.update_comm (show (79 : ℕ) ≠ 80 by decide),
      one, zero, above.le, not_le.mpr above, above.ne']

/-- Each row occupies adjacent endpoint pairs and one cost cell per column. -/
structure MatchingPairSeededRow (k seen i natBase realBase : ℕ) (s : ArithmeticState)
    (cost : ℕ → ℝ) : Prop where
  first : ∀ j < seen, s.nm (natBase + 2 * j) = if j = i then k else i
  second : ∀ j < seen, s.nm (natBase + 2 * j + 1) = j
  score : ∀ j < seen, s.rm (realBase + j) = cost j

private structure MatchingPairRowInvariant (k row natBase costBase realBase : ℕ)
    (original : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  column : s.nr 75 = i
  regs : ∀ r, r ≠ 75 → r ≠ 79 → r ≠ 80 → s.nr r = original.nr r
  delta : s.rr 15 = original.rr 15
  tables : MatchingPairSeededRow k i row natBase realBase s (fun j => original.rm (costBase + j))
  naturalFrame : ∀ a, a < natBase ∨ natBase + 2 * i ≤ a → s.nm a = original.nm a
  realFrame : ∀ a, a < realBase ∨ realBase + i ≤ a → s.rm a = original.rm a

private theorem seedMatchingPairRowLoop_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 34 = 1) (zero : s.nr 81 = 0)
    (disjoint : s.nr 77 + s.nr 55 ≤ s.nr 76 ∨ s.nr 76 + s.nr 55 ≤ s.nr 77) :
    let k := s.nr 55
    let row := s.nr 74
    let natBase := s.nr 78
    let costBase := s.nr 77
    let realBase := s.nr 76
    ∃ t steps, steps ≤ 16 * k + 2 ∧
      BlockRuns (countedLoopFromZero 34 75 55 seedMatchingPairCell) steps s t ∧ t.halted = false ∧
      MatchingPairSeededRow k k row natBase realBase t (fun j => s.rm (costBase + j)) ∧
      (∀ r, r ≠ 75 → r ≠ 79 → r ≠ 80 → t.nr r = s.nr r) ∧
      t.rr 15 = s.rr 15 ∧
      (∀ a, a < natBase ∨ natBase + 2 * k ≤ a → t.nm a = s.nm a) ∧
      (∀ a, a < realBase ∨ realBase + k ≤ a → t.rm a = s.rm a) := by
  intro k row natBase costBase realBase
  let inv := MatchingPairRowInvariant k row natBase costBase realBase s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 75 0} := by
    refine ⟨rfl, running, by simp, ?_, rfl, ⟨by simp, by simp, by simp⟩, fun _ _ => rfl, fun _ _ => rfl⟩
    intro r different _ _
    simp [different]
  have iterate (i : ℕ) (hi : i < k) (m : ArithmeticState) (hm : inv i m) :
      ∃ t steps, steps ≤ 13 ∧ BlockRuns seedMatchingPairCell steps m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 75 (t.nr 75 + t.nr 34)} := by
    have fixed (r : ℕ) (a : r ≠ 75 := by decide) (b : r ≠ 79 := by decide) (c : r ≠ 80 := by decide) :=
      hm.regs r a b c
    have offset : m.nr 78 = natBase := fixed 78
    have costOffset : m.nr 77 = costBase := fixed 77
    have realOffset : m.nr 76 = realBase := fixed 76
    have size : m.nr 55 = k := fixed 55
    have rowAt : m.nr 74 = row := fixed 74
    have oneAt : m.nr 34 = 1 := (fixed 34).trans one
    have zeroAt : m.nr 81 = 0 := (fixed 81).trans zero
    have inputValue : m.rm (costBase + i) = s.rm (costBase + i) := by
      apply hm.realFrame
      change costBase + k ≤ realBase ∨ realBase + k ≤ costBase at disjoint
      rcases disjoint with earlier | later
      · left; omega
      · right; omega
    let t := matchingPairCellResult m (if m.nr 75 = m.nr 74 then m.nr 55 else m.nr 74)
    obtain ⟨steps, bound, run⟩ := seedMatchingPairCell_correct hm.entry hm.running oneAt zeroAt
    refine ⟨t, steps, bound, run, hm.running, ?_⟩
    constructor
    · rfl
    · exact hm.running
    · simp [t, matchingPairCellResult, hm.column, oneAt]
    · intro r a b c
      simp [t, matchingPairCellResult, a, b, c, fixed r a b c]
    · simpa [t, matchingPairCellResult] using hm.delta
    · refine ⟨?_, ?_, ?_⟩
      · intro j hj
        obtain before | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)
        · simp (disch := omega) [t, matchingPairCellResult, hm.column, offset, Function.update_apply,
            hm.tables.first j before]
        · simp (disch := omega) [t, matchingPairCellResult, hm.column, offset, rowAt, size,
            Function.update_apply, Nat.two_mul]
      · intro j hj
        obtain before | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)
        · simp (disch := omega) [t, matchingPairCellResult, hm.column, offset, Function.update_apply,
            hm.tables.second j before]
        · simp [t, matchingPairCellResult, hm.column, offset, Nat.two_mul]
      · intro j hj
        obtain before | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)
        · simp (disch := omega) [t, matchingPairCellResult, hm.column, realOffset, Function.update_apply,
            hm.tables.score j before]
        · simp [t, matchingPairCellResult, hm.column, realOffset, costOffset, inputValue]
    · intro a ha
      have old : a < natBase ∨ natBase + 2 * i ≤ a := by omega
      simp (disch := omega) [t, matchingPairCellResult, hm.column, offset, Function.update_apply,
        hm.naturalFrame a old]
    · intro a ha
      have old : a < realBase ∨ realBase + i ≤ a := by omega
      simp (disch := omega) [t, matchingPairCellResult, hm.column, realOffset, Function.update_apply,
        hm.realFrame a old]
  obtain ⟨last, steps, done, bound, run⟩ := countedLoopFromZero_bounded 34 75 55 k 13
    seedMatchingPairCell inv entry running initial
    (fun _ _ h => ⟨h.entry, h.running, h.column, h.regs 55 (by decide) (by decide) (by decide)⟩) iterate
  exact ⟨_, steps, by omega, run, done.running, ⟨done.tables.first, done.tables.second, done.tables.score⟩,
    done.regs, done.delta, done.naturalFrame, done.realFrame⟩

private theorem seedMatchingPairRow_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 34 = 1) (zero : s.nr 81 = 0)
    (costBefore : s.nr 20 + s.nr 55 * s.nr 55 ≤ s.nr 66) (rowIn : s.nr 74 < s.nr 55)
    (offset : s.nm (s.nr 21 + s.nr 74) = s.nr 55 * s.nr 74) :
    let k := s.nr 55
    let row := s.nr 74
    let natBase := s.nr 65 + 2 * (k * row)
    let costBase := s.nr 20 + k * row
    let realBase := s.nr 66 + k * row
    ∃ t steps, steps ≤ 16 * k + 8 ∧ BlockRuns seedMatchingPairRow steps s t ∧ t.halted = false ∧
      MatchingPairSeededRow k k row natBase realBase t (fun j => s.rm (costBase + j)) ∧
      (∀ r, r < 75 ∨ 80 < r → t.nr r = s.nr r) ∧ t.rr 15 = s.rr 15 ∧
      (∀ a, a < natBase ∨ natBase + 2 * k ≤ a → t.nm a = s.nm a) ∧
      (∀ a, a < realBase ∨ realBase + k ≤ a → t.rm a = s.rm a) := by
  intro k row natBase costBase realBase
  let loaded := (arithmeticStep prepareMatchingPairRow)^[6] s
  have loadedEq : loaded = {s with
      pc := 6
      nr := Function.update (Function.update (Function.update (Function.update s.nr 76 (k * row))
        77 costBase) 78 natBase) 76 realBase} := by
    simp [loaded, prepareMatchingPairRow, arithmeticStep, entry, running, Function.iterate_succ_apply',
      Function.update_idem, offset, natBase, costBase, realBase, k, row, Nat.two_mul]
  have live : loaded.halted = false := by rw [loadedEq]; exact running
  have head : BlockRuns prepareMatchingPairRow 6 s loaded :=
    BlockRuns.of_running_exit rfl live (by rw [loadedEq]; rfl)
  let input := {loaded with pc := 0}
  have sizes : k * (row + 1) ≤ k * k := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt rowIn)
  have distinct : input.nr 77 + input.nr 55 ≤ input.nr 76 ∨ input.nr 76 + input.nr 55 ≤ input.nr 77 := by
    left
    simp [input, loadedEq]
    change costBase + k ≤ realBase
    simp only [Nat.mul_add, Nat.mul_one] at sizes
    dsimp [costBase, realBase, k, row] at sizes ⊢
    omega
  have oneAt : input.nr 34 = 1 := by simpa [input, loadedEq] using one
  have zeroAt : input.nr 81 = 0 := by simpa [input, loadedEq] using zero
  obtain ⟨t, steps, bound, run, ready, tables, regs, delta, natural, real⟩ :=
    seedMatchingPairRowLoop_correct (s := input) rfl live oneAt zeroAt distinct
  refine ⟨_, 6 + steps, ?_, head.append run, ready, ?_, ?_, ?_, ?_, ?_⟩
  · simp [input, loadedEq] at bound
    omega
  · constructor
    · simpa [input, loadedEq, relocateState] using tables.first
    · simpa [input, loadedEq, relocateState] using tables.second
    · simpa [input, loadedEq, relocateState] using tables.score
  · intro r untouched
    have a : r ≠ 75 := by omega
    have b : r ≠ 76 := by omega
    have c : r ≠ 77 := by omega
    have d : r ≠ 78 := by omega
    have e : r ≠ 79 := by omega
    have f : r ≠ 80 := by omega
    simpa [input, loadedEq, relocateState, b, c, d] using regs r a e f
  · simpa [input, loadedEq, relocateState] using delta
  · simpa [input, loadedEq, relocateState] using natural
  · simpa [input, loadedEq, relocateState] using real

private structure MatchingPairSweepInvariant (k natBase realBase : ℕ)
    (original : ArithmeticState) (row : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  rowIndex : s.nr 74 = row
  regs : ∀ r, r < 74 ∨ 80 < r → s.nr r = original.nr r
  delta : s.rr 15 = original.rr 15
  rows : ∀ i < row, MatchingPairSeededRow k k i (natBase + 2 * (k * i)) (realBase + k * i) s
    (fun j => original.rm (original.nr 20 + k * i + j))
  natural : ∀ a, a < natBase ∨ natBase + 2 * (k * row) ≤ a → s.nm a = original.nm a
  real : ∀ a, a < realBase ∨ realBase + k * row ≤ a → s.rm a = original.rm a

private theorem MatchingPairSeededRow.transfer {k scanned i natBase realBase : ℕ}
    {before after : ArithmeticState} {c d : ℕ → ℝ}
    (old : MatchingPairSeededRow k scanned i natBase realBase before c)
    (natMem : ∀ a, natBase ≤ a → a < natBase + 2 * scanned → after.nm a = before.nm a)
    (realMem : ∀ a, realBase ≤ a → a < realBase + scanned → after.rm a = before.rm a)
    (cost : ∀ j < scanned, c j = d j) : MatchingPairSeededRow k scanned i natBase realBase after d where
  first j hj := (natMem _ (by omega) (by omega)).trans (old.first j hj)
  second j hj := (natMem _ (by omega) (by omega)).trans (old.second j hj)
  score j hj := (realMem _ (by omega) (by omega)).trans ((old.score j hj).trans (cost j hj))

set_option maxHeartbeats 600000 in
private theorem seedMatchingPairSweep_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 34 = 1) (zero : s.nr 81 = 0)
    (offsetsBefore : s.nr 21 + s.nr 55 ≤ s.nr 65)
    (costBefore : s.nr 20 + s.nr 55 * s.nr 55 ≤ s.nr 66)
    (offsets : ∀ i < s.nr 55, s.nm (s.nr 21 + i) = s.nr 55 * i) :
    ∃ t steps, steps ≤ s.nr 55 * (16 * s.nr 55 + 11) + 2 ∧
      BlockRuns (countedLoopFromZero 34 74 55 seedMatchingPairRow) steps s t ∧ t.halted = false ∧
      t.rr 15 = s.rr 15 ∧ (∀ r, r < 74 ∨ 80 < r → t.nr r = s.nr r) ∧
      (∀ i < s.nr 55, MatchingPairSeededRow (s.nr 55) (s.nr 55) i
        (s.nr 65 + 2 * (s.nr 55 * i)) (s.nr 66 + s.nr 55 * i) t
        (fun j => s.rm (s.nr 20 + s.nr 55 * i + j))) ∧
      (∀ a < s.nr 65, t.nm a = s.nm a) ∧ (∀ a < s.nr 66, t.rm a = s.rm a) := by
  let k := s.nr 55
  let natBase := s.nr 65
  let realBase := s.nr 66
  let inv := MatchingPairSweepInvariant k natBase realBase s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 74 0} := by
    refine ⟨rfl, running, by simp, ?_, rfl, by simp, fun _ _ => rfl, fun _ _ => rfl⟩
    intro r available
    have h : r ≠ 74 := by omega
    simp [h]
  have iterate (row : ℕ) (hrow : row < k) (m : ArithmeticState) (hm : inv row m) :
      ∃ t steps, steps ≤ 16 * k + 8 ∧ BlockRuns seedMatchingPairRow steps m t ∧
        t.halted = false ∧ inv (row + 1)
          {t with pc := 0, nr := Function.update t.nr 74 (t.nr 74 + t.nr 34)} := by
    have r20 := hm.regs 20 (Or.inl (by decide))
    have r21 := hm.regs 21 (Or.inl (by decide))
    have r34 := hm.regs 34 (Or.inl (by decide))
    have r55 : m.nr 55 = k := hm.regs 55 (Or.inl (by decide))
    have r65 : m.nr 65 = natBase := hm.regs 65 (Or.inl (by decide))
    have r66 : m.nr 66 = realBase := hm.regs 66 (Or.inl (by decide))
    have r81 := hm.regs 81 (Or.inr (by decide))
    have rowCell : m.nm (m.nr 21 + m.nr 74) = m.nr 55 * m.nr 74 := by
      rw [r21, hm.rowIndex, r55]
      have low : s.nr 21 + row < natBase := by dsimp [natBase, k] at hrow ⊢; omega
      exact (hm.natural _ (Or.inl low)).trans (offsets row hrow)
    obtain ⟨t, steps, budget, run, ready, tables, regs, delta, natMem, realMem⟩ :=
      seedMatchingPairRow_correct hm.entry hm.running (r34.trans one) (r81.trans zero)
        (by rw [r20, r55, r66]; exact costBefore) (by rw [hm.rowIndex, r55]; exact hrow) rowCell
    rw [r55] at budget
    rw [r55, r65, r66, r20, hm.rowIndex] at tables
    rw [r55, r65, hm.rowIndex] at natMem
    rw [r55, r66, hm.rowIndex] at realMem
    let next := {t with pc := 0, nr := Function.update t.nr 74 (t.nr 74 + t.nr 34)}
    refine ⟨t, steps, budget, run, ready, show inv (row + 1) next from ?_⟩
    constructor
    · rfl
    · exact ready
    · simp [next, regs 74 (Or.inl (by decide)), regs 34 (Or.inl (by decide)), hm.rowIndex, r34, one]
    · intro r available
      have different : r ≠ 74 := by omega
      have kept : r < 75 ∨ 80 < r := by omega
      simpa [next, different] using (regs r kept).trans (hm.regs r available)
    · exact delta.trans hm.delta
    · intro i hi
      obtain before | here := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi)
      · have lower : k * i + k ≤ k * row := by
          simpa [Nat.mul_add] using Nat.mul_le_mul_left k (Nat.succ_le_of_lt before)
        apply (hm.rows i before).transfer
        · intro a _ bound
          apply natMem
          left
          omega
        · intro a _ bound
          apply realMem
          left
          omega
        · intro _ _; rfl
      · subst i
        refine ⟨tables.first, tables.second, fun j hj => (tables.score j hj).trans ?_⟩
        have bound : k * row + j < k * k := by
          have bounded := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hrow)
          rw [Nat.mul_succ] at bounded
          omega
        have low : s.nr 20 + k * row + j < realBase := by dsimp [k, realBase] at bound ⊢; omega
        exact hm.real _ (Or.inl low)
    · intro a available
      have rowWidth : k * (row + 1) = k * row + k := by simp [Nat.mul_add]
      rw [rowWidth] at available
      have outside : a < natBase + 2 * (k * row) ∨ natBase + 2 * (k * row) + 2 * k ≤ a := by omega
      have previous : a < natBase ∨ natBase + 2 * (k * row) ≤ a := by omega
      exact (natMem a outside).trans (hm.natural a previous)
    · intro a available
      have rowWidth : k * (row + 1) = k * row + k := by simp [Nat.mul_add]
      rw [rowWidth] at available
      have outside : a < realBase + k * row ∨ realBase + k * row + k ≤ a := by omega
      have previous : a < realBase ∨ realBase + k * row ≤ a := by omega
      exact (realMem a outside).trans (hm.real a previous)
  obtain ⟨last, steps, done, cost, run⟩ := countedLoopFromZero_bounded 34 74 55 k (16 * k + 8)
    seedMatchingPairRow inv entry running initial
    (fun _ _ h => ⟨h.entry, h.running, h.rowIndex, h.regs 55 (Or.inl (by decide))⟩) iterate
  refine ⟨_, steps, ?_, run, done.running, done.delta, done.regs, ?_, ?_, ?_⟩
  · change steps ≤ 1 + (k * (16 * k + 8 + 3) + 1) at cost
    change steps ≤ k * (16 * k + 11) + 2
    rw [show 16 * k + 8 + 3 = 16 * k + 11 by omega] at cost
    omega
  · intro i hi
    have row := done.rows i hi
    exact ⟨row.first, row.second, row.score⟩
  · exact fun a h => done.natural a (Or.inl h)
  · exact fun a h => done.real a (Or.inl h)

private theorem finishMatchingPairs_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 34 = 1) (zero : s.nr 81 = 0)
    (offsets : ∀ i < s.nr 55, s.nm (s.nr 21 + i) = s.nr 55 * i) :
    let k := s.nr 55
    let t := {s with
      pc := 10
      nr := Function.update (Function.update
        (Function.update (Function.update s.nr 76 (k * k)) 69 (s.nr 66 + k * k))
        76 (k * k + k * k)) 68 (s.nr 65 + (k * k + k * k))}
    ∃ steps ≤ 9, BlockRuns finishMatchingPairs steps s t := by
  intro k t
  by_cases empty : s.nr 55 = 0
  · refine ⟨5, by decide, BlockRuns.of_running_exit ?_ (show t.halted = false from running) rfl⟩
    simp [t, k, finishMatchingPairs, arithmeticStep, entry, running, zero, empty,
      Function.iterate_succ_apply']
  · have positive : 0 < s.nr 55 := Nat.pos_of_ne_zero empty
    have index : s.nr 55 - 1 < s.nr 55 := by omega
    have last := offsets _ index
    have square : s.nr 55 * (s.nr 55 - 1) + s.nr 55 = s.nr 55 * s.nr 55 := by
      rw [← Nat.mul_succ, show (s.nr 55 - 1).succ = s.nr 55 by omega]
    refine ⟨9, le_rfl, BlockRuns.of_running_exit ?_ (show t.halted = false from running) rfl⟩
    simp [t, k, finishMatchingPairs, arithmeticStep, entry, running, one, zero,
      not_le.mpr positive, last, square, Function.iterate_succ_apply', Function.update_idem]

/-- The pair-cache addresses and entries after the row sweep. Prior memory remains available. -/
structure MatchingPairSeeded (s t : ArithmeticState) : Prop where
  naturalBase : t.nr 65 = s.nr 68
  realBase : t.nr 66 = s.nr 69
  naturalEnd : t.nr 68 = s.nr 68 + 2 * (s.nr 55 * s.nr 55)
  realEnd : t.nr 69 = s.nr 69 + s.nr 55 * s.nr 55
  cumulativeDelta : t.rr 15 = 0
  rows : ∀ i < s.nr 55, MatchingPairSeededRow (s.nr 55) (s.nr 55) i
    (s.nr 68 + 2 * (s.nr 55 * i)) (s.nr 69 + s.nr 55 * i) t
    (fun j => s.rm (s.nr 20 + s.nr 55 * i + j))
  natural : ∀ a < s.nr 68, t.nm a = s.nm a
  real : ∀ a < s.nr 69, t.rm a = s.rm a
  registers : ∀ r, r < 65 ∨ 81 < r → t.nr r = s.nr r

set_option maxHeartbeats 550000 in
theorem seedMatchingPairCacheBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 34 = 1)
    (offsetsBefore : s.nr 21 + s.nr 55 ≤ s.nr 68)
    (costBefore : s.nr 20 + s.nr 55 * s.nr 55 ≤ s.nr 69)
    (offsets : ∀ i < s.nr 55, s.nm (s.nr 21 + i) = s.nr 55 * i) :
    ∃ t steps, steps ≤ s.nr 55 * (16 * s.nr 55 + 11) + 15 ∧
      BlockRuns seedMatchingPairCacheBlock steps s t ∧ t.halted = false ∧ MatchingPairSeeded s t := by
  let initialized := {s with
    pc := 4
    nr := Function.update (Function.update (Function.update s.nr 81 0) 65 (s.nr 68)) 66 (s.nr 69)
    rr := Function.update s.rr 15 0}
  have head : BlockRuns prepareMatchingPairs 4 s initialized := by
    refine BlockRuns.of_running_exit ?_ (show initialized.halted = false from running) rfl
    simp [initialized, prepareMatchingPairs, arithmeticStep, entry, running, Function.iterate_succ_apply']
  let input := {initialized with pc := 0}
  obtain ⟨middle, scanSteps, scanBudget, scan, live, delta, regs, rows, natural, real⟩ :=
    seedMatchingPairSweep_correct (s := input) rfl running (by simpa [input, initialized] using one)
      (by simp [input, initialized]) (by simpa [input, initialized] using offsetsBefore)
      (by simpa [input, initialized] using costBefore) (by simpa [input, initialized] using offsets)
  let tailInput := {middle with pc := 0}
  have nr20 : tailInput.nr 20 = s.nr 20 := by simpa [tailInput, input, initialized] using regs 20 (Or.inl (by decide))
  have nr21 : tailInput.nr 21 = s.nr 21 := by simpa [tailInput, input, initialized] using regs 21 (Or.inl (by decide))
  have nr34 : tailInput.nr 34 = 1 := by simpa [tailInput, input, initialized, one] using regs 34 (Or.inl (by decide))
  have nr55 : tailInput.nr 55 = s.nr 55 := by simpa [tailInput, input, initialized] using regs 55 (Or.inl (by decide))
  have nr65 : tailInput.nr 65 = s.nr 68 := by simpa [tailInput, input, initialized] using regs 65 (Or.inl (by decide))
  have nr66 : tailInput.nr 66 = s.nr 69 := by simpa [tailInput, input, initialized] using regs 66 (Or.inl (by decide))
  have nr81 : tailInput.nr 81 = 0 := by simpa [tailInput, input, initialized] using regs 81 (Or.inr (by decide))
  have natMem (a : ℕ) (low : a < s.nr 68) : middle.nm a = s.nm a :=
    natural a (by simpa [input, initialized] using low)
  have tailOffsets (i : ℕ) (hi : i < tailInput.nr 55) :
      tailInput.nm (tailInput.nr 21 + i) = tailInput.nr 55 * i := by
    change middle.nm _ = _
    rw [nr55] at hi
    rw [nr21, nr55, natMem _ (by omega), offsets i hi]
  obtain ⟨tailSteps, tailBudget, tailRun⟩ := finishMatchingPairs_correct (s := tailInput) rfl live nr34 nr81 tailOffsets
  refine ⟨_, 4 + (scanSteps + tailSteps), ?_, head.append (scan.append tailRun), live, ?_⟩
  · simp [input, initialized] at scanBudget
    omega
  constructor
  · simpa [relocateState] using nr65
  · simpa [relocateState] using nr66
  · simp [relocateState, nr65, nr55, Nat.two_mul]
  · simp [relocateState, nr66, nr55]
  · simpa [relocateState, input, initialized] using delta
  · intro i hi
    have isLt : i < input.nr 55 := by simpa [input, initialized] using hi
    have row := rows i isLt
    constructor
    · simpa [relocateState, input, initialized] using row.first
    · simpa [relocateState, input, initialized] using row.second
    · simpa [relocateState, input, initialized] using row.score
  · exact natMem
  · simpa [relocateState, input, initialized] using real
  · intro r hr
    have a : r ≠ 65 := by omega
    have b : r ≠ 66 := by omega
    have c : r ≠ 68 := by omega
    have d : r ≠ 69 := by omega
    have e : r ≠ 76 := by omega
    have f : r ≠ 81 := by omega
    have kept : r < 74 ∨ 80 < r := by omega
    simpa [relocateState, input, initialized, a, b, c, d, e, f] using regs r kept


end VehicleRoutingSurvey.Routing
end RppSource_MatchingPairSeed

/-! matching/MatchingPrelude.lean -/
section RppSource_MatchingPrelude
namespace VehicleRoutingSurvey.Routing







/-- The allocator and two linear passes leave the selector empty, with the exposed roots and
all compact inputs ready for the initial cost scan. -/
structure CompactMatchingArraysStart (k : ℕ) (layout : MatchingWorkspace)
    (original t : ArithmeticState) : Prop where
  workspace : MatchingWorkspaceRegisters k layout t
  mapBase : t.nr 56 = original.nr 31
  metric : t.nr 20 = original.nr 20 ∧ t.nr 21 = original.nr 21
  stage : t.nr 31 = 6 * k + 1 ∧ t.nr 32 = 0 ∧ t.nr 33 = 1 ∧ t.nr 34 = 1
  outer : t.nr 41 = 1 ∧ t.nr 42 = k / 2
  selector : t.nr 1 = 0 ∧ t.nr 9 = 1 ∧ t.nr 8 = 3 * k ∧ t.nr 61 = 3 * k ∧
    t.nr 3 = layout.identifiers ∧ t.nr 4 = layout.slacks ∧ t.nr 5 = layout.rates
  inactive : ∀ i < 3 * k, t.nm (layout.identifiers + i) = 0
  mates : ∀ v : Fin k, t.nm (layout.mates + v.val) = k
  forest : AlternatingForestMemory
    (resetAlternatingForest Finset.univ (fun _ : Fin k => none)) layout.roles t.nm
  representatives : ∀ v : Fin k, t.nm (layout.representatives + v.val) = v.val
  potentials : ∀ v : Fin k, t.rm (layout.potentials + v.val) = 0
  natural : ∀ a < original.nr 63, t.nm a = original.nm a
  real : ∀ a < original.nr 64, t.rm a = original.rm a
  saved : ∀ r ≥ 100, t.nr r = original.nr r

set_option maxHeartbeats 650000 in
theorem initializeCompactMatchingArraysBlock_correct {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {s : ArithmeticState} (input : CompactMateInput cost s)
    (entry : s.pc = 0) (running : s.halted = false) :
    let layout := MatchingWorkspace.allocate k (s.nr 63) (s.nr 64)
    ∃ t, BlockRuns initializeCompactMatchingArraysBlock (38 * k + 37) s t ∧ t.halted = false ∧
      CompactMatchingArraysStart k layout s t := by
  intro layout
  obtain ⟨a, allocated, aLive, aFrame⟩ := allocateMatchingWorkspaceBlock_correct entry running
  rw [input.dimension] at aFrame
  let aInput := {a with pc := 0}
  have aPointers : MatchingWorkspaceRegisters k layout aInput := by
    have w := aFrame.workspace
    exact ⟨w.dimension, w.mates, w.roles, w.parents, w.depths, w.representatives, w.identifiers,
      w.endpoints, w.potentials, w.slacks, w.rates, w.naturalEnd, w.realEnd⟩
  obtain ⟨b, vertices, bLive, bFrame⟩ := initializeMatchingVerticesBlock_correct
    (s := aInput) rfl aLive aPointers aFrame.stageOne aFrame.zero aFrame.count aFrame.parity
  let entered := relocateState allocateMatchingWorkspaceBlock.length b
  let bInput := {entered with pc := 0}
  have bReg (r : ℕ) (h0 : r ≠ 0 := by decide) (h42 : r ≠ 42 := by decide)
      (h65 : r ≠ 65 := by decide) (h70 : r ≠ 70 := by decide) : bInput.nr r = a.nr r :=
    bFrame.register r h0 h42 h65 h70
  have startOne : bInput.nr 34 = 1 := (bReg 34).trans aFrame.stageOne
  obtain ⟨c, cleared, cLive, cReg, cReal, cNatural⟩ := clearMatchingCandidatesBlock_correct (s := bInput) rfl bLive startOne
  let t := relocateState (appendBlock allocateMatchingWorkspaceBlock initializeMatchingVerticesBlock).length c
  have tReg (r : ℕ) (h0 : r ≠ 0 := by decide) (h2 : r ≠ 2 := by decide)
      (h42 : r ≠ 42 := by decide) (h65 : r ≠ 65 := by decide) (h70 : r ≠ 70 := by decide)
      (h71 : r ≠ 71 := by decide) : t.nr r = a.nr r :=
    (cReg r h0 h2 h71).trans (bReg r h0 h42 h65 h70)
  have idBase : bInput.nr 58 = layout.identifiers := (bReg 58).trans aFrame.workspace.identifiers
  have count : bInput.nr 61 = 3 * k := (bReg 61).trans aFrame.candidateCount
  have below (address : ℕ) (low : address < layout.identifiers) : t.nm address = b.nm address := by
    change c.nm address = b.nm address
    rw [cNatural, idBase, if_neg (fun h => (not_le.mpr low) h.1)] <;> rfl
  have steps : 33 + (20 * k + 2) + (6 * bInput.nr 61 + 2) = 38 * k + 37 := by rw [count]; omega
  refine ⟨t, steps ▸ (allocated.append vertices).append cleared, cLive, ?_⟩
  constructor
  · exact ⟨(tReg 55).trans aFrame.workspace.dimension, (tReg 50).trans aFrame.workspace.mates,
      (tReg 51).trans aFrame.workspace.roles, (tReg 52).trans aFrame.workspace.parents,
      (tReg 53).trans aFrame.workspace.depths, (tReg 57).trans aFrame.workspace.representatives,
      (tReg 58).trans aFrame.workspace.identifiers, (tReg 54).trans aFrame.workspace.endpoints,
      (tReg 62).trans aFrame.workspace.potentials, (tReg 59).trans aFrame.workspace.slacks,
      (tReg 60).trans aFrame.workspace.rates, (tReg 68).trans aFrame.workspace.naturalEnd,
      (tReg 69).trans aFrame.workspace.realEnd⟩
  · exact (tReg 56).trans aFrame.oddMap
  · exact ⟨(tReg 20).trans (aFrame.inputReg 20 (by decide)), (tReg 21).trans (aFrame.inputReg 21 (by decide))⟩
  · exact ⟨(tReg 31).trans aFrame.stageLimit, (tReg 32).trans aFrame.stageZero,
      (tReg 33).trans aFrame.stageActive, (tReg 34).trans aFrame.stageOne⟩
  · exact ⟨(tReg 41).trans aFrame.outerOne, (cReg 42 (by decide) (by decide) (by decide)).trans bFrame.count⟩
  · exact ⟨(tReg 1).trans aFrame.selectorInit.1, (tReg 9).trans aFrame.selectorInit.2,
      (tReg 8).trans aFrame.selectorCount, (tReg 61).trans aFrame.candidateCount,
      (tReg 3).trans aFrame.selectorBases.1, (tReg 4).trans aFrame.selectorBases.2.1,
      (tReg 5).trans aFrame.selectorBases.2.2⟩
  · intro i hi
    change c.nm (layout.identifiers + i) = 0
    rw [cNatural, idBase, count, if_pos (by omega)]
  · intro v
    rw [below _ (by dsimp [layout, MatchingWorkspace.allocate]; omega)]
    exact bFrame.mates v
  · intro v
    have strict := v.isLt
    have h1 := below (layout.roles + v.val) (by dsimp [layout, MatchingWorkspace.allocate]; omega)
    have h2 := below (layout.roles + k + v.val) (by dsimp [layout, MatchingWorkspace.allocate]; omega)
    have h3 := below (layout.roles + k + k + v.val) (by dsimp [layout, MatchingWorkspace.allocate]; omega)
    rw [h1, h2, h3]
    exact bFrame.forest v
  · intro v
    rw [below _ (by dsimp [layout, MatchingWorkspace.allocate]; exact Nat.add_lt_add_left v.isLt _)]
    exact bFrame.representatives v
  · intro v
    change c.rm _ = _
    rw [cReal]
    exact bFrame.potentials v
  · intro address low
    rw [below _ (by dsimp [layout, MatchingWorkspace.allocate]; omega)]
    exact (bFrame.natural address low).trans (congrFun aFrame.natural address)
  · intro address low
    change c.rm address = s.rm address
    rw [cReal]
    exact (bFrame.real address low).trans (congrFun aFrame.real address)
  · intro r high
    exact (tReg r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (aFrame.saved r high)


/-- The first search starts with singleton exposed roots and zero dual variables. The selector
contains one least edge per root, and pair buckets retain the original compact costs. -/
structure CompactMatchingFirstStage {k : ℕ} (cost : Fin k → Fin k → ℝ)
    (layout : MatchingWorkspace) (original t : ArithmeticState) : Prop where
  workspace : MatchingWorkspaceRegisters k
    {layout with naturalEnd := layout.naturalEnd + 2 * (k * k), realEnd := layout.realEnd + k * k} t
  mapBase : t.nr 56 = original.nr 31
  metric : t.nr 20 = original.nr 20 ∧ t.nr 21 = original.nr 21
  stage : t.nr 31 = 6 * k + 1 ∧ t.nr 32 = 0 ∧ t.nr 33 = 1 ∧ t.nr 34 = 1
  outer : t.nr 41 = 1 ∧ t.nr 42 = k / 2
  selector : t.nr 1 = 0 ∧ t.nr 9 = 1 ∧ t.nr 8 = 3 * k ∧ t.nr 61 = 3 * k ∧
    t.nr 3 = layout.identifiers ∧ t.nr 4 = layout.slacks ∧ t.nr 5 = layout.rates
  candidates : ∃ rows, DualBoundTable t rows (decodeInitialMatchingEvent k t) ∧
    DualSlackCache (matchingDualSlacks cost (compactMatchingEdges k) ∅
      (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ => 0)) (rows.filterMap id)
  pairCacheBases : t.nr 65 = layout.naturalEnd ∧ t.nr 66 = layout.realEnd
  pairCache : ∀ i < k, MatchingPairSeededRow k k i (layout.naturalEnd + 2 * (k * i))
    (layout.realEnd + k * i) t (fun j => original.rm (original.nr 20 + k * i + j))
  cumulativeDelta : t.rr 15 = 0
  mates : ∀ v : Fin k, t.nm (layout.mates + v.val) = k
  forest : AlternatingForestMemory
    (resetAlternatingForest Finset.univ (fun _ : Fin k => none)) layout.roles t.nm
  representatives : ∀ v : Fin k, t.nm (layout.representatives + v.val) = v.val
  potentials : ∀ v : Fin k, t.rm (layout.potentials + v.val) = 0
  natural : ∀ a < original.nr 63, t.nm a = original.nm a
  real : ∀ a < original.nr 64, t.rm a = original.rm a
  saved : ∀ r ≥ 100, t.nr r = original.nr r

set_option maxHeartbeats 950000 in
theorem prepareCompactMatchingBlock_correct {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {s : ArithmeticState} (input : CompactMateInput cost s)
    (entry : s.pc = 0) (running : s.halted = false) :
    let layout := MatchingWorkspace.allocate k (s.nr 63) (s.nr 64)
    ∃ t steps, steps ≤ 32 * k * k + 77 * k + 55 ∧ BlockRuns prepareCompactMatchingBlock steps s t ∧
      t.halted = false ∧ CompactMatchingFirstStage cost layout s t := by
  intro layout
  obtain ⟨a, arrays, aLive, aFrame⟩ := initializeCompactMatchingArraysBlock_correct input entry running
  let aInput := {a with pc := 0}
  have dimension : aInput.nr 55 = k := aFrame.workspace.dimension
  have costBefore : s.nr 20 + k * k ≤ s.nr 64 := by simpa only [pow_two] using input.realSpace
  have rows (i : ℕ) (hi : i < k) : aInput.nm (aInput.nr 21 + i) = k * i := by
    change a.nm (a.nr 21 + i) = _
    rw [aFrame.metric.2, aFrame.natural _ (by have := input.naturalSpace; omega)]
    exact input.rows i hi
  have weights (i j : Fin k) : aInput.rm (aInput.nr 20 + k * i.val + j.val) = cost i j := by
    have hi := i.isLt
    have hj := j.isLt
    have within := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hi)
    rw [Nat.mul_succ] at within
    change a.rm (a.nr 20 + k * i.val + j.val) = _
    rw [aFrame.metric.1, aFrame.real _ (by omega)]
    exact input.weights i j
  have evenAt : aInput.nr 55 % 2 = 0 := dimension.symm ▸ input.even
  have idsAfter : aInput.nr 21 + aInput.nr 55 ≤ aInput.nr 58 := by
    rw [dimension, show aInput.nr 21 = s.nr 21 from aFrame.metric.2,
      show aInput.nr 58 = layout.identifiers from aFrame.workspace.identifiers]
    have := input.naturalSpace
    dsimp [layout, MatchingWorkspace.allocate]
    omega
  have dictAfter : aInput.nr 58 + aInput.nr 55 ≤ aInput.nr 54 := by
    rw [dimension, show aInput.nr 58 = layout.identifiers from aFrame.workspace.identifiers,
      show aInput.nr 54 = layout.endpoints from aFrame.workspace.endpoints]
    dsimp [layout, MatchingWorkspace.allocate]
    omega
  have slackAfter : aInput.nr 20 + aInput.nr 55 * aInput.nr 55 ≤ aInput.nr 59 := by
    rw [dimension, show aInput.nr 20 = s.nr 20 from aFrame.metric.1,
      show aInput.nr 59 = layout.slacks from aFrame.workspace.slacks]
    dsimp [layout, MatchingWorkspace.allocate]
    omega
  have rateAfter : aInput.nr 59 + aInput.nr 55 ≤ aInput.nr 60 := by
    rw [dimension, show aInput.nr 59 = layout.slacks from aFrame.workspace.slacks,
      show aInput.nr 60 = layout.rates from aFrame.workspace.rates]
    dsimp [layout, MatchingWorkspace.allocate]
    omega
  obtain ⟨b, seedSteps, seedBudget, seeded, bLive, noWinner, cache⟩ :=
    seedMatchingEventCacheBlock_correct (s := aInput) rfl aLive aFrame.stage.2.2.2
      aFrame.selector.2.1 evenAt idsAfter dictAfter slackAfter rateAfter
      (by simpa only [dimension] using rows)
  let bInput := {relocateState initializeCompactMatchingArraysBlock.length b with pc := 0}
  have bReg (r : ℕ) (high : 3 ≤ r := by decide)
      (fixed : r ∉ [6, 10, 14, 15, 16, 18, 71, 72, 73] := by decide) : bInput.nr r = aInput.nr r :=
    cache.regs r high fixed
  have natSeed (address : ℕ) (beforeIds : address < layout.identifiers) : bInput.nm address = aInput.nm address := by
    apply cache.natural address
    · exact Or.inl (aFrame.workspace.identifiers.symm ▸ beforeIds)
    · apply Or.inl
      rw [show aInput.nr 54 = layout.endpoints from aFrame.workspace.endpoints]
      dsimp [layout, MatchingWorkspace.allocate] at beforeIds ⊢
      omega
  have realSeed (address : ℕ) (beforeSlack : address < layout.slacks) : bInput.rm address = aInput.rm address := by
    apply cache.real address
    · exact Or.inl (aFrame.workspace.slacks.symm ▸ beforeSlack)
    · apply Or.inl
      rw [show aInput.nr 60 = layout.rates from aFrame.workspace.rates]
      dsimp [layout, MatchingWorkspace.allocate] at beforeSlack ⊢
      omega
  have bSize : bInput.nr 55 = k := (bReg 55).trans dimension
  have bNatEnd : bInput.nr 68 = layout.naturalEnd := (bReg 68).trans aFrame.workspace.naturalEnd
  have bRealEnd : bInput.nr 69 = layout.realEnd := (bReg 69).trans aFrame.workspace.realEnd
  have bOne : bInput.nr 34 = 1 := (bReg 34).trans aFrame.stage.2.2.2
  have bRows (i : ℕ) (hi : i < bInput.nr 55) : bInput.nm (bInput.nr 21 + i) = bInput.nr 55 * i := by
    rw [bSize] at hi
    rw [bReg 21, bSize, natSeed _ (by
      rw [show aInput.nr 21 = s.nr 21 from aFrame.metric.2]
      have := input.naturalSpace
      dsimp [layout, MatchingWorkspace.allocate]
      omega)]
    exact rows i hi
  obtain ⟨c, pairSteps, pairBudget, paired, cLive, pair⟩ :=
    seedMatchingPairCacheBlock_correct (s := bInput) rfl bLive bOne
      (by rw [bReg 21, bSize, bNatEnd, show aInput.nr 21 = s.nr 21 from aFrame.metric.2]
          have := input.naturalSpace
          dsimp [layout, MatchingWorkspace.allocate]
          omega)
      (by rw [bReg 20, bSize, bRealEnd, show aInput.nr 20 = s.nr 20 from aFrame.metric.1]
          dsimp [layout, MatchingWorkspace.allocate]
          omega) bRows
  let t := relocateState (appendBlock initializeCompactMatchingArraysBlock seedMatchingEventCacheBlock).length c
  have kept (r : ℕ) (high : 3 ≤ r := by decide) (low : r < 65 := by decide)
      (fixed : r ∉ [6, 10, 14, 15, 16, 18, 71, 72, 73] := by decide) : t.nr r = aInput.nr r :=
    (pair.registers r (Or.inl low)).trans (bReg r high fixed)
  have naturalPair (address : ℕ) (low : address < layout.naturalEnd) : t.nm address = bInput.nm address :=
    pair.natural address (bNatEnd.symm ▸ low)
  have realPair (address : ℕ) (low : address < layout.realEnd) : t.rm address = bInput.rm address :=
    pair.real address (bRealEnd.symm ▸ low)
  have belowIds (address : ℕ) (low : address < layout.identifiers) : t.nm address = a.nm address :=
    (naturalPair address (by dsimp [layout, MatchingWorkspace.allocate] at low ⊢; omega)).trans
      (natSeed address low)
  have belowSlack (address : ℕ) (low : address < layout.slacks) : t.rm address = a.rm address :=
    (realPair address (by dsimp [layout, MatchingWorkspace.allocate] at low ⊢; omega)).trans
      (realSeed address low)
  have stagesBound : (38 * k + 37) + seedSteps + pairSteps ≤ 32 * k * k + 77 * k + 55 := by
    rw [dimension] at seedBudget
    rw [bSize] at pairBudget
    calc
      _ ≤ (38 * k + 37) + (k * (16 * k + 28) + 3) + (k * (16 * k + 11) + 15) :=
        Nat.add_le_add (Nat.add_le_add_left seedBudget _) pairBudget
      _ = _ := by ring
  refine ⟨t, _, stagesBound, (arrays.append seeded).append paired, cLive, ?_⟩
  constructor
  · exact ⟨(kept 55).trans dimension, (kept 50).trans aFrame.workspace.mates,
      (kept 51).trans aFrame.workspace.roles, (kept 52).trans aFrame.workspace.parents,
      (kept 53).trans aFrame.workspace.depths, (kept 57).trans aFrame.workspace.representatives,
      (kept 58).trans aFrame.workspace.identifiers, (kept 54).trans aFrame.workspace.endpoints,
      (kept 62).trans aFrame.workspace.potentials, (kept 59).trans aFrame.workspace.slacks,
      (kept 60).trans aFrame.workspace.rates,
      by simpa only [t, relocateState, bNatEnd, bSize] using pair.naturalEnd,
      by simpa only [t, relocateState, bRealEnd, bSize] using pair.realEnd⟩
  · exact (kept 56).trans aFrame.mapBase
  · exact ⟨(kept 20).trans aFrame.metric.1, (kept 21).trans aFrame.metric.2⟩
  · exact ⟨(kept 31).trans aFrame.stage.1, (kept 32).trans aFrame.stage.2.1,
      (kept 33).trans aFrame.stage.2.2.1, (kept 34).trans aFrame.stage.2.2.2⟩
  · exact ⟨(kept 41).trans aFrame.outer.1, (kept 42).trans aFrame.outer.2⟩
  · exact ⟨(pair.registers 1 (Or.inl (by decide))).trans noWinner, (kept 9).trans aFrame.selector.2.1,
      (kept 8).trans aFrame.selector.2.2.1, (kept 61).trans aFrame.selector.2.2.2.1,
      (kept 3).trans aFrame.selector.2.2.2.2.1, (kept 4).trans aFrame.selector.2.2.2.2.2.1,
      (kept 5).trans aFrame.selector.2.2.2.2.2.2⟩
  · apply matchingSeedEntries_validSelector (original := aInput) (t := t) _ dimension
      ((kept 8).trans aFrame.selector.2.2.1)
      ((kept 3).trans (aFrame.selector.2.2.2.2.1.trans aFrame.workspace.identifiers.symm)) (kept 54)
      ((kept 4).trans (aFrame.selector.2.2.2.2.2.1.trans aFrame.workspace.slacks.symm))
      ((kept 5).trans (aFrame.selector.2.2.2.2.2.2.trans aFrame.workspace.rates.symm))
      _ weights input.symmetric (compactMatchingEdges k)
      (fun _ h => mem_compactMatchingEdges_iff.mp h) (fun _ _ h => mem_compactMatchingEdges_mk h)
    · intro i hi
      obtain ⟨j, row⟩ := cache.entries i (dimension.symm ▸ hi)
      have left : aInput.nr 58 = layout.identifiers := aFrame.workspace.identifiers
      have dict : aInput.nr 54 = layout.endpoints := aFrame.workspace.endpoints
      have slack : aInput.nr 59 = layout.slacks := aFrame.workspace.slacks
      have rate : aInput.nr 60 = layout.rates := aFrame.workspace.rates
      refine ⟨j, row.within, row.distinct, row.least, ?_, ?_, ?_, ?_, ?_⟩
      · exact (naturalPair _ (by rw [left]; dsimp [layout, MatchingWorkspace.allocate]; omega)).trans row.identifier
      · exact (naturalPair _ (by rw [dict]; dsimp [layout, MatchingWorkspace.allocate]; omega)).trans row.source
      · exact (naturalPair _ (by rw [dict]; dsimp [layout, MatchingWorkspace.allocate]; omega)).trans row.target
      · exact (realPair _ (by rw [slack]; dsimp [layout, MatchingWorkspace.allocate]; omega)).trans row.slack
      · exact (realPair _ (by rw [rate]; dsimp [layout, MatchingWorkspace.allocate]; omega)).trans row.rate
    · intro i past hi
      rw [show aInput.nr 58 = layout.identifiers from aFrame.workspace.identifiers,
        naturalPair _ (by dsimp [layout, MatchingWorkspace.allocate]; omega)]
      change b.nm (layout.identifiers + i) = 0
      have unread := cache.natural (layout.identifiers + i)
      rw [dimension, show aInput.nr 58 = layout.identifiers from aFrame.workspace.identifiers,
        show aInput.nr 54 = layout.endpoints from aFrame.workspace.endpoints] at unread
      exact (unread (Or.inr (by omega)) (Or.inl (by dsimp [layout, MatchingWorkspace.allocate]; omega))).trans
        (aFrame.inactive i hi)
  · exact ⟨pair.naturalBase.trans bNatEnd, pair.realBase.trans bRealEnd⟩
  · intro i hi
    have row := pair.rows i (bSize.symm ▸ hi)
    rw [bSize, bNatEnd, bRealEnd, bReg 20] at row
    refine ⟨row.first, row.second, fun j hj => (row.score j hj).trans ?_⟩
    have within := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hi)
    rw [Nat.mul_succ] at within
    rw [show aInput.nr 20 = s.nr 20 from aFrame.metric.1]
    exact (realSeed _ (by dsimp [layout, MatchingWorkspace.allocate]; omega)).trans (aFrame.real _ (by omega))
  · exact pair.cumulativeDelta
  · intro v
    have := v.isLt
    exact (belowIds _ (by dsimp [layout, MatchingWorkspace.allocate]; omega)).trans (aFrame.mates v)
  · intro v
    have := v.isLt
    obtain ⟨role, parent, depth⟩ := aFrame.forest v
    exact ⟨(belowIds _ (by dsimp [layout, MatchingWorkspace.allocate]; omega)).trans role,
      (belowIds _ (by dsimp [layout, MatchingWorkspace.allocate]; omega)).trans parent,
      (belowIds _ (by dsimp [layout, MatchingWorkspace.allocate]; omega)).trans depth⟩
  · intro v
    have := v.isLt
    exact (belowIds _ (by dsimp [layout, MatchingWorkspace.allocate]; omega)).trans (aFrame.representatives v)
  · intro v
    have := v.isLt
    exact (belowSlack _ (by dsimp [layout, MatchingWorkspace.allocate]; omega)).trans (aFrame.potentials v)
  · intro address low
    exact (belowIds _ (by dsimp [layout, MatchingWorkspace.allocate]; omega)).trans (aFrame.natural address low)
  · intro address low
    exact (belowSlack _ (by dsimp [layout, MatchingWorkspace.allocate]; omega)).trans (aFrame.real address low)
  · intro r high
    exact (pair.registers r (Or.inr (by omega))).trans
      ((bReg r (by omega) (by simp; omega)).trans (aFrame.saved r high))


end VehicleRoutingSurvey.Routing
end RppSource_MatchingPrelude

/-! matching/MatchingForestTraceSetup.lean -/
section RppSource_MatchingForestTraceSetup
namespace VehicleRoutingSurvey.Routing

/-- The two trace arrays and the vertex-to-left-position array have one
word per compact vertex. -/
structure MatchingForestTraceStorage (k base : ℕ) (s : ArithmeticState) : Prop where
  left : s.nr 83 = base
  right : s.nr 84 = base + k
  marks : s.nr 85 = base + k + k



theorem allocateForestTraceScratchBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns allocateForestTraceScratchBlock 5 s t ∧ t.halted = false ∧
      MatchingForestTraceStorage (s.nr 55) (s.nr 68) t ∧ t.nr 68 = s.nr 68 + 3 * s.nr 55 ∧
      t.nm = s.nm ∧ t.rr = s.rr ∧ t.rm = s.rm ∧
      (∀ r, r ∉ [49, 68, 83, 84, 85] → t.nr r = s.nr r) := by
  let t := (arithmeticStep allocateForestTraceScratchBlock)^[5] s
  have ready : t.halted = false := by
    simp [t, allocateForestTraceScratchBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  have exit : t.pc = allocateForestTraceScratchBlock.length := by
    simp [t, allocateForestTraceScratchBlock, arithmeticStep, Function.iterate_succ_apply', entry, running]
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | intro r away
      apply arithmeticRun_keeps_register _ s 5
      simp [allocateForestTraceScratchBlock, naturalDestination] at away ⊢
      omega
    | simp [t, allocateForestTraceScratchBlock, arithmeticStep,
        Function.iterate_succ_apply', entry, running] <;> omega



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

/-! matching/MatchingContractRowsRAM.lean -/
section RppSource_MatchingContractRowsRAM
namespace VehicleRoutingSurvey.Routing



theorem allocateMatchingContractionScratch_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    ∃ t, BlockRuns allocateMatchingContractionScratch 5 s t ∧ t.halted = false ∧
      t.nr 86 = s.nr 68 ∧ t.nr 88 = s.nr 68 + s.nr 55 ∧ t.nr 89 = s.nr 68 + 2 * s.nr 55 ∧
      t.nr 68 = s.nr 68 + 3 * s.nr 55 ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  let t := (arithmeticStep allocateMatchingContractionScratch)^[5] s
  have exit : t.pc = allocateMatchingContractionScratch.length ∧ t.halted = false := by
    simp [t, allocateMatchingContractionScratch, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl exit.2 exit.1, exit.2, ?_⟩
  simp [t, allocateMatchingContractionScratch, arithmeticStep, entry, running, Function.iterate_succ_apply'] <;> omega



































end VehicleRoutingSurvey.Routing
end RppSource_MatchingContractRowsRAM

/-! matching/MatchingAuxiliaryInit.lean -/
section RppSource_MatchingAuxiliaryInit
namespace VehicleRoutingSurvey.Routing



structure MatchingAuxiliaryInit (s t : ArithmeticState) : Prop where
  topNodes : t.nr 74 = s.nr 68
  cutDuals : t.nr 75 = s.nr 69
  nextNode : t.nr 76 = 1
  recordBases : t.nr 77 = s.nr 68 + s.nr 55
  recordLengths : t.nr 78 = s.nr 68 + s.nr 55 + matchingBlossomCapacity (s.nr 55)
  traces : MatchingForestTraceStorage (s.nr 55)
    (s.nr 68 + s.nr 55 + 2 * matchingBlossomCapacity (s.nr 55)) t
  parentWitnesses : t.nr 90 = s.nr 68 + 4 * s.nr 55 + 2 * matchingBlossomCapacity (s.nr 55)
  workRecords : t.nr 86 = t.nr 90 + 2 * s.nr 55
  promotionMarks : t.nr 88 = t.nr 86 + s.nr 55
  absorbedMarks : t.nr 89 = t.nr 86 + 2 * s.nr 55
  naturalEnd : t.nr 68 = t.nr 86 + 3 * s.nr 55
  realEnd : t.nr 69 = s.nr 69 + matchingBlossomCapacity (s.nr 55)
  natural : ∀ a, t.nm a = if s.nr 68 ≤ a ∧ a < s.nr 68 + s.nr 55 then 0 else s.nm a
  real : t.rm = s.rm
  delta : t.rr 15 = s.rr 15
  registers : ∀ r, r ∉ [0, 6, 7, 14, 23, 49, 68, 69, 74, 75, 76, 77, 78, 79, 80,
    83, 84, 85, 86, 88, 89, 90] → t.nr r = s.nr r

set_option maxRecDepth 4096 in
theorem initializeMatchingAuxiliaryBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (pairEnd : s.nr 69 = s.nr 66 + s.nr 55 * s.nr 55) :
    ∃ t, BlockRuns initializeMatchingAuxiliaryBlock (5 * s.nr 55 + 27) s t ∧
      t.halted = false ∧ MatchingAuxiliaryInit s t := by
  obtain ⟨a, registry, aLive, r74, r75, r76, r77, r78, aEnd, aRealEnd, aZero, aReal, aRR, aNat⟩ :=
    initializeMatchingBlossomRegistry_correct s entry running one pairEnd
  let aInput := {a with pc := 0}
  have aSize : aInput.nr 55 = s.nr 55 := by
    change a.nr 55 = s.nr 55
    rw [← registry.run]
    exact arithmeticRun_keeps_from_destination_list [0, 6, 7, 14, 68, 69, 74, 75, 76, 77, 78, 79, 80]
      (by decide) (by decide) s _
  obtain ⟨b, traces, bLive, traceBase, bEnd, bNat, bRR, bReal, bFixed⟩ :=
    allocateForestTraceScratchBlock_correct (s := aInput) rfl aLive
  let front := appendBlock initializeMatchingBlossomRegistry allocateForestTraceScratchBlock
  let bInput := {relocateState initializeMatchingBlossomRegistry.length b with pc := 0}
  have bSize : bInput.nr 55 = s.nr 55 := (bFixed 55 (by decide)).trans aSize
  have bZero : bInput.nr 14 = 0 := (bFixed 14 (by decide)).trans aZero
  obtain ⟨c, witnesses, cLive, witnessBase, cEnd, cNat, cReal, cRR⟩ :=
    allocateMatchingForestWitnessArray_spec bInput rfl bLive bZero
  let allocated := appendBlock front allocateMatchingForestWitnessArray
  let cInput := {relocateState front.length c with pc := 0}
  have cFixed (r : ℕ) (safe : r ∉ [0, 68, 90] := by decide) : cInput.nr r = bInput.nr r := by
    change c.nr r = _
    rw [← witnesses.run]
    exact arithmeticRun_keeps_from_destination_list _ (by decide) safe bInput 3
  obtain ⟨d, records, dLive, workBase, promo, absorbed, dEnd, dNat, dReal⟩ :=
    allocateMatchingContractionScratch_spec cInput rfl cLive
  let t := relocateState allocated.length d
  have dFixed (r : ℕ) (safe : r ∉ [0, 23, 68, 86, 88, 89] := by decide) : t.nr r = cInput.nr r := by
    change d.nr r = _
    rw [← records.run]
    exact arithmeticRun_keeps_from_destination_list _ (by decide) safe cInput 5
  have later (r : ℕ) (hb : r ∉ [49, 68, 83, 84, 85] := by decide)
      (hc : r ∉ [0, 68, 90] := by decide) (hd : r ∉ [0, 23, 68, 86, 88, 89] := by decide) :
      t.nr r = aInput.nr r := (dFixed r hd).trans ((cFixed r hc).trans (bFixed r hb))
  have cSize : cInput.nr 55 = s.nr 55 := (cFixed 55).trans bSize
  have aAllocated : aInput.nr 68 = s.nr 68 + s.nr 55 + 2 * matchingBlossomCapacity (s.nr 55) := aEnd
  have afterTrace : bInput.nr 68 = s.nr 68 + s.nr 55 + 2 * matchingBlossomCapacity (s.nr 55) + 3 * s.nr 55 := by
    change b.nr 68 = _
    rw [bEnd, aAllocated, aSize]
  have afterWitness : cInput.nr 68 = t.nr 90 + 2 * s.nr 55 := by
    rw [dFixed 90, show cInput.nr 90 = bInput.nr 68 from witnessBase]
    change c.nr 68 = _
    simpa only [bSize] using cEnd
  have composite : BlockRuns initializeMatchingAuxiliaryBlock
      (((12 + (1 + (s.nr 55 * 5 + 1))) + 5) + 3 + 5) s t :=
    (((registry.append traces).append witnesses).append records)
  have ticks : ((12 + (1 + (s.nr 55 * 5 + 1))) + 5) + 3 + 5 = 5 * s.nr 55 + 27 := by omega
  refine ⟨t, ticks ▸ composite, dLive, ?_⟩
  constructor
  · exact (later 74).trans r74
  · exact (later 75).trans r75
  · exact (later 76).trans r76
  · exact (later 77).trans r77
  · exact (later 78).trans r78
  · obtain ⟨left, right, marks⟩ := traceBase
    exact ⟨by simpa only [aAllocated] using (dFixed 83).trans ((cFixed 83).trans left),
      by simpa only [aAllocated, aSize] using (dFixed 84).trans ((cFixed 84).trans right),
      by simpa only [aAllocated, aSize] using (dFixed 85).trans ((cFixed 85).trans marks)⟩
  · have atBase := (dFixed 90).trans witnessBase
    rw [atBase, afterTrace]
    omega
  · exact workBase.trans afterWitness
  · simpa only [t, relocateState, cSize, ← workBase] using promo
  · simpa only [t, relocateState, cSize, ← workBase] using absorbed
  · simpa only [t, relocateState, cSize, ← workBase] using dEnd
  · exact (later 69).trans aRealEnd
  · intro address
    exact (congrFun (dNat.trans (cNat.trans bNat)) address).trans (aNat address)
  · exact dReal.trans (cReal.trans (bReal.trans aReal))
  · have delta : d.rr 15 = cInput.rr 15 := by
      rw [← records.run]
      exact arithmeticRun_keeps_real_from_destination_list [0] (by decide) (by decide) cInput 5
    exact delta.trans (congrFun (cRR.trans (bRR.trans aRR)) 15)
  · intro r safe
    rw [← composite.run]
    exact arithmeticRun_keeps_from_destination_list _ (by decide) safe s _


end VehicleRoutingSurvey.Routing
end RppSource_MatchingAuxiliaryInit

/-! matching/MatchingInitialization.lean -/
section RppSource_MatchingInitialization
namespace VehicleRoutingSurvey.Routing



theorem allocateMatchingStageScratchBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns allocateMatchingStageScratchBlock 8 s t ∧ t.halted = false ∧
      t.nr 79 = s.nr 68 ∧ t.nr 80 = s.nr 68 + s.nr 55 ∧ t.nr 68 = s.nr 68 + 6 * s.nr 55 ∧
      t.nm = s.nm ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      ∀ r, r ∉ [0, 6, 14, 68, 79, 80] → t.nr r = s.nr r := by
  let seeded := {s with pc := 1, nr := Function.update s.nr 14 0}
  have seed : BlockRuns [.natConst 14 0] 1 s seeded := by
    apply BlockRuns.of_running_exit
    · simp [seeded, arithmeticStep, entry, running]
    · exact running
    · rfl
  let a := {seeded with pc := 0}
  have aFixed (r : ℕ) (safe : r ≠ 14 := by decide) : a.nr r = s.nr r := by simp [a, seeded, safe]
  obtain ⟨b, alloc, bLive, top, dfs, cursor, bNat, bReal, bRR, bFixed⟩ :=
    allocateMatchingCycleScratchBlock_correct (s := a) rfl running (by simp [a, seeded])
  let bInput := {b with pc := 0}
  obtain ⟨c, reserve, live, cEnd, natural, real, rr, cFixed⟩ :=
    reserveMatchingRebaseJobsBlock_correct (s := bInput) rfl bLive
  have bDim : bInput.nr 55 = s.nr 55 := (bFixed 55 (by decide)).trans (aFixed 55)
  have cursorAfter : c.nr 68 = s.nr 68 + 6 * s.nr 55 := by
    change c.nr 68 = _
    rw [cEnd, show bInput.nr 68 = a.nr 68 + 4 * a.nr 55 from cursor, aFixed 68, aFixed 55, bDim]
    omega
  have run : BlockRuns allocateMatchingStageScratchBlock 8 s _ := seed.append (alloc.append reserve)
  refine ⟨_, run, live, (cFixed 79 (by decide)).trans (top.trans (aFixed 68)),
    (cFixed 80 (by decide)).trans ?_, cursorAfter,
    natural.trans bNat, real.trans bReal, rr.trans bRR, ?_⟩
  · simpa only [aFixed 68, aFixed 55] using dfs
  · intro r safe
    exact (cFixed r (by simp at safe ⊢; omega)).trans ((bFixed r (by simp at safe ⊢; omega)).trans
      (aFixed r (by simp at safe; omega)))



set_option maxRecDepth 4096 in
theorem initializeWeightedMatchingBlock_correct {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {s : ArithmeticState} (input : CompactMateInput cost s) (entry : s.pc = 0) (running : s.halted = false) :
    let layout := MatchingWorkspace.allocate k (s.nr 63) (s.nr 64)
    ∃ t steps compact auxiliary, steps ≤ 32 * k * k + 82 * k + 90 ∧
      BlockRuns initializeWeightedMatchingBlock steps s t ∧ t.halted = false ∧
      CompactMatchingFirstStage cost layout s compact ∧ MatchingAuxiliaryInit {compact with pc := 0} auxiliary ∧
      t.nr 79 = auxiliary.nr 68 ∧ t.nr 80 = auxiliary.nr 68 + k ∧ t.nr 68 = auxiliary.nr 68 + 6 * k ∧
      t.nm = auxiliary.nm ∧ t.rm = auxiliary.rm ∧ t.rr = auxiliary.rr ∧
      ∀ r, r ∉ [0, 6, 14, 68, 79, 80] → t.nr r = auxiliary.nr r := by
  intro layout
  obtain ⟨a, preTicks, preCost, preparationRun, aLive, preFrame⟩ := prepareCompactMatchingBlock_correct input entry running
  let compact := {a with pc := 0}
  have pairEnd : compact.nr 69 = compact.nr 66 + compact.nr 55 * compact.nr 55 := by
    exact preFrame.workspace.realEnd.trans (by simp [compact, preFrame.pairCacheBases.2, preFrame.workspace.dimension])
  obtain ⟨b, init, bLive, initialized⟩ := initializeMatchingAuxiliaryBlock_correct (s := compact) rfl aLive
    preFrame.selector.2.1 pairEnd
  let auxiliary := {b with pc := 0}
  obtain ⟨c, reserve, live, map, stack, endAt, natural, real, reals, fixed⟩ :=
    allocateMatchingStageScratchBlock_correct (s := auxiliary) rfl bLive
  have size : auxiliary.nr 55 = k := (initialized.registers 55 (by decide)).trans preFrame.workspace.dimension
  have composed : BlockRuns initializeWeightedMatchingBlock (preTicks + ((5 * compact.nr 55 + 27) + 8)) s _ :=
    preparationRun.append (init.append reserve)
  rw [size] at stack endAt
  refine ⟨_, _, a, b, ?_, composed, live, preFrame, initialized, map, stack, endAt, natural, real, reals, fixed⟩
  change preTicks + ((5 * compact.nr 55 + 27) + 8) ≤ _
  rw [show compact.nr 55 = k from preFrame.workspace.dimension]
  omega


end VehicleRoutingSurvey.Routing
end RppSource_MatchingInitialization

/-! matching/MatchingInitializationView.lean -/
section RppSource_MatchingInitializationView
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 4096 in
/-- The full initialization realizes the empty matching, zero potentials, and singleton
partition, with a fresh registry and disjoint numerical scratch ranges. -/
theorem initializeWeightedMatchingBlock_primal {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {s : ArithmeticState} (input : CompactMateInput cost s) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t steps, steps ≤ 32 * k * k + 82 * k + 90 ∧
      BlockRuns initializeWeightedMatchingBlock steps s t ∧ t.halted = false ∧
      CompactMatchingPrimalDualMemory (initialCompactMatchingPrimalDual cost input.nonnegative input.symmetric) s t ∧
      (∀ v : Fin k, t.nm (t.nr 74 + v.val) = 0) ∧
      (∀ v : Fin k, t.nm (t.nr 57 + v.val) = v.val) ∧
      (∀ v : Fin k, t.rm (t.nr 62 + v.val) = 0) := by
  obtain ⟨t, steps, compact, auxiliary, price, run, live, ready, allocated,
    _, _, _, mt, rt, _, fixed⟩ := initializeWeightedMatchingBlock_correct input entry running
  let layout := MatchingWorkspace.allocate k (s.nr 63) (s.nr 64)
  have unchanged (r : ℕ) (noScratch : r ∉ [0, 6, 14, 68, 79, 80] := by decide)
      (noRegistry : r ∉ [0, 6, 7, 14, 23, 49, 68, 69, 74, 75, 76, 77, 78, 79, 80,
        83, 84, 85, 86, 88, 89, 90] := by decide) : t.nr r = compact.nr r :=
    (fixed r noScratch).trans (allocated.registers r noRegistry)
  have topBase : t.nr 74 = compact.nr 68 := (fixed 74 (by decide)).trans allocated.topNodes
  have dimension : compact.nr 55 = k := ready.workspace.dimension
  have originalMates : compact.nr 50 = layout.mates := ready.workspace.mates
  have originalReps : compact.nr 57 = layout.representatives := ready.workspace.representatives
  have originalPotential : compact.nr 62 = layout.potentials := ready.workspace.potentials
  have mateEnd : layout.mates + k ≤ compact.nr 68 := by
    rw [ready.workspace.naturalEnd]
    simp [layout, MatchingWorkspace.allocate] <;> omega
  have repEnd : layout.representatives + k ≤ compact.nr 68 := by
    rw [ready.workspace.naturalEnd]
    simp [layout, MatchingWorkspace.allocate] <;> omega
  have freeBase : s.nr 63 = layout.mates := rfl
  have low (a : ℕ) (before : a < compact.nr 68) : t.nm a = compact.nm a := by
    rw [mt, allocated.natural, if_neg (fun claim => (not_le_of_gt before) claim.1)]
  have usesMate : t.nr 50 = layout.mates := (unchanged 50).trans originalMates
  have math : CompactMatchingPrimalDualMemory (initialCompactMatchingPrimalDual cost
      input.nonnegative input.symmetric) s t := by
    refine ⟨(unchanged 55).trans dimension, (unchanged 56).trans ready.mapBase,
      freeBase.le.trans (le_of_eq usesMate.symm), ?_, ?_, ?_, ?_⟩
    · intro v
      have inside := v.isLt
      rw [usesMate, low _ (by omega)]
      simpa only [initialCompactMatchingPrimalDual, Finset.notMem_empty, if_false] using ready.mates v
    · intro r hi
      exact (unchanged r (by simp; omega) (by simp; omega)).trans (ready.saved r hi)
    · intro a before
      exact (low a (by omega)).trans (ready.natural a before)
    · intro a before
      rw [rt, allocated.real]
      exact ready.real a before
  refine ⟨t, steps, price, run, live, math, ?_, ?_, ?_⟩
  · intro v
    have inside := v.isLt
    rw [topBase, mt, allocated.natural]
    have inRegistry : compact.nr 68 ≤ compact.nr 68 + v.val ∧
        compact.nr 68 + v.val < compact.nr 68 + compact.nr 55 := by omega
    exact if_pos inRegistry
  · intro v
    have inside := v.isLt
    rw [unchanged 57, originalReps, low _ (by omega)]
    exact ready.representatives v
  · intro v
    rw [unchanged 62, originalPotential, rt, allocated.real]
    exact ready.potentials v


end VehicleRoutingSurvey.Routing
end RppSource_MatchingInitializationView

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

/-! matching/MatchingInitializationLayout.lean -/
section RppSource_MatchingInitializationLayout
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 8192 in
/-- The actual allocator installs the table relationships needed by a warm
search and gives the empty registry its first available identifier. -/
theorem initializeWeightedMatchingBlock_search_layout {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {s : ArithmeticState} (input : CompactMateInput cost s) (entry : s.pc = 0) (running : s.halted = false) :
    let state := initialCompactMatchingPrimalDual cost input.nonnegative input.symmetric
    let part := initialCompactMatchingPartition cost input.nonnegative input.symmetric
    let forest := resetAlternatingForest Finset.univ (fun _ : Fin k => none)
    ∃ t steps, steps ≤ 32 * k * k + 82 * k + 90 ∧ BlockRuns initializeWeightedMatchingBlock steps s t ∧
      t.halted = false ∧ MatchingWarmLayout t k ∧
      CompactMatchingPrimalDualMemory state s t ∧
      MatchingRefreshInput t part.representative (fun v => alternatingRoleCode (forest.role v)) cost
        (effectiveVertexPotential state.cuts state.potential state.cutDual) ∧
      Nonempty (MatchingSearchDualMemory part forest t) ∧
      (∃ records : MatchingTopMemberTrees k t, records.registryIds = []) ∧
      t.nr 76 = 1 ∧ t.nr 65 + 2 * (k * k) = t.nr 74 ∧ t.nr 66 + k * k = t.nr 75 ∧
      t.nr 62 = s.nr 64 ∧ t.nr 41 = 1 ∧ t.nr 42 = k / 2 := by
  intro state part forest
  obtain ⟨t, steps, compact, aux, bound, run, live, initial, placed, _, _, _, nat, real, _, stable⟩ :=
    initializeWeightedMatchingBlock_correct input entry running
  obtain ⟨u, elapsed, _, checked, _, primal, noNodes, repWords, potentialWords⟩ :=
    initializeWeightedMatchingBlock_primal input entry running
  have aligned := (checked.same_exit run).2
  subst u
  let w := MatchingWorkspace.allocate k (s.nr 63) (s.nr 64)
  have unchanged (r : ℕ) (noScratch : r ∉ [0, 6, 14, 68, 79, 80] := by decide)
      (noRegistry : r ∉ [0, 6, 7, 14, 23, 49, 68, 69, 74, 75, 76, 77, 78, 79, 80,
        83, 84, 85, 86, 88, 89, 90] := by decide) : t.nr r = compact.nr r :=
    (stable r noScratch).trans (placed.registers r noRegistry)
  have n50 : t.nr 50 = w.mates := (unchanged 50).trans initial.workspace.mates
  have n51 : t.nr 51 = w.roles := (unchanged 51).trans initial.workspace.roles
  have n52 : t.nr 52 = w.parents := (unchanged 52).trans initial.workspace.parents
  have n53 : t.nr 53 = w.depths := (unchanged 53).trans initial.workspace.depths
  have n54 : t.nr 54 = w.endpoints := (unchanged 54).trans initial.workspace.endpoints
  have n57 : t.nr 57 = w.representatives := (unchanged 57).trans initial.workspace.representatives
  have n58 : t.nr 58 = w.identifiers := (unchanged 58).trans initial.workspace.identifiers
  have n59 : t.nr 59 = w.slacks := (unchanged 59).trans initial.workspace.slacks
  have n60 : t.nr 60 = w.rates := (unchanged 60).trans initial.workspace.rates
  have n61 : t.nr 61 = 3 * k := (unchanged 61).trans initial.selector.2.2.2.1
  have n62 : t.nr 62 = w.potentials := (unchanged 62).trans initial.workspace.potentials
  have n65 : t.nr 65 = w.naturalEnd := (unchanged 65).trans initial.pairCacheBases.1
  have n66 : t.nr 66 = w.realEnd := (unchanged 66).trans initial.pairCacheBases.2
  have nodeBase : t.nr 74 = compact.nr 68 := (stable 74 (by decide)).trans placed.topNodes
  have cutBase : t.nr 75 = compact.nr 69 := (stable 75 (by decide)).trans placed.cutDuals
  have metricBase : t.nr 20 = s.nr 20 := (unchanged 20).trans initial.metric.1
  have offsetBase : t.nr 21 = s.nr 21 := (unchanged 21).trans initial.metric.2
  have natEnd : compact.nr 68 = w.naturalEnd + 2 * (k * k) := initial.workspace.naturalEnd
  have realEnd : compact.nr 69 = w.realEnd + k * k := initial.workspace.realEnd
  have legacy (v : Fin k) : t.rm (t.nr 62 + v.val) =
      effectiveVertexPotential state.cuts state.potential state.cutDual v := by
    simpa [state, initialCompactMatchingPrimalDual, effectiveVertexPotential] using potentialWords v
  have forestMemory : AlternatingForestMemory forest (t.nr 51) t.nm := by
    intro v
    have inside := v.isLt
    have prev (a : ℕ) (low : a < compact.nr 68) : t.nm a = compact.nm a := by
      rw [nat, placed.natural, if_neg (fun h => (not_le_of_gt low) h.1)]
    rw [n51]
    have low : w.roles + 3 * k ≤ compact.nr 68 := by rw [natEnd]; simp [w, MatchingWorkspace.allocate] <;> omega
    obtain ⟨role, parent, depth⟩ := initial.forest v
    exact ⟨(prev _ (by omega)).trans role, (prev _ (by omega)).trans parent, (prev _ (by omega)).trans depth⟩
  have cache : MatchingCacheLayout k t := by
    refine ⟨primal.dimension, n61, ?_, ?_, ?_, ?_⟩
    · simp [n58, n61, n54, w, MatchingWorkspace.allocate]
    · simp [n54, n61, n65, w, MatchingWorkspace.allocate] <;> omega
    · simp [n59, n61, n60, w, MatchingWorkspace.allocate]
    · simp [n60, n61, n66, w, MatchingWorkspace.allocate]
  have warm : MatchingWarmLayout t k := by
    refine ⟨primal.dimension, n61, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [n52, n51, w, MatchingWorkspace.allocate]
    · simp [n53, n51, w, MatchingWorkspace.allocate]
    · simp [n50, n51, w, MatchingWorkspace.allocate]
    · simp [n51, n57, w, MatchingWorkspace.allocate] <;> omega
    · simp [n57, n58, w, MatchingWorkspace.allocate]
    · simp [n58, n54, w, MatchingWorkspace.allocate]
    · simp [n58, n65, w, MatchingWorkspace.allocate] <;> omega
    · simp [n59, n60, w, MatchingWorkspace.allocate]
    · exact Nat.le_trans (Nat.le_add_right _ _) (cache.slacksBefore.trans
        (Nat.le_trans (Nat.le_add_right _ _) cache.ratesBefore))
    · simpa [offsetBase, n50, w, MatchingWorkspace.allocate] using input.naturalSpace
  have metricRoom : s.nr 20 + k * k ≤ s.nr 64 := by simpa only [pow_two] using input.realSpace
  have reads : MatchingRefreshInput t part.representative (fun v => alternatingRoleCode (forest.role v)) cost
      (effectiveVertexPotential state.cuts state.potential state.cutDual) := by
    refine ⟨cache, ?_, warm.candidatesAfter, ?_, ?_, ?_, ?_, repWords, fun v => (forestMemory v).1, ?_, legacy⟩
    · have offsets := warm.offsetsBefore
      have mates := warm.matesBefore
      have forestEnd : t.nr 51 ≤ t.nr 58 := by simp [n51, n58, w, MatchingWorkspace.allocate] <;> omega
      omega
    · simp [n51, n58, w, MatchingWorkspace.allocate] <;> omega
    · rw [metricBase, n59]
      exact metricRoom.trans (by simp [w, MatchingWorkspace.allocate])
    · simp [n62, n59, w, MatchingWorkspace.allocate]
    · intro v
      rw [offsetBase, primal.natural _ (by have h := v.isLt; have room := input.naturalSpace; omega)]
      exact input.rows v.val v.isLt
    · intro i j
      rw [metricBase]
      have fits := Nat.mul_le_mul_left k (Nat.succ_le_of_lt i.isLt)
      rw [Nat.mul_succ] at fits
      rw [primal.real _ (by have h := j.isLt; omega)]
      exact input.weights i j
  have dual : Nonempty (MatchingSearchDualMemory part forest t) := by
    refine ⟨⟨primal.dimension, ?_, repWords, forestMemory, legacy, fun _ => 0,
      ?_, ?_, ?_, ?_⟩⟩
    · rw [cutBase, realEnd, n62]
      simp [w, MatchingWorkspace.allocate] <;> omega
    · simp [state, initialCompactMatchingPrimalDual]
    · intro B inside
      exact (Finset.notMem_empty _ inside).elim
    · simp [state, initialCompactMatchingPrimalDual]
    · intro v
      have h : (part.blocks.block v).card = 1 := by simp [part, initialCompactMatchingPartition]
      simp [blossomNodeAt, noNodes v, h]
  let records : MatchingTopMemberTrees k t := ⟨fun _ => .nil,
    by intro v; simp [noNodes, MatchingMemberTree.rootKeys], fun _ => trivial, fun _ => trivial⟩
  refine ⟨t, steps, bound, run, live, warm, primal, reads, dual, ⟨records, by simp [records, MatchingTopMemberTrees.registryIds, MatchingMemberTree.registryIds]⟩,
    (stable 76 (by decide)).trans placed.nextNode, ?_, ?_, n62,
    (unchanged 41).trans initial.outer.1, (unchanged 42).trans initial.outer.2⟩
  · rw [n65, nodeBase, natEnd]
  · rw [n66, cutBase, realEnd]


end VehicleRoutingSurvey.Routing
end RppSource_MatchingInitializationLayout

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

theorem initializeWeightedMatchingBlock_storage {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {original t : ArithmeticState} {ticks : ℕ} (input : CompactMateInput cost original)
    (entry : original.pc = 0) (running : original.halted = false)
    (run : BlockRuns initializeWeightedMatchingBlock ticks original t) :
    MatchingStageStorage k original t ∧ MatchingCycleRecordOrder t := by
  obtain ⟨a, _, compact, aux, _, checked, _, init, layout, leafMap, stack, last, _, _, _, ports⟩ :=
    initializeWeightedMatchingBlock_correct input entry running
  have first := (checked.same_exit run).2
  subst a
  obtain ⟨a, _, _, tested, _, warm, _, _, _, _, cursor, natural, real, floor, _, _⟩ :=
    initializeWeightedMatchingBlock_search_layout input entry running
  have second := (tested.same_exit run).2
  subst a
  have keep (r : ℕ) (safe : r ∉ [0,6,14,68,79,80] := by decide) := ports r safe
  have size : compact.nr 55 = k := init.workspace.dimension
  have nodes : t.nr 74 = compact.nr 68 := (keep 74).trans layout.topNodes
  have start : t.nr 77 = compact.nr 68+k := by simpa only [keep 77, size] using layout.recordBases
  have length : t.nr 78 = compact.nr 68+k+matchingBlossomCapacity k := by
    simpa only [keep 78, size] using layout.recordLengths
  have left : t.nr 83 = compact.nr 68+k+2*matchingBlossomCapacity k := by simpa only [keep 83, size] using layout.traces.left
  have right : t.nr 84 = compact.nr 68+k+2*matchingBlossomCapacity k+k := by simpa only [keep 84, size] using layout.traces.right
  have marks : t.nr 85 = compact.nr 68+k+2*matchingBlossomCapacity k+k+k := by simpa only [keep 85, size] using layout.traces.marks
  have words : t.nr 90 = compact.nr 68+4*k+2*matchingBlossomCapacity k := by simpa only [keep 90, size] using layout.parentWitnesses
  have records : t.nr 86 = t.nr 90+2*k := by simpa only [keep 86, keep 90, size] using layout.workRecords
  have promoted : t.nr 88 = t.nr 86+k := by simpa only [keep 88, keep 86, size] using layout.promotionMarks
  have mask : t.nr 89 = t.nr 86+2*k := by simpa only [keep 89, keep 86, size] using layout.absorbedMarks
  have auxEnd : aux.nr 68 = t.nr 86+3*k := by simpa only [keep 86, size] using layout.naturalEnd
  have metric : t.nr 20+k*k ≤ t.nr 62 := by
    have metricBase : t.nr 20 = original.nr 20 :=
      (keep 20).trans ((layout.registers 20 (by decide)).trans init.metric.1)
    simpa only [metricBase, floor, pow_two] using input.realSpace
  refine ⟨⟨warm, floor, natural.symm, real.symm, ?_, ?_, ?_, ?_, ?_, ?_, records, promoted, ?_, ?_, ?_, metric⟩,
    MatchingCycleRecordOrder.empty ?_ cursor⟩
  all_goals first | omega | unfold matchingRebaseScratchEnd; rw [warm.size]; omega


end VehicleRoutingSurvey.Routing
end RppSource_MatchingStageStorage

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

/-! matching/MatchingChosenStage.lean -/
section RppSource_MatchingChosenStage
namespace VehicleRoutingSurvey.Routing



theorem MatchingActiveStage.selectedState {k stage : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {positive : 0 < k} {cutAt : Fin k → Finset (Fin k)}
    {original s t : ArithmeticState} {ticks : ℕ} (active : MatchingActiveStage part forest positive cutAt original stage s)
    (even : Even k) (incomplete : state.covered ≠ Finset.univ) (callerFloor : original.nr 64 ≤ s.nr 59)
    (cutBase : s.nr 66+k*k ≤ s.nr 75) (run : BlockRuns selectAndAdvanceDualSlackBlock ticks s t)
    (minimum : DualBoundMinimum s (s.nr 8) t) (natural : t.nm = s.nm)
    (real : ∀ a, t.rm a = if t.nr 1 ≠ 0 ∧ s.nr 4 ≤ a ∧ a < s.nr 4+s.nr 8 then
      s.rm a - t.rr 1 * s.rm (s.nr 5+(a-s.nr 4)) else s.rm a) :
    t.nr 1 ≠ 0 ∧ ∃ view : MatchingChosenStage part forest positive cutAt original t,
      view.dual.node = active.dual.node ∧ view.registry.trees.tree = active.registry.trees.tree := by
  obtain ⟨nonzero, ⟨event, choice, kind, adjustment⟩, valid, least, keys⟩ :=
    selectedMatchingSearch_step active.search even incomplete active.rows active.dual.roles active.dual.reps
      run minimum natural real
  obtain ⟨fixed, realReg⟩ := selectAndAdvanceDualSlackBlock_keeps_registers run
  have port (r : ℕ) (safe : r ∉ [0,1,2,6,7,10,11] := by decide) := fixed r safe
  have below (a : ℕ) (floor : a < s.nr 59) : t.rm a = s.rm a := by
    rw [real, if_neg]
    intro hit
    have lo := active.rows.slacks
    omega
  have above (a : ℕ) (floor : s.nr 75 ≤ a) : t.rm a = s.rm a := by
    rw [real, if_neg]
    intro hit
    have count := active.rows.count
    have lo := active.rows.slacks
    have mid := active.rows.layout.slacksBefore
    have high := active.rows.layout.ratesBefore
    omega
  have read := active.reads.keeps (t := t) ⟨fun a _ => congrFun natural a, fun a h _ _ => below a h⟩
    (fun r h => port r (by simp [matchingRefreshTableRegisters] at h; simp; omega))
  have primal := active.primal
  have mate : CompactMatchingPrimalDualMemory state original t := by
    refine ⟨read.layout.dimension, (port 56).trans primal.oddMap, ?_, ?_, ?_, ?_, ?_⟩
    · rw [port 50]; exact primal.mateAbove
    · intro v
      rw [natural, port 50]
      exact primal.mate v
    · intro r high
      exact (port r (by simp; omega)).trans (primal.saved r high)
    · intro a h
      exact (congrFun natural a).trans (primal.natural a h)
    · intro a h
      exact (below a (h.trans_le callerFloor)).trans (primal.real a h)
  have top (v : Fin k) : blossomNodeAt t v = blossomNodeAt s v := by simp only [blossomNodeAt, port 74, natural]
  let dual : MatchingSearchDualMemory part forest t := {
    dimension := read.layout.dimension
    separated := by rw [port 62, port 75]; exact active.dual.separated
    reps := read.representatives
    roles := by rw [natural, port 51]; exact active.dual.roles
    effective := read.potentials
    node := active.dual.node
    nodeNonzero := active.dual.nodeNonzero
    nodeInjective := active.dual.nodeInjective
    cutValues B inside := by rw [port 75, above _ (by omega)]; exact active.dual.cutValues B inside
    top v := (top v).trans (active.dual.top v) }
  let registry : MatchingRegistryView dual := active.registry.transport rfl (port 77) (port 78) (port 76)
    (port 65) top (fun a _ => congrFun natural a)
  have words (v : Fin k) : matchingForestWitnessAt t.nm (t.nr 90) v.val = matchingForestWitnessAt s.nm (s.nr 90) v.val := by
    rw [natural, port 90]
  have pairs : MatchingSearchOuterBuckets t part.representative (fun v => alternatingRoleCode (forest.role v)) cost
      (effectiveVertexPotential state.cuts state.potential state.cutDual) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simpa only [MatchingPairBucketValid, port 65, natural] using active.pairs.valid i hi
    · intro a b diff left right
      rw [keys, realReg 15 (by decide)]
      exact active.pairs.least a b diff left right
    · intro a b off
      exact (keys _).trans (active.pairs.inactive a b off)
  refine ⟨nonzero, ⟨event, choice, kind, adjustment, mate, dual, registry, read, ?_,
    active.links.advance rfl words, pairs, fun i h => valid i (port 61 ▸ h), least⟩, rfl, rfl⟩
  intro child parent link
  simpa only [natural, port 90] using active.witnesses link


end VehicleRoutingSurvey.Routing
end RppSource_MatchingChosenStage

/-! matching/MatchingInterstageView.lean -/
section RppSource_MatchingInterstageView
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory





theorem CompactMatchingInterstage.terminal {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {original s : ArithmeticState} (view : CompactMatchingInterstage cost original (k / 2) s)
    (even : k % 2 = 0) : Nonempty (MatchingTerminalCertificate k cost original s) :=
  CompactMatchingPrimalDual.toTerminal view.primal even view.count

theorem initialCompactMatchingTop {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (nonnegative : ∀ u v, 0 ≤ cost u v) (symmetric : ∀ u v, cost u v = cost v u) :
    CompactTopMatching (initialCompactMatchingPartition cost nonnegative symmetric) := by
  constructor
  · intro v w member unequal
    have isV : w = v := Finset.mem_singleton.mp member
    exact (unequal isV).elim
  · intro v w _ mate
    have empty := ((initialCompactMatchingPrimalDual cost nonnegative symmetric).partialMate_some_iff).mp mate
    exact (Finset.notMem_empty _ empty).elim



/-- The terminal certificate reads the same memory after removing the loop's
private counter and local program counter. -/
theorem CompactMatchingInterstage.terminal_unsnapshot {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {original result : ArithmeticState} (view : CompactMatchingInterstage cost original (k / 2) (matchingLoopSnapshot result))
    (even : k % 2 = 0) : Nonempty (MatchingTerminalCertificate k cost original result) := by
  obtain ⟨certificate⟩ := view.terminal even
  refine ⟨⟨certificate.mate, certificate.cuts, certificate.potential, certificate.cutDual,
    certificate.dimension, certificate.mapBase, certificate.mateAbove, certificate.mateBytes, certificate.validMate,
    ?_, certificate.natural, certificate.real, certificate.cutValid, certificate.feasible,
    certificate.tight, certificate.internal⟩⟩
  intro r high
  have different : r ≠ 40 := by omega
  simpa only [matchingLoopSnapshot, Function.update_of_ne different] using certificate.saved r high


end VehicleRoutingSurvey.Routing
end RppSource_MatchingInterstageView

/-! matching/MatchingInitialRegistry.lean -/
section RppSource_MatchingInitialRegistry
namespace VehicleRoutingSurvey.Routing

/-- A partition into singleton blocks with no registered cuts has empty
typed trees at the actual top-node addresses. -/
def MatchingRegistryView.of_empty {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {s : ArithmeticState}
    (dual : MatchingSearchDualMemory part forest s) (empty : state.cuts = ∅)
    (single : ∀ v, (part.blocks.block v).card = 1) : MatchingRegistryView dual := by
  have zero (v : Fin k) : s.nm (s.nr 74+v.val) = 0 := by
    change blossomNodeAt s v = 0
    simp [dual.top, single]
  let trees : MatchingTopMemberTrees k s := {
    tree := fun _ => .nil
    roots := by intro v; simp [zero, MatchingMemberTree.rootKeys]
    proper := fun _ => trivial
    encoded := fun _ => trivial }
  have ids : trees.registryIds = [] := by
    simp [trees, MatchingTopMemberTrees.registryIds, MatchingMemberTree.registryIds]
  refine ⟨trees, fun _ => trivial, by simp [ids], ?_, ?_, ?_, ?_, ?_⟩ <;> simp [empty, ids]


end VehicleRoutingSurvey.Routing
end RppSource_MatchingInitialRegistry

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

theorem initializeWeightedMatchingBlock_between {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {original t : ArithmeticState} {ticks : ℕ} (input : CompactMateInput cost original)
    (entry : original.pc = 0) (running : original.halted = false)
    (init : BlockRuns initializeWeightedMatchingBlock ticks original t) :
    Nonempty (MatchingBetweenStages cost original 0 (matchingLoopSnapshot t)) := by
  obtain ⟨u, _, _, run, _, _, primal, reads, ⟨dual⟩, _, cursor, _, _, _, _, _⟩ :=
    initializeWeightedMatchingBlock_search_layout input entry running
  have eq := (run.same_exit init).2
  subst u
  let state := initialCompactMatchingPrimalDual cost input.nonnegative input.symmetric
  let part := initialCompactMatchingPartition cost input.nonnegative input.symmetric
  let graph : CompactMatchingInterstage cost original 0 t := ⟨state, part,
    initialCompactMatchingTop input.nonnegative input.symmetric, rfl,
    by simp [CompactMatchingPrimalDual.InternalCuts, state, initialCompactMatchingPrimalDual], primal,
    reads.representatives, reads.potentials⟩
  let reg := MatchingRegistryView.of_empty dual rfl (by intro v; simp [part, initialCompactMatchingPartition])
  obtain ⟨storage, order⟩ := initializeWeightedMatchingBlock_storage input entry running init
  let old : MatchingBetweenStages cost original 0 t := ⟨graph, _, dual, reg, MatchingLiveCycles.empty reg rfl,
    storage, order, by simp [cursor], reads⟩
  exact ⟨old.reframe (t := matchingLoopSnapshot t) rfl rfl (fun r _ away => Function.update_of_ne away _ _)⟩

theorem MatchingBetweenStages.terminal {k : ℕ} {cost : Fin k → Fin k → ℝ} {original t : ArithmeticState}
    (input : CompactMateInput cost original) (done : MatchingBetweenStages cost original (k/2) (matchingLoopSnapshot t)) :
    Nonempty (MatchingTerminalCertificate k cost original t) := done.graph.terminal_unsnapshot input.even


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




end VehicleRoutingSurvey.Routing
end RppSource_MatchingChosenFrame

/-! matching/MatchingDispatchState.lean -/
section RppSource_MatchingDispatchState
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory



theorem MatchingPreparedStage.select {k i : ℕ} {cost : Fin k → Fin k → ℝ}
    {original s t : ArithmeticState} {ticks : ℕ}
    (stage : MatchingPreparedStage cost original i (matchingStageSnapshot s))
    (input : CompactMateInput cost original) (searching : i < k/2)
    (run : BlockRuns selectAndAdvanceDualSlackBlock ticks s t) (minimum : DualBoundMinimum s (s.nr 8) t)
    (natural : t.nm = s.nm) (real : ∀ a, t.rm a = if t.nr 1 ≠ 0 ∧ s.nr 4 ≤ a ∧ a < s.nr 4+s.nr 8 then
      s.rm a - t.rr 1*s.rm (s.nr 5+(a-s.nr 4)) else s.rm a) :
    t.nr 1 ≠ 0 ∧ t.nr 1 ≤ t.nr 61 ∧ ∃ _ : MatchingDispatchState cost original i {t with pc := 0},
      matchingStageCountsFromRAM k (matchingStageSnapshot s) ((matchingStageSnapshot s).nr 39) =
        matchingStageCountsFromRAM k {t with pc := 0} (t.nr 39) := by
  let old := matchingStageSnapshot s
  let out := {t with pc := 0}
  have snap (r : ℕ) (away : r ≠ 30 := by decide) : old.nr r = s.nr r := Function.update_of_ne away _ _
  let active := stage.active.reframe (t := s) rfl rfl rfl (fun r away _ => (snap r away).symm)
  have incomplete : stage.state.covered ≠ Finset.univ := by
    intro covered
    have count := perfectMatching_card_twice stage.state.perfect
    rw [stage.count, covered, Finset.card_univ, Fintype.card_fin] at count
    omega
  have floor : original.nr 64 ≤ s.nr 59 := by
    have a := stage.storage.inputFloor
    have b := stage.active.reads.effectiveBefore
    change s.nr 62 = original.nr 64 at a
    change s.nr 62+k ≤ s.nr 59 at b
    omega
  obtain ⟨used,⟨chosen, ids, trees⟩⟩ := active.selectedState (Nat.even_iff.mpr input.even) incomplete floor
    (by change s.nr 66+k*k ≤ s.nr 75; exact stage.storage.cutDuals.ge) run minimum natural real
  let selected := chosen.reframe (t := out) rfl rfl rfl rfl rfl (fun _ _ => rfl)
  obtain ⟨fixed,_⟩ := selectAndAdvanceDualSlackBlock_keeps_registers run
  have port (r : ℕ) (safe : r ∉ [0,1,2,6,7,10,11] := by decide) (snapSafe : r ≠ 30 := by decide) :
      out.nr r = old.nr r := (fixed r safe).trans (snap r snapSafe).symm
  have winner : t.nr 1 ≤ t.nr 61 := by
    obtain ⟨row, inside, present, id, _⟩ := minimum.1 used
    have count : s.nr 8 = old.nr 61 := (snap 8).symm.trans stage.active.rows.count
    have cell : dualBoundIdentifier s row = old.nm (old.nr 58+row) := by
      rw [dualBoundIdentifier, ← snap 3, stage.active.rows.ids]
      rfl
    have occupied := present.1
    rw [cell] at id occupied
    obtain empty | ⟨own, _⟩ := stage.active.rows.valid row (count ▸ inside)
    · exact (occupied empty).elim
    · rw [id, own]
      change row + 1 ≤ out.nr 61
      rw [port 61]
      omega
  have registryIds : selected.dual.node = stage.active.dual.node := ids
  have treeIds : selected.registry.trees.tree = stage.active.registry.trees.tree := trees
  have kept : MatchingLiveCycles selected.registry := stage.cycles.sameNodes selected.registry registryIds treeIds
    (fun B h => (stage.cycles.memory B h).sameMemory natural (fun r mem =>
      port r (by simp at mem ⊢; omega) (by simp at mem; omega)))
  have store := stage.storage.keeps (t := out) (fun r mem => port r
    (by simp [matchingFixedStorageRegisters] at mem; simp; omega) (by simp [matchingFixedStorageRegisters] at mem; omega))
  have bytes : out.nm = old.nm := natural
  have order := stage.order.transport (s := old) (t := out) (by simp [matchingRebaseScratchEnd, port 80, port 55])
    (port 76) (port 68) (fun _ _ _ => by simp only [matchingCycleRecordStart, port 77, bytes])
    (fun _ _ _ => by simp only [matchingCycleRecordEnd, matchingCycleRecordStart, port 77, port 78, bytes])
  have countEq : matchingStageCountsFromRAM k out (out.nr 39) = matchingStageCountsFromRAM k old (old.nr 39) := by
    rw [matchingStageCountsFromRAM_eq selected.dual stage.positive _ selected.registry.trees selected.registry.unique selected.registry.keys,
      matchingStageCountsFromRAM_eq stage.active.dual stage.positive _ stage.active.registry.trees stage.active.registry.unique stage.active.registry.keys,
      registryIds, port 39]
  have budget := stage.active.budget.keeps (port 39) (port 76) countEq
  refine ⟨used,winner,⟨stage.state,stage.part,stage.forest,stage.positive,stage.count,active.top,active.internal,active.search,
    selected,kept,store,order,?_,budget,(port 9).trans stage.active.unit⟩,countEq.symm⟩
  rw [registryIds,port 39]; exact stage.active.freshCuts






end VehicleRoutingSurvey.Routing
end RppSource_MatchingDispatchState

/-! matching/MatchingDispatchTraceFrame.lean -/
section RppSource_MatchingDispatchTraceFrame
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory















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

/-! matching/MatchingProgram.lean -/
section RppSource_MatchingProgram
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory







set_option maxRecDepth 32768 in
set_option maxHeartbeats 3200000 in
/-- Every event arm preserves the stage controls and the fixed table bases. -/
theorem weightedBlossomEventHandler_keeps_stage {s t : ArithmeticState} {steps r : ℕ}
    (run : BlockRuns weightedBlossomEventHandler steps s t)
    (kept : r ∈ [30, 31, 32, 34, 39] ++ matchingFixedStorageRegisters) : t.nr r = s.nr r := by
  have avoids : weightedBlossomEventHandler.all
      (fun ins => decide (naturalDestination ins ∉ [30, 31, 32, 34, 39] ++ matchingFixedStorageRegisters)) = true := by
    decide
  exact run.run ▸ arithmeticRun_keeps_register
    (fun ins present same => (of_decide_eq_true (List.all_eq_true.mp avoids ins present)) (same ▸ kept)) s steps








end VehicleRoutingSurvey.Routing
end RppSource_MatchingProgram

/-! matching/MatchingLoopRefinement.lean -/
section RppSource_MatchingLoopRefinement
namespace VehicleRoutingSurvey.Routing

/-- A continuing event leaves a prepared forest. A finishing event installs
the original-vertex matching for the next iteration in the same RAM. -/
def matchingLoopFrame {k : ℕ} (cost : Fin k → Fin k → ℝ) (original : ArithmeticState)
    (i : ℕ) (s : ArithmeticState) : Prop :=
  (s.nr 33 ≠ 0 ∧ Nonempty (MatchingPreparedStage cost original i s)) ∨
  (s.nr 33 = 0 ∧ Nonempty (MatchingBetweenStages cost original (i+1) s))



theorem matchingLoopFrame_ready {k i : ℕ} {cost : Fin k → Fin k → ℝ} {original s : ArithmeticState}
    (frame : matchingLoopFrame cost original i (matchingStageSnapshot s)) (on : s.nr 33 ≠ 0) :
    s.nr 1 = 0 ∧ s.nr 9 = 1 ∧ s.nr 8 ≤ 3*k ∧
    ∀ j < s.nr 8, ¬ (s.nr 4 ≤ s.nr 5+j ∧ s.nr 5+j < s.nr 4+s.nr 8) := by
  rcases frame with ⟨_,⟨stage⟩⟩ | ⟨off,_⟩
  · have read := stage.active.rows
    exact ⟨stage.active.winnerEmpty,stage.active.unit,(read.count.trans read.layout.rows).le,read.separated⟩
  · exact (on off).elim

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3200000 in
theorem matchingPreparationAndStage_loopControls {s t : ArithmeticState} {ticks : ℕ}
    (run : BlockRuns (appendBlock prepareWeightedMatchingStageBlock (matchingStageProgram weightedBlossomEventHandler)) ticks s t)
    {r : ℕ} (used : r ∈ ([40,41,42] : List ℕ)) : t.nr r = s.nr r := by
  have avoids : (appendBlock prepareWeightedMatchingStageBlock (matchingStageProgram weightedBlossomEventHandler)).all
      (fun ins => decide (naturalDestination ins ∉ ([40,41,42] : List ℕ))) = true := by decide
  rw [← run.run]
  exact arithmeticRun_keeps_register (fun ins h eq => (of_decide_eq_true (List.all_eq_true.mp avoids ins h)) (eq ▸ used)) s ticks

/-- The allocator, every warm preparation, the final certificate, and the
outer counted loop consume these concrete payloads. The only remaining
input to the program-level proof is the checked search-event dispatcher. -/
noncomputable def weightedBlossomRefinement_of_handler {k : ℕ} {cost : Fin k → Fin k → ℝ} {original : ArithmeticState}
    (input : CompactMateInput cost original) (entry : original.pc = 0) (running : original.halted = false)
    (handler : ∀ i < k/2, ∀ s selected selectSteps,
      Nonempty (MatchingPreparedStage cost original i (matchingStageSnapshot s)) → s.nr 33 ≠ 0 →
      BlockRuns selectAndAdvanceDualSlackBlock selectSteps s selected → selected.halted = false →
      DualBoundMinimum s (s.nr 8) selected → selected.nm = s.nm →
      (∀ a, selected.rm a = if selected.nr 1 ≠ 0 ∧ s.nr 4 ≤ a ∧ a < s.nr 4 + s.nr 8 then
        s.rm a - selected.rr 1 * s.rm (s.nr 5 + (a - s.nr 4)) else s.rm a) →
      ∃ next ticks, BlockRuns weightedBlossomEventHandler ticks {selected with pc := 0} next ∧
        next.halted = false ∧ matchingLoopFrame cost original i (matchingStageSnapshot next) ∧
        ((next.nr 33 = 0 ∧ ticks ≤ 512*(k^2+1)) ∨
          (next.nr 33 ≠ 0 ∧ ∃ charge,
            MatchingStageTransition (matchingLoopCounts k i (matchingStageSnapshot s)) charge
              (matchingLoopCounts k i (matchingStageSnapshot next)) ∧ ticks ≤ 1024*(k+1)*charge))) :
    WeightedMatchingRefinement k cost original where
  interstage i s := Nonempty (MatchingBetweenStages cost original i s)
  active := matchingLoopFrame cost original
  counts := matchingLoopCounts k
  initial _ _ run := initializeWeightedMatchingBlock_between input entry running run
  certificate _ h := h.elim (fun view => view.terminal input)
  loop := {
    initializeStage := by
      rintro i before s pc live _ _ _ ⟨old⟩
      obtain ⟨t, ticks, limit, run, ready, size, zero, on, one, prepared, credit⟩ := old.prepare before input pc live
      exact ⟨t,ticks,limit,run,ready,size,zero,one,Or.inl ⟨(by change t.nr 33 ≠ 0; omega),prepared⟩,credit⟩
    handlerChecked := by
      intro i before
      refine ⟨fun _ frame active => matchingLoopFrame_ready frame active, ?_⟩
      intro s selected selectSteps frame active picked live minimum natural real
      rcases frame with ⟨_, prepared⟩ | ⟨off, _⟩
      · obtain ⟨next, ticks, run, nextLive, nextFrame, charge⟩ :=
          handler i before s selected selectSteps prepared active picked live minimum natural real
        have kept := (selectAndAdvanceDualSlackBlock_keeps_registers picked).1
        exact ⟨next, ticks, run, nextLive, nextFrame,
          (weightedBlossomEventHandler_keeps_stage run (r := 30) (by decide)).trans (kept 30 (by decide)),
          (weightedBlossomEventHandler_keeps_stage run (r := 31) (by decide)).trans (kept 31 (by decide)),
          (weightedBlossomEventHandler_keeps_stage run (r := 32) (by decide)).trans (kept 32 (by decide)),
          (weightedBlossomEventHandler_keeps_stage run (r := 34) (by decide)).trans (kept 34 (by decide)), charge⟩
      · exact (active off).elim
    augmented := by
      intro i before s t ticks _ run frame off
      rcases frame with ⟨active,_⟩ | ⟨_,⟨next⟩⟩
      · exact (active off).elim
      · have transferred := next.reframe (t := matchingLoopSnapshot t) rfl rfl (by
          intro r otherStage otherLoop
          simp only [matchingStageSnapshot,matchingLoopSnapshot,Function.update_of_ne otherStage,Function.update_of_ne otherLoop])
        exact ⟨⟨transferred⟩,matchingPreparationAndStage_loopControls run (by decide),
          matchingPreparationAndStage_loopControls run (by decide),matchingPreparationAndStage_loopControls run (by decide)⟩ }


end VehicleRoutingSurvey.Routing
end RppSource_MatchingLoopRefinement

/-! matching/MatchingDispatchComplete.lean -/
section RppSource_MatchingDispatchComplete
namespace VehicleRoutingSurvey.Routing

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
noncomputable def weightedBlossomRefinement {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {original : ArithmeticState} (input : CompactMateInput cost original)
    (entry : original.pc = 0) (running : original.halted = false) :
    WeightedMatchingRefinement k cost original := by
  apply weightedBlossomRefinement_of_handler input entry running
  intro i searching s selected selectSteps prepared active picked live minimum natural real
  obtain ⟨stage⟩ := prepared
  obtain ⟨_, winner, before, counts⟩ := stage.select input searching picked minimum natural real
  let m := {selected with pc := 0}
  change MatchingDispatchState cost original i m at before
  have on : m.nr 33 ≠ 0 := fun off =>
    active (((selectAndAdvanceDualSlackBlock_keeps_registers picked).1 33 (by decide)).symm.trans off)
  have continueEvent : (∃ next ticks charge,
      BlockRuns weightedBlossomEventHandler ticks m next ∧ next.halted = false ∧ next.nr 33 ≠ 0 ∧
      Nonempty (MatchingPreparedStage cost original i (matchingStageSnapshot next)) ∧
      MatchingStageTransition (matchingLoopCounts k i m) charge (matchingLoopCounts k i (matchingStageSnapshot next)) ∧
      ticks ≤ 1024*(k+1)*charge) →
      (∃ next ticks, BlockRuns weightedBlossomEventHandler ticks m next ∧
        next.halted = false ∧ matchingLoopFrame cost original i (matchingStageSnapshot next) ∧
        ((next.nr 33 = 0 ∧ ticks ≤ 512*(k^2+1)) ∨
          (next.nr 33 ≠ 0 ∧ ∃ charge,
            MatchingStageTransition (matchingLoopCounts k i (matchingStageSnapshot s)) charge
              (matchingLoopCounts k i (matchingStageSnapshot next)) ∧ ticks ≤ 1024*(k+1)*charge))) := by
    rintro ⟨next,ticks,charge,ran,after,on,ready,paid,bounded⟩
    refine ⟨next,ticks,ran,after,Or.inl ⟨on,ready⟩,Or.inr ⟨on,charge,?_,bounded⟩⟩
    change MatchingStageTransition (matchingStageCountsFromRAM k (matchingStageSnapshot s) ((matchingStageSnapshot s).nr 39))
      charge (matchingLoopCounts k i (matchingStageSnapshot next))
    rw [counts]
    exact paid
  have eventClass : matchingEventClass m = 0 ∨ matchingEventClass m = 1 ∨ matchingEventClass m = 2 := by
    unfold matchingEventClass
    split
    · exact Or.inr (Or.inr rfl)
    · split
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  rcases eventClass with grow | outer | expand
  · exact continueEvent (before.grow searching input.symmetric rfl live on grow)
  · obtain ⟨a,b,_,_,_,_,_,_,middle,spent,_,classify,_,_,_,_,_,_,_,_,_,_,ready,_,_,traces⟩ :=
      before.traceOuter rfl live outer
    by_cases same : before.forest.commonAncestor (before.part.representative a) (before.part.representative b) = none
    · have tag : middle.nr 35 = 3 := by simpa only [same, if_true] using traces.tag
      obtain ⟨next,ticks,ran,nextLive,off,between,bounded⟩ := before.augment searching rfl live outer winner classify tag
      exact ⟨next,ticks,ran,nextLive,Or.inr ⟨off,between⟩,Or.inl ⟨off,bounded⟩⟩
    · have tag : middle.nr 35 = 1 := by simpa only [if_neg same] using traces.tag
      exact continueEvent (before.contract searching input.symmetric rfl live on outer winner classify tag)
  · exact continueEvent (before.expand searching input.symmetric rfl live on expand)

/-- Correctness and instruction bound of the fixed arithmetic-RAM matcher. -/
theorem weightedBlossomMatchingBlock_checked :
    CompactMateBlockSpec weightedBlossomMatchingBlock 27648 :=
  weightedBlossomMatchingBlock_spec_at_entry
    (fun input entry running => ⟨weightedBlossomRefinement input entry running⟩)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingDispatchComplete

open VehicleRoutingSurvey.Routing SupplyChainTheory in
theorem solution : ∃ matching : List ArithmeticInstruction, CompactMateBlockSpec matching 27648 :=
  ⟨weightedBlossomMatchingBlock, VehicleRoutingSurvey.Routing.weightedBlossomMatchingBlock_checked⟩
