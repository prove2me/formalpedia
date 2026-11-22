-- Prove2me | solution 1 for VehicleRoutingSurvey.Routing.weightedBlossomMatchingBlock_spec_at_entry
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T16:07:57.314229+00:00
-- url     : https://prove2.me/submissions/ed3fe170-f449-47b9-a818-07b08944e674

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

/-! matching/WeightedDeltaRAM.lean -/
section RppSource_WeightedDeltaRAM
namespace VehicleRoutingSurvey.Routing



private noncomputable def preparedDualBound (s : ArithmeticState) : ArithmeticState :=
  let initial := {s with pc := 6, rr := Function.update s.rr 4 0}
  if s.rr 3 ≤ 0 then {initial with nr := Function.update initial.nr 0 0}
  else {initial with rr := Function.update initial.rr 0 (s.rr 0 / s.rr 3)}

private theorem prepareDualBoundBlock_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) : BlockRuns prepareDualBoundBlock 4 s (preparedDualBound s) := by
  classical
  have instructionResult : (arithmeticStep prepareDualBoundBlock)^[4] s = preparedDualBound s := by
    by_cases nonpositive : s.rr 3 ≤ 0 <;>
      simp [prepareDualBoundBlock, arithmeticStep, Function.iterate_succ_apply', entry, running,
        preparedDualBound, nonpositive]
  apply BlockRuns.of_running_exit instructionResult
  · by_cases nonpositive : s.rr 3 ≤ 0 <;> simp [preparedDualBound, nonpositive, running]
  · by_cases nonpositive : s.rr 3 ≤ 0 <;> simp [preparedDualBound, nonpositive, prepareDualBoundBlock]



def mergeDualBoundTakesCandidate (s : ArithmeticState) : Prop :=
  s.nr 0 ≠ 0 ∧ 0 < s.rr 3 ∧ (s.nr 1 = 0 ∨ s.rr 0 / s.rr 3 < s.rr 1)

/-- A candidate is normalized to its slack divided by its positive rate and compared to
the previous minimum in at most eleven instructions. -/
theorem mergeDualBoundBlock_spec (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ steps ≤ 11, let result := (arithmeticStep mergeDualBoundBlock)^[steps] s
      BlockRuns mergeDualBoundBlock steps s result ∧
      (mergeDualBoundTakesCandidate s → result.nr 1 = s.nr 0 ∧ result.rr 1 = s.rr 0 / s.rr 3) ∧
      (¬mergeDualBoundTakesCandidate s → result.nr 1 = s.nr 1 ∧ result.rr 1 = s.rr 1) ∧
      result.nm = s.nm ∧ result.rm = s.rm := by
  classical
  let middle := {preparedDualBound s with pc := 0}
  have middleLive : middle.halted = false := by
    by_cases nonpositive : s.rr 3 ≤ 0 <;> simp [middle, preparedDualBound, nonpositive, running]
  have unchanged : middle.nr 1 = s.nr 1 ∧ middle.rr 1 = s.rr 1 ∧ middle.nm = s.nm ∧ middle.rm = s.rm := by
    by_cases nonpositive : s.rr 3 ≤ 0 <;> simp [middle, preparedDualBound, nonpositive]
  have equivalent : mergeSlackEntryTakesCandidate middle ↔ mergeDualBoundTakesCandidate s := by
    by_cases nonpositive : s.rr 3 ≤ 0
    · simp [middle, preparedDualBound, mergeSlackEntryTakesCandidate, mergeDualBoundTakesCandidate,
        nonpositive, not_lt_of_ge nonpositive]
    · simp [middle, preparedDualBound, mergeSlackEntryTakesCandidate, mergeDualBoundTakesCandidate,
        nonpositive, lt_of_not_ge nonpositive]
  obtain ⟨steps, short, compared, chosen, kept, natMem, realMem⟩ := mergeSlackEntryBlock_spec middle rfl middleLive
  have joined := BlockRuns.append (prepareDualBoundBlock_spec s entry running) compared
  refine ⟨4 + steps, by omega, ?_⟩
  dsimp only
  rw [mergeDualBoundBlock, joined.run]
  refine ⟨joined, ?_, ?_, natMem.trans unchanged.2.2.1, realMem.trans unchanged.2.2.2⟩
  · intro take
    have found := chosen (equivalent.mpr take)
    have positive : 0 < s.rr 3 := take.2.1
    have registers : middle.nr 0 = s.nr 0 ∧ middle.rr 0 = s.rr 0 / s.rr 3 := by
      simp [middle, preparedDualBound, not_le.mpr positive]
    exact ⟨found.1.trans registers.1, found.2.trans registers.2⟩
  · intro skip
    have found := kept (fun take => skip (equivalent.mp take))
    exact ⟨found.1.trans unchanged.1, found.2.trans unchanged.2.1⟩

end VehicleRoutingSurvey.Routing
end RppSource_WeightedDeltaRAM

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

private theorem mergeDualBoundBlock_low_writes (r : ℕ) (high : 3 ≤ r) :
    ∀ ins ∈ mergeDualBoundBlock, naturalDestination ins < r := by
  simp [mergeDualBoundBlock, appendBlock, prepareDualBoundBlock, mergeSlackEntryBlock,
    relocateInstruction, naturalDestination] <;> omega

private theorem mergeDualBoundBlock_no_halt : ArithmeticInstruction.halt ∉ mergeDualBoundBlock := by
  simp [mergeDualBoundBlock, appendBlock, prepareDualBoundBlock, mergeSlackEntryBlock, relocateInstruction]



private def dualBoundReadState (s : ArithmeticState) : ArithmeticState :=
  let idAddress := s.nr 3 + s.nr 7
  let slackAddress := s.nr 4 + s.nr 7
  let rateAddress := s.nr 5 + s.nr 7
  {s with
    pc := 6
    nr := Function.update (Function.update (Function.update (Function.update s.nr 6 idAddress)
      0 (s.nm idAddress)) 6 slackAddress) 6 rateAddress
    rr := Function.update (Function.update s.rr 0 (s.rm slackAddress)) 3 (s.rm rateAddress)}

private theorem readDualBoundBlock_spec (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) :
    BlockRuns readDualBoundBlock 6 s (dualBoundReadState s) := by
  apply BlockRuns.of_running_exit
  · simp [dualBoundReadState, arithmeticStep, readDualBoundBlock, Function.iterate_succ_apply', entry, running]
  · exact running
  · rfl



def considerDualBoundTakesCandidate (s : ArithmeticState) : Prop :=
  s.nm (s.nr 3 + s.nr 7) ≠ 0 ∧ 0 < s.rm (s.nr 5 + s.nr 7) ∧
    (s.nr 1 = 0 ∨ s.rm (s.nr 4 + s.nr 7) / s.rm (s.nr 5 + s.nr 7) < s.rr 1)

/-- Read and consider one cached event in at most seventeen instructions. -/
theorem considerDualBoundBlock_spec (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ steps ≤ 17, let result := (arithmeticStep considerDualBoundBlock)^[steps] s
      BlockRuns considerDualBoundBlock steps s result ∧ result.halted = false ∧
      (considerDualBoundTakesCandidate s → result.nr 1 = s.nm (s.nr 3 + s.nr 7) ∧
        result.rr 1 = s.rm (s.nr 4 + s.nr 7) / s.rm (s.nr 5 + s.nr 7)) ∧
      (¬considerDualBoundTakesCandidate s → result.nr 1 = s.nr 1 ∧ result.rr 1 = s.rr 1) ∧
      result.nm = s.nm ∧ result.rm = s.rm ∧ ∀ r, 3 ≤ r → r ≠ 6 → result.nr r = s.nr r := by
  let middle := {dualBoundReadState s with pc := 0}
  have takes : mergeDualBoundTakesCandidate middle ↔ considerDualBoundTakesCandidate s := by
    simp [middle, dualBoundReadState, mergeDualBoundTakesCandidate, considerDualBoundTakesCandidate]
  obtain ⟨steps, bounded, merged, chosen, kept, natMem, realMem⟩ := mergeDualBoundBlock_spec middle rfl running
  have joined := BlockRuns.append (readDualBoundBlock_spec s entry running) merged
  have staysLive := no_halt_from_running (s := middle) running merged.inside mergeDualBoundBlock_no_halt
  refine ⟨6 + steps, by omega, ?_⟩
  dsimp only
  rw [considerDualBoundBlock, joined.run]
  refine ⟨joined, staysLive, ?_, ?_, natMem, realMem, ?_⟩
  · intro h
    simpa [middle, dualBoundReadState, relocateState] using chosen (takes.mpr h)
  · intro h
    simpa [middle, dualBoundReadState, relocateState] using kept (fun yes => h (takes.mp yes))
  · intro r high away
    have nonzero : r ≠ 0 := by omega
    have fixed := arithmeticRun_keeps_high_register (mergeDualBoundBlock_low_writes r high) middle steps
    simpa [middle, dualBoundReadState, relocateState, away, nonzero] using fixed

end VehicleRoutingSurvey.Routing
end RppSource_WeightedReadDeltaRAM

/-! matching/MatchingStageControl.lean -/
section RppSource_MatchingStageControl
namespace VehicleRoutingSurvey.Routing









theorem publishCompactMateTableBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns publishCompactMateTableBlock 4 s t ∧ t.halted = false ∧
      t.nr 31 = s.nr 56 ∧ t.nr 32 = s.nr 55 ∧ t.nr 33 = s.nr 50 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      ∀ r ≥ 100, t.nr r = s.nr r := by
  let t := (arithmeticStep publishCompactMateTableBlock)^[4] s
  have ready : t.halted = false := by
    simp [t, publishCompactMateTableBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = publishCompactMateTableBlock.length := by
    simp [t, publishCompactMateTableBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [t, publishCompactMateTableBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [t, publishCompactMateTableBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [t, publishCompactMateTableBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [t, publishCompactMateTableBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [t, publishCompactMateTableBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · intro r high
    apply arithmeticRun_keeps_high_register _ s 4
    simp [publishCompactMateTableBlock, naturalDestination] <;> omega


end VehicleRoutingSurvey.Routing
end RppSource_MatchingStageControl

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

/-- Every perfect matching uses at least one edge across an odd cut. -/
theorem matching_cut_nonempty_of_odd {n : ℕ} {O S : Finset (Fin n)}
    {M : Finset (Sym2 (Fin n))} (perfect : IsPerfectMatchingOn O M) (sub : S ⊆ O)
    (odd : Odd S.card) : (M.filter (MatchingCrossesCut S)).Nonempty := by
  have filtered : O.filter (· ∈ S) = S := Finset.ext fun _ =>
    Finset.mem_filter.trans ⟨And.right, fun hv => ⟨sub hv, hv⟩⟩
  have incidence : (∑ e ∈ M, (e.toFinset.filter (· ∈ S)).card) = S.card := by
    simpa only [Finset.sum_boole, Nat.cast_id, filtered] using
      perfectMatching_sum_vertices perfect (fun v => if v ∈ S then (1 : ℕ) else 0)
  by_contra absent
  have even : (∑ e ∈ M, (e.toFinset.filter (· ∈ S)).card) ≡ 0 [MOD 2] := by
    apply Nat.ModEq.sum_zero
    intro e he
    have distinct := (perfect.1 e he).1
    have bound : (e.toFinset.filter (· ∈ S)).card ≤ 2 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (Sym2.card_toFinset_of_not_isDiag e distinct)
    have notOne : (e.toFinset.filter (· ∈ S)).card ≠ 1 := fun crosses =>
      absent ⟨e, Finset.mem_filter.mpr ⟨he, distinct, crosses⟩⟩
    change (e.toFinset.filter (· ∈ S)).card % 2 = 0
    omega
  rw [incidence] at even
  change S.card % 2 = 0 at even
  exact Nat.zero_ne_one (even.symm.trans (Nat.odd_iff.mp odd))



theorem oddCutDualEdgeValue_mk {n : ℕ} (cuts : Finset (Finset (Fin n)))
    (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ) {u v : Fin n} (distinct : u ≠ v) :
    oddCutDualEdgeValue cuts potential cutDual s(u, v) = potential u + potential v +
      ∑ S ∈ cuts.filter (fun S => (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S)), cutDual S := by
  have sameCuts : cuts.filter (MatchingCrossesCut · s(u, v)) =
      cuts.filter (fun S => (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S)) := Finset.ext fun S => by
    simp only [Finset.mem_filter, matchingCrossesCut_mk_iff S distinct]
  simp [oddCutDualEdgeValue, sameCuts, Sym2.toFinset_mk_eq, Finset.sum_insert, distinct]

private theorem sum_oddCutDualEdgeValue {n : ℕ} {O : Finset (Fin n)}
    {M : Finset (Sym2 (Fin n))} (perfect : IsPerfectMatchingOn O M)
    (cuts : Finset (Finset (Fin n))) (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ) :
    (∑ e ∈ M, oddCutDualEdgeValue cuts potential cutDual e) =
      (∑ v ∈ O, potential v) +
        ∑ S ∈ cuts, ((M.filter (MatchingCrossesCut S)).card : ℝ) * cutDual S := by
  simp only [oddCutDualEdgeValue, Finset.sum_add_distrib, perfectMatching_sum_vertices perfect]
  congr 1
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun S _ => by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- Feasible odd-cut dual variables certify a perfect matching when its edges are tight and
each cut with a positive dual variable is crossed exactly once. -/
theorem perfectMatching_min_of_oddCut_certificate {n : ℕ} {c : Fin n → Fin n → ℝ}
    {O : Finset (Fin n)} {M : Finset (Sym2 (Fin n))} (perfect : IsPerfectMatchingOn O M)
    (cuts : Finset (Finset (Fin n))) (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ)
    (valid : ∀ S ∈ cuts, S ⊆ O ∧ Odd S.card ∧ 0 ≤ cutDual S)
    (feasible : ∀ e, ¬e.IsDiag → (∀ v ∈ e, v ∈ O) →
      oddCutDualEdgeValue cuts potential cutDual e ≤ edgeCost c e)
    (tight : ∀ e ∈ M, oddCutDualEdgeValue cuts potential cutDual e = edgeCost c e)
    (once : ∀ S ∈ cuts, 0 < cutDual S → (M.filter (MatchingCrossesCut S)).card = 1) :
    IsMinMatchingOn c O M := by
  refine ⟨perfect, fun N other => ?_⟩
  have chosenCuts : (∑ S ∈ cuts, ((M.filter (MatchingCrossesCut S)).card : ℝ) * cutDual S) =
      ∑ S ∈ cuts, cutDual S := by
    apply Finset.sum_congr rfl
    intro S hS
    by_cases positive : 0 < cutDual S
    · simp [once S hS positive]
    · simp [le_antisymm (le_of_not_gt positive) (valid S hS).2.2]
  have otherCuts : (∑ S ∈ cuts, cutDual S) ≤
      ∑ S ∈ cuts, ((N.filter (MatchingCrossesCut S)).card : ℝ) * cutDual S := by
    apply Finset.sum_le_sum
    intro S hS
    obtain ⟨sub, odd, nonneg⟩ := valid S hS
    have count := Finset.card_pos.mpr (matching_cut_nonempty_of_odd other sub odd)
    have countReal : (1 : ℝ) ≤ (N.filter (MatchingCrossesCut S)).card := by
      exact_mod_cast count
    simpa only [one_mul] using mul_le_mul_of_nonneg_right countReal nonneg
  calc
    edgeSetWeight c M = ∑ e ∈ M, oddCutDualEdgeValue cuts potential cutDual e :=
      (Finset.sum_congr rfl tight).symm
    _ = (∑ v ∈ O, potential v) + ∑ S ∈ cuts, cutDual S := by
      rw [sum_oddCutDualEdgeValue perfect, chosenCuts]
    _ ≤ (∑ v ∈ O, potential v) +
        ∑ S ∈ cuts, ((N.filter (MatchingCrossesCut S)).card : ℝ) * cutDual S :=
      add_le_add le_rfl otherCuts
    _ = ∑ e ∈ N, oddCutDualEdgeValue cuts potential cutDual e :=
      (sum_oddCutDualEdgeValue other cuts potential cutDual).symm
    _ ≤ edgeSetWeight c N := Finset.sum_le_sum fun e he =>
      feasible e (other.1 e he).1 (other.1 e he).2

end VehicleRoutingSurvey.Routing
end RppSource_WeightedCertificate

/-! matching/WeightedBlossomCertificate.lean -/
section RppSource_WeightedBlossomCertificate
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- If a blossom is already matched internally away from its base, only its base can be
incident to a crossing matching edge. Oddness then forces exactly one crossing. -/
theorem matching_single_crossing_of_blossom {n : ℕ} {O S : Finset (Fin n)}
    {M : Finset (Sym2 (Fin n))} (perfect : IsPerfectMatchingOn O M) (sub : S ⊆ O)
    (odd : Odd S.card) {base : Fin n} (baseMem : base ∈ S)
    (internal : ∀ v ∈ S, v ≠ base → ∃ e ∈ M, v ∈ e ∧ ∀ w ∈ e, w ∈ S) :
    (M.filter (MatchingCrossesCut S)).card = 1 := by
  have atBase : ∀ e ∈ M.filter (MatchingCrossesCut S), base ∈ e := by
    intro e he
    obtain ⟨inM, crosses⟩ := Finset.mem_filter.mp he
    obtain ⟨v, inside⟩ := Finset.card_eq_one.mp crosses.2
    have inFilter : v ∈ e.toFinset.filter (· ∈ S) := inside.symm ▸ Finset.mem_singleton_self v
    obtain ⟨endpoint, inS⟩ := Finset.mem_filter.mp inFilter
    have atEdge := Sym2.mem_toFinset.mp endpoint
    by_cases isBase : v = base
    · exact isBase ▸ atEdge
    · obtain ⟨f, hf, atInternal, contained⟩ := internal v inS isBase
      have equal := (perfect.2 v (sub inS)).unique ⟨inM, atEdge⟩ ⟨hf, atInternal⟩
      have allInside : e.toFinset.filter (· ∈ S) = e.toFinset := Finset.filter_eq_self.mpr
        fun w hw => contained w (equal ▸ Sym2.mem_toFinset.mp hw)
      have one := crosses.2
      rw [allInside, Sym2.card_toFinset_of_not_isDiag e crosses.1] at one
      omega
  obtain ⟨crossing, chosen⟩ := matching_cut_nonempty_of_odd perfect sub odd
  have singleton : M.filter (MatchingCrossesCut S) = {crossing} := Finset.ext fun e =>
    ⟨fun he => Finset.mem_singleton.mpr ((perfect.2 base (sub baseMem)).unique
        ⟨(Finset.mem_filter.mp he).1, atBase e he⟩
        ⟨(Finset.mem_filter.mp chosen).1, atBase crossing chosen⟩),
      fun he => (Finset.mem_singleton.mp he).symm ▸ chosen⟩
  rw [singleton, Finset.card_singleton]

/-- Termination with a perfect matching, feasible dual variables, tight matched edges, and
internally matched positive blossoms certifies a minimum-weight matching. -/
theorem perfectMatching_min_of_blossom_certificate {n : ℕ} {c : Fin n → Fin n → ℝ}
    {O : Finset (Fin n)} {M : Finset (Sym2 (Fin n))} (perfect : IsPerfectMatchingOn O M)
    (cuts : Finset (Finset (Fin n))) (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ)
    (valid : ∀ S ∈ cuts, S ⊆ O ∧ Odd S.card ∧ 0 ≤ cutDual S)
    (feasible : ∀ e, ¬e.IsDiag → (∀ v ∈ e, v ∈ O) →
      oddCutDualEdgeValue cuts potential cutDual e ≤ edgeCost c e)
    (tight : ∀ e ∈ M, oddCutDualEdgeValue cuts potential cutDual e = edgeCost c e)
    (internallyMatched : ∀ S ∈ cuts, 0 < cutDual S → ∃ base ∈ S,
      ∀ v ∈ S, v ≠ base → ∃ e ∈ M, v ∈ e ∧ ∀ w ∈ e, w ∈ S) : IsMinMatchingOn c O M := by
  refine perfectMatching_min_of_oddCut_certificate perfect cuts potential cutDual valid feasible tight ?_
  intro S hS positive
  obtain ⟨base, baseMem, internal⟩ := internallyMatched S hS positive
  exact matching_single_crossing_of_blossom perfect (valid S hS).1 (valid S hS).2.1 baseMem internal

end VehicleRoutingSurvey.Routing
end RppSource_WeightedBlossomCertificate

/-! matching/MatchingCertifiedOutput.lean -/
section RppSource_MatchingCertifiedOutput
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Publish the final original-vertex mate table. Feasibility of the dual and the
internally matched positive blossoms certify the exact optimum. -/
theorem publishCertifiedCompactMateTableBlock_correct {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {original s : ArithmeticState} {mate : Fin k → Fin k}
    (entry : s.pc = 0) (running : s.halted = false)
    (dimension : s.nr 55 = k) (mapBase : s.nr 56 = original.nr 31)
    (mateAbove : original.nr 63 ≤ s.nr 50) (mateBytes : ∀ v : Fin k, s.nm (s.nr 50 + v.val) = (mate v).val)
    (validMate : MateTableOn Finset.univ mate)
    (saved : ∀ r ≥ 100, s.nr r = original.nr r)
    (natural : ∀ a < original.nr 63, s.nm a = original.nm a)
    (real : ∀ a < original.nr 64, s.rm a = original.rm a)
    (cuts : Finset (Finset (Fin k))) (potential : Fin k → ℝ) (cutDual : Finset (Fin k) → ℝ)
    (cutValid : ∀ B ∈ cuts, Odd B.card ∧ 0 ≤ cutDual B)
    (feasible : ∀ e, ¬e.IsDiag → oddCutDualEdgeValue cuts potential cutDual e ≤ edgeCost cost e)
    (tight : ∀ e ∈ mateEdgeSet Finset.univ mate, oddCutDualEdgeValue cuts potential cutDual e = edgeCost cost e)
    (internal : ∀ B ∈ cuts, 0 < cutDual B → ∃ base ∈ B,
      ∀ v ∈ B, v ≠ base → ∃ e ∈ mateEdgeSet Finset.univ mate, v ∈ e ∧ ∀ w ∈ e, w ∈ B) :
    ∃ t, BlockRuns publishCompactMateTableBlock 4 s t ∧ t.halted = false ∧
      t.nr 31 = original.nr 31 ∧ t.nr 32 = k ∧ original.nr 63 ≤ t.nr 33 ∧
      (∀ v : Fin k, t.nm (t.nr 33 + v.val) = (mate v).val) ∧
      IsMinMatchingOn cost Finset.univ (mateEdgeSet Finset.univ mate) ∧
      (∀ r ≥ 100, t.nr r = original.nr r) ∧
      (∀ a < original.nr 63, t.nm a = original.nm a) ∧ ∀ a < original.nr 64, t.rm a = original.rm a := by
  have optimal := perfectMatching_min_of_blossom_certificate (mateEdgeSet_perfect validMate)
    cuts potential cutDual (fun B hb => ⟨Finset.subset_univ B, cutValid B hb⟩)
    (fun e legal _ => feasible e legal) tight internal
  obtain ⟨t, run, live, oddMap, size, output, natMem, realMem, fixed⟩ :=
    publishCompactMateTableBlock_correct entry running
  exact ⟨t, run, live, oddMap.trans mapBase, size.trans dimension, output.symm ▸ mateAbove,
    fun v => by rw [natMem, output]; exact mateBytes v, optimal,
    fun r hr => (fixed r hr).trans (saved r hr),
    fun a ha => (congrFun natMem a).trans (natural a ha),
    fun a ha => (congrFun realMem a).trans (real a ha)⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingCertifiedOutput

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

/-! matching/WeightedDualCache.lean -/
section RppSource_WeightedDualCache
namespace VehicleRoutingSurvey.Routing

/-- Keep actual constraints as representatives. A positive-rate constraint can be omitted only
when the cache has a constraint of the same rate and no more slack. -/
structure DualSlackCache {Event : Type*} (full cache : List (DualSlack Event)) : Prop where
  sound : ∀ {c}, c ∈ cache → c ∈ full
  covers : ∀ c ∈ full, 0 < c.rate →
    ∃ r ∈ cache, r.rate = c.rate ∧ r.slack ≤ c.slack

















end VehicleRoutingSurvey.Routing
end RppSource_WeightedDualCache

/-! matching/WeightedDeltaScan.lean -/
section RppSource_WeightedDeltaScan
namespace VehicleRoutingSurvey.Routing









private theorem dualBoundMinimum_next {initial current result : ArithmeticState} {index : ℕ}
    (previous : DualBoundMinimum initial index current)
    (selected : dualBoundPresent initial index ∧ (current.nr 1 = 0 ∨ dualBoundRatio initial index < current.rr 1) →
      result.nr 1 = dualBoundIdentifier initial index ∧ result.rr 1 = dualBoundRatio initial index)
    (retained : ¬(dualBoundPresent initial index ∧ (current.nr 1 = 0 ∨ dualBoundRatio initial index < current.rr 1)) →
      result.nr 1 = current.nr 1 ∧ result.rr 1 = current.rr 1) : DualBoundMinimum initial (index + 1) result := by
  classical
  by_cases choose : dualBoundPresent initial index ∧ (current.nr 1 = 0 ∨ dualBoundRatio initial index < current.rr 1)
  · obtain ⟨id, delta⟩ := selected choose
    have live : result.nr 1 ≠ 0 := id.symm ▸ choose.1.1
    refine ⟨fun _ => ⟨index, Nat.lt_succ_self _, choose.1, id, delta⟩, fun j within present => ⟨live, ?_⟩⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp within with earlier | rfl
    · obtain ⟨nonempty, lower⟩ := previous.2 j earlier present
      rw [delta]
      exact (choose.2.resolve_left nonempty).le.trans lower
    · exact le_of_eq delta
  · obtain ⟨id, delta⟩ := retained choose
    refine ⟨?_, ?_⟩
    · intro live
      obtain ⟨j, earlier, present, originalID, originalDelta⟩ := previous.1 (id ▸ live)
      exact ⟨j, earlier.trans (Nat.lt_succ_self _), present, id.trans originalID, delta.trans originalDelta⟩
    · intro j within present
      rw [id, delta]
      rcases Nat.lt_succ_iff_lt_or_eq.mp within with earlier | rfl
      · exact previous.2 j earlier present
      · exact ⟨fun empty => choose ⟨present, Or.inl empty⟩,
          le_of_not_gt (fun better => choose ⟨present, Or.inr better⟩)⟩

private structure DualBoundScanState (initial : ArithmeticState) (index : ℕ) (current : ArithmeticState) : Prop where
  entry : current.pc = 0
  running : current.halted = false
  indexAt : current.nr 7 = index
  fixed : ∀ reg, 3 ≤ reg → reg ≠ 6 → reg ≠ 7 → current.nr reg = initial.nr reg
  natMemory : current.nm = initial.nm
  realMemory : current.rm = initial.rm
  minimum : DualBoundMinimum initial index current



/-- Scan the cached event table in at most twenty instructions per row and two for the
loop boundary. The accumulator holds an actual least nonempty positive-rate candidate. -/
theorem scanDualBoundBlock_spec (initial : ArithmeticState) (entry : initial.pc = 0)
    (running : initial.halted = false) (empty : initial.nr 1 = 0) (one : initial.nr 9 = 1) :
    ∃ result steps, steps ≤ 20 * initial.nr 8 + 2 ∧ BlockRuns scanDualBoundBlock steps initial result ∧
      result.halted = false ∧ DualBoundMinimum initial (initial.nr 8) result ∧
      result.nm = initial.nm ∧ result.rm = initial.rm ∧
      ∀ reg, 3 ≤ reg → reg ≠ 6 → reg ≠ 7 → result.nr reg = initial.nr reg := by
  let inv := DualBoundScanState initial
  have starts : inv 0 {initial with pc := 0, nr := Function.update initial.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, rfl, rfl, ?_⟩
    · intro reg _ _ away
      simp [Function.update_of_ne away]
    · simp [DualBoundMinimum, empty]
  have control (i : ℕ) (m : ArithmeticState) (hm : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 8 = initial.nr 8 :=
    ⟨hm.entry, hm.running, hm.indexAt, hm.fixed 8 (by decide) (by decide) (by decide)⟩
  have iterate (i : ℕ) (_ : i < initial.nr 8) (m : ArithmeticState) (hm : inv i m) :
      ∃ t steps, steps ≤ 17 ∧ BlockRuns considerDualBoundBlock steps m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    obtain ⟨steps, count, body, live, chosen, kept, natMem, realMem, fixed⟩ :=
      considerDualBoundBlock_spec m hm.entry hm.running
    let t := (arithmeticStep considerDualBoundBlock)^[steps] m
    have idBase := hm.fixed 3 (by decide) (by decide) (by decide)
    have slackBase := hm.fixed 4 (by decide) (by decide) (by decide)
    have rateBase := hm.fixed 5 (by decide) (by decide) (by decide)
    have decision : considerDualBoundTakesCandidate m ↔
        dualBoundPresent initial i ∧ (m.nr 1 = 0 ∨ dualBoundRatio initial i < m.rr 1) := by
      simp [considerDualBoundTakesCandidate, dualBoundPresent, dualBoundIdentifier, dualBoundRatio,
        hm.natMemory, hm.realMemory, hm.indexAt, idBase, slackBase, rateBase, and_assoc]
    have minimum : DualBoundMinimum initial (i + 1) t := by
      refine dualBoundMinimum_next hm.minimum ?_ ?_
      · intro take
        simpa [t, dualBoundIdentifier, dualBoundRatio, hm.natMemory, hm.realMemory,
          hm.indexAt, idBase, slackBase, rateBase] using chosen (decision.mpr take)
      · intro skip
        exact kept (fun take => skip (decision.mp take))
    refine ⟨t, steps, count, body, live, rfl, live, ?_, ?_, natMem.trans hm.natMemory,
      realMem.trans hm.realMemory, ?_⟩
    · have stillIndex : t.nr 7 = i := (fixed 7 (by decide) (by decide)).trans hm.indexAt
      have stillOne : t.nr 9 = 1 := (fixed 9 (by decide) (by decide)).trans
        ((hm.fixed 9 (by decide) (by decide) (by decide)).trans one)
      simp [stillIndex, stillOne]
    · intro reg high away unchanged
      simp only [Function.update_of_ne unchanged]
      exact (fixed reg high away).trans (hm.fixed reg high away unchanged)
    · simpa [DualBoundMinimum] using minimum
  obtain ⟨last, steps, valid, costs, run⟩ := countedLoopFromZero_bounded 9 7 8 (initial.nr 8) 17
    considerDualBoundBlock inv entry running starts control iterate
  refine ⟨_, steps, ?_, run, valid.running, valid.minimum, valid.natMemory, valid.realMemory, valid.fixed⟩
  omega

end VehicleRoutingSurvey.Routing
end RppSource_WeightedDeltaScan

/-! matching/WeightedSlackAdvanceRAM.lean -/
section RppSource_WeightedSlackAdvanceRAM
namespace VehicleRoutingSurvey.Routing



private noncomputable def advancedDualSlackCell (s : ArithmeticState) : ArithmeticState :=
  let destination := s.nr 4 + s.nr 7
  let source := s.nr 5 + s.nr 7
  let product := s.rr 1 * s.rm source
  let updated := s.rm destination - product
  {s with
    pc := 7
    nr := Function.update (Function.update s.nr 6 destination) 10 source
    rr := Function.update (Function.update (Function.update (Function.update s.rr 2 (s.rm source))
      2 product) 3 (s.rm destination)) 3 updated
    rm := Function.update s.rm destination updated}

private theorem advanceDualSlackCell_spec (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) :
    BlockRuns advanceDualSlackCell 7 s (advancedDualSlackCell s) := by
  apply BlockRuns.of_running_exit
  · simp [advancedDualSlackCell, arithmeticStep, advanceDualSlackCell, Function.iterate_succ_apply', entry, running]
  · exact running
  · rfl



private structure AdvanceDualSlackState (initial : ArithmeticState) (index : ℕ) (current : ArithmeticState) : Prop where
  entry : current.pc = 0
  running : current.halted = false
  indexAt : current.nr 7 = index
  fixed : ∀ reg, reg ≠ 6 → reg ≠ 7 → reg ≠ 10 → current.nr reg = initial.nr reg
  delta : current.rr 1 = initial.rr 1
  natMemory : current.nm = initial.nm
  values : ∀ a, current.rm a =
    if initial.nr 4 ≤ a ∧ a < initial.nr 4 + index then
      initial.rm a - initial.rr 1 * initial.rm (initial.nr 5 + (a - initial.nr 4))
    else initial.rm a

/-- Advance the slack table in place, using the separate rate table, in ten instructions per
row and two for the loop boundary. Register 1 contains the selected dual step. -/
theorem advanceDualSlackBlock_spec (initial : ArithmeticState) (entry : initial.pc = 0)
    (running : initial.halted = false) (one : initial.nr 9 = 1)
    (separate : ∀ i < initial.nr 8, ¬(initial.nr 4 ≤ initial.nr 5 + i ∧
      initial.nr 5 + i < initial.nr 4 + initial.nr 8)) :
    ∃ result, BlockRuns advanceDualSlackBlock (1 + (initial.nr 8 * 10 + 1)) initial result ∧
      result.halted = false ∧ result.nm = initial.nm ∧ result.nr 1 = initial.nr 1 ∧ result.rr 1 = initial.rr 1 ∧
      ∀ a, result.rm a = if initial.nr 4 ≤ a ∧ a < initial.nr 4 + initial.nr 8 then
        initial.rm a - initial.rr 1 * initial.rm (initial.nr 5 + (a - initial.nr 4))
        else initial.rm a := by
  let inv := AdvanceDualSlackState initial
  have starts : inv 0 {initial with pc := 0, nr := Function.update initial.nr 7 0} := by
    refine ⟨rfl, running, by simp, ?_, rfl, rfl, ?_⟩
    · intro r _ unchanged _
      simp [Function.update_of_ne unchanged]
    · intro a
      have outside : ¬(initial.nr 4 ≤ a ∧ a < initial.nr 4 + 0) := by omega
      rw [if_neg outside]
  have control (i : ℕ) (m : ArithmeticState) (hm : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 7 = i ∧ m.nr 8 = initial.nr 8 :=
    ⟨hm.entry, hm.running, hm.indexAt, hm.fixed 8 (by decide) (by decide) (by decide)⟩
  have iterate (i : ℕ) (within : i < initial.nr 8) (m : ArithmeticState) (hm : inv i m) :
      ∃ t, BlockRuns advanceDualSlackCell 7 m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 7 (t.nr 7 + t.nr 9)} := by
    let t := advancedDualSlackCell m
    have still (r : ℕ) (away6 : r ≠ 6) (away10 : r ≠ 10) : t.nr r = m.nr r := by
      simp [t, advancedDualSlackCell, away6, away10]
    have valBase := hm.fixed 4 (by decide) (by decide) (by decide)
    have rateBase := hm.fixed 5 (by decide) (by decide) (by decide)
    let address := initial.nr 4 + i
    let rateAddress := initial.nr 5 + i
    have fresh : m.rm address = initial.rm address := by
      rw [hm.values, if_neg]
      simp [address]
    have stableRate : m.rm rateAddress = initial.rm rateAddress := by
      rw [hm.values, if_neg]
      exact fun bad => separate i within ⟨bad.1, bad.2.trans_le (Nat.add_le_add_left within.le _)⟩
    refine ⟨t, advanceDualSlackCell_spec m hm.entry hm.running, hm.running,
      rfl, hm.running, ?_, ?_, ?_, hm.natMemory, ?_⟩
    · have indexStill : t.nr 7 = i := (still 7 (by decide) (by decide)).trans hm.indexAt
      have oneStill : t.nr 9 = 1 := (still 9 (by decide) (by decide)).trans
        ((hm.fixed 9 (by decide) (by decide) (by decide)).trans one)
      simp [indexStill, oneStill]
    · intro r away6 away7 away10
      simp only [Function.update_of_ne away7]
      exact (still r away6 away10).trans (hm.fixed r away6 away7 away10)
    · simpa [t, advancedDualSlackCell] using hm.delta
    · intro a
      change (Function.update m.rm (m.nr 4 + m.nr 7)
          (m.rm (m.nr 4 + m.nr 7) - m.rr 1 * m.rm (m.nr 5 + m.nr 7))) a = _
      rw [valBase, rateBase, hm.indexAt, hm.delta]
      change Function.update m.rm address (m.rm address - initial.rr 1 * m.rm rateAddress) a = _
      by_cases atAddress : a = address
      · subst a
        have nextRange : initial.nr 4 ≤ address ∧ address < initial.nr 4 + (i + 1) := by
          dsimp [address]
          omega
        rw [Function.update_self, if_pos nextRange, fresh, stableRate]
        simp [address, rateAddress]
      · rw [Function.update_of_ne atAddress, hm.values]
        have sameRange : (initial.nr 4 ≤ a ∧ a < initial.nr 4 + i) ↔
            initial.nr 4 ≤ a ∧ a < initial.nr 4 + (i + 1) := by
          dsimp [address] at atAddress
          omega
        simp only [sameRange]
  obtain ⟨last, valid, completed⟩ := countedLoopFromZero_correct 9 7 8 (initial.nr 8) 7
    advanceDualSlackCell inv entry running starts control iterate
  exact ⟨_, completed, valid.running, valid.natMemory, valid.fixed 1 (by decide) (by decide) (by decide),
    valid.delta, valid.values⟩

end VehicleRoutingSurvey.Routing
end RppSource_WeightedSlackAdvanceRAM

/-! matching/WeightedDeltaPhaseRAM.lean -/
section RppSource_WeightedDeltaPhaseRAM
namespace VehicleRoutingSurvey.Routing



private theorem advanceDualSlackIfSelected_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (separate : ∀ i < s.nr 8, ¬(s.nr 4 ≤ s.nr 5 + i ∧ s.nr 5 + i < s.nr 4 + s.nr 8)) :
    ∃ result steps, steps ≤ 10 * s.nr 8 + 5 ∧ BlockRuns advanceDualSlackIfSelected steps s result ∧
      result.halted = false ∧ result.nr 1 = s.nr 1 ∧ result.rr 1 = s.rr 1 ∧ result.nm = s.nm ∧
      ∀ a, result.rm a = if s.nr 1 ≠ 0 ∧ s.nr 4 ≤ a ∧ a < s.nr 4 + s.nr 8 then
        s.rm a - s.rr 1 * s.rm (s.nr 5 + (a - s.nr 4)) else s.rm a := by
  let ready := {s with pc := 0, nr := Function.update s.nr 11 0}
  have starts := zeroRegister_runs 11 s entry running
  by_cases empty : s.nr 1 = 0
  · have same : ready.nr 1 = ready.nr 11 := by simp [ready, empty]
    have skipped := branchOnUnequal_skip 1 11 advanceDualSlackBlock ready rfl running same
    have run := starts.append skipped
    refine ⟨_, 3, by omega, run, running, ?_, rfl, rfl, ?_⟩
    · simp [ready, relocateState]
    · intro a
      simp [ready, relocateState, empty]
  · have different : ready.nr 1 ≠ ready.nr 11 := by simp [ready, empty]
    obtain ⟨result, body, live, natMemory, keptID, keptDelta, realMemory⟩ :=
      advanceDualSlackBlock_spec ready rfl running (by simpa [ready] using one) (by simpa [ready] using separate)
    have taken := branchOnUnequal_take 1 11 advanceDualSlackBlock (s := ready) rfl running different body
    have run := starts.append taken
    refine ⟨_, _, ?_, run, live, ?_, keptDelta, natMemory, ?_⟩
    · show 1 + (2 + (1 + (ready.nr 8 * 10 + 1))) ≤ 10 * s.nr 8 + 5
      have count : ready.nr 8 = s.nr 8 := by simp [ready]
      omega
    · simpa [ready, relocateState] using keptID
    · intro a
      simpa [ready, relocateState, empty] using realMemory a





/-- Select the least admissible delta and advance the cached slack table, or leave the table
untouched when no event exists. Both passes together cost at most thirty instructions per row
plus seven fixed instructions. -/
theorem selectAndAdvanceDualSlackBlock_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (empty : s.nr 1 = 0) (one : s.nr 9 = 1)
    (separate : ∀ i < s.nr 8, ¬(s.nr 4 ≤ s.nr 5 + i ∧ s.nr 5 + i < s.nr 4 + s.nr 8)) :
    ∃ result steps, steps ≤ 30 * s.nr 8 + 7 ∧ BlockRuns selectAndAdvanceDualSlackBlock steps s result ∧
      result.halted = false ∧ DualBoundMinimum s (s.nr 8) result ∧ result.nm = s.nm ∧
      ∀ a, result.rm a = if result.nr 1 ≠ 0 ∧ s.nr 4 ≤ a ∧ a < s.nr 4 + s.nr 8 then
        s.rm a - result.rr 1 * s.rm (s.nr 5 + (a - s.nr 4)) else s.rm a := by
  obtain ⟨scanned, scanSteps, scanBound, scanRun, scanLive, minimum, natMemory, realMemory, fixed⟩ :=
    scanDualBoundBlock_spec s entry running empty one
  let ready := {scanned with pc := 0}
  have valueBase : ready.nr 4 = s.nr 4 := fixed 4 (by decide) (by decide) (by decide)
  have rateBase : ready.nr 5 = s.nr 5 := fixed 5 (by decide) (by decide) (by decide)
  have rows : ready.nr 8 = s.nr 8 := fixed 8 (by decide) (by decide) (by decide)
  have oneAfter : ready.nr 9 = 1 := (fixed 9 (by decide) (by decide) (by decide)).trans one
  have readySeparate : ∀ i < ready.nr 8,
      ¬(ready.nr 4 ≤ ready.nr 5 + i ∧ ready.nr 5 + i < ready.nr 4 + ready.nr 8) := by
    simpa only [valueBase, rateBase, rows] using separate
  obtain ⟨result, advanceSteps, advanceBound, advanceRun, live, keptID, keptDelta, keptMemory, shifted⟩ :=
    advanceDualSlackIfSelected_spec ready rfl scanLive oneAfter readySeparate
  have combined := scanRun.append advanceRun
  refine ⟨_, scanSteps + advanceSteps, by omega, combined, live, ?_, keptMemory.trans natMemory, ?_⟩
  · simpa [DualBoundMinimum, relocateState, keptID, keptDelta, ready] using minimum
  · intro a
    simpa only [relocateState, valueBase, rateBase, rows, show ready.rm = s.rm from realMemory,
      keptID, keptDelta] using shifted a

end VehicleRoutingSurvey.Routing
end RppSource_WeightedDeltaPhaseRAM

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









end VehicleRoutingSurvey.Routing
end RppSource_WeightedDeltaTable

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

/-! matching/WeightedStageDriver.lean -/
section RppSource_WeightedStageDriver
namespace VehicleRoutingSurvey.Routing



private theorem matchingStageSnapshot_update (s : ArithmeticState) (pc counter : ℕ) :
    matchingStageSnapshot {s with pc := pc, nr := Function.update s.nr 30 counter} = matchingStageSnapshot s := by
  simp [matchingStageSnapshot]

theorem matchingStageSnapshot_pc (s : ArithmeticState) (pc : ℕ) :
    matchingStageSnapshot {s with pc := pc} = matchingStageSnapshot s := rfl







private def matchingStagePotential (counts : ArithmeticState → MatchingStageCounts)
    (perCharge finishBudget : ℕ) (s : ArithmeticState) : ℕ :=
  if s.nr 33 = 0 then 0 else finishBudget + perCharge * (counts (matchingStageSnapshot s)).credit

private structure MatchingStageLoopState (n : ℕ) (frame : ArithmeticState → Prop)
    (counts : ArithmeticState → MatchingStageCounts) (index : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  indexAt : s.nr 30 = index
  limit : s.nr 31 = 6 * n + 1
  zero : s.nr 32 = 0
  one : s.nr 34 = 1
  payload : frame (matchingStageSnapshot s)
  progress : s.nr 33 ≠ 0 → index + (counts (matchingStageSnapshot s)).credit ≤ 6 * n

/-- A bounded stage runs the selector and event handler while active. The actual total
cost amortizes row work against the verified charge for growth, contraction, or expansion. -/
theorem matchingStageProgram_spec {n rowCap perCharge finishBudget : ℕ}
    {handler : List ArithmeticInstruction} {frame : ArithmeticState → Prop}
    {counts : ArithmeticState → MatchingStageCounts}
    (checked : MatchingStageHandler handler frame counts rowCap perCharge finishBudget)
    (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false)
    (limit : s.nr 31 = 6 * n + 1) (zero : s.nr 32 = 0) (one : s.nr 34 = 1)
    (established : frame (matchingStageSnapshot s))
    (initialCredit : (counts (matchingStageSnapshot s)).credit ≤ 6 * n) :
    ∃ result steps, steps ≤ (6 * n + 1) * (30 * rowCap + 12) + finishBudget + perCharge * (6 * n) + 2 ∧
      BlockRuns (matchingStageProgram handler) steps s result ∧ result.halted = false ∧
      result.nr 33 = 0 ∧ frame (matchingStageSnapshot result) := by
  let inv := MatchingStageLoopState n frame counts
  let pot := matchingStagePotential counts perCharge finishBudget
  let seed := {s with pc := 0, nr := Function.update s.nr 30 0}
  have starts : inv 0 seed := by
    refine ⟨rfl, running, by simp [seed], ?_, ?_, ?_, ?_, ?_⟩
    · simpa [seed] using limit
    · simpa [seed] using zero
    · simpa [seed] using one
    · simpa only [seed, matchingStageSnapshot_update] using established
    · intro _
      simpa only [seed, matchingStageSnapshot_update, Nat.zero_add] using initialCredit
  have control (i : ℕ) (m : ArithmeticState) (valid : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 30 = i ∧ m.nr 31 = 6 * n + 1 :=
    ⟨valid.entry, valid.running, valid.indexAt, valid.limit⟩
  have iterate (i : ℕ) (_ : i < 6 * n + 1) (m : ArithmeticState) (valid : inv i m) :
      ∃ t steps,
        let next := {t with pc := 0, nr := Function.update t.nr 30 (t.nr 30 + t.nr 34)}
        BlockRuns (matchingStageBody handler) steps m t ∧ t.halted = false ∧ inv (i + 1) next ∧
          steps + pot next ≤ (30 * rowCap + 9) + pot m := by
    by_cases done : m.nr 33 = 0
    · let t := {m with pc := (matchingStageBody handler).length}
      let next := {t with pc := 0, nr := Function.update t.nr 30 (t.nr 30 + t.nr 34)}
      have run : BlockRuns (matchingStageBody handler) 2 m t :=
        branchOnUnequal_skip 33 32 (appendBlock selectAndAdvanceDualSlackBlock handler)
          m valid.entry valid.running (done.trans valid.zero.symm)
      have spare : matchingStageSnapshot next = matchingStageSnapshot m := by
        simp only [next, matchingStageSnapshot_update, t]
      have stillDone : next.nr 33 = 0 := by simpa [next, t] using done
      have nextInv : inv (i + 1) next := by
        refine ⟨rfl, valid.running, ?_, ?_, ?_, ?_, spare.symm ▸ valid.payload, fun live => (live stillDone).elim⟩
        · simp [next, t, valid.indexAt, valid.one]
        · simpa [next, t] using valid.limit
        · simpa [next, t] using valid.zero
        · simpa [next, t] using valid.one
      refine ⟨t, 2, run, valid.running, nextInv, ?_⟩
      change 2 + pot next ≤ (30 * rowCap + 9) + pot m
      have beforePotential : pot m = 0 := if_pos done
      have afterPotential : pot next = 0 := if_pos stillDone
      rw [beforePotential, afterPotential]
      omega
    · obtain ⟨empty, selectorOne, rows, separate⟩ := checked.ready m valid.payload done
      obtain ⟨selected, selectTicks, selectBound, selectRun, selectedLive, minimum, natural, real⟩ :=
        selectAndAdvanceDualSlackBlock_spec m valid.entry valid.running empty selectorOne separate
      obtain ⟨after, ticks, eventRun, live, nextFrame, indexSame, limitSame, zeroSame, oneSame, decision⟩ :=
        checked.dispatch m selected selectTicks valid.payload done selectRun selectedLive minimum natural real
      have steps := selectRun.append eventRun
      have different : m.nr 33 ≠ m.nr 32 := by simpa only [valid.zero] using done
      have run := branchOnUnequal_take 33 32 _ valid.entry valid.running different steps
      let t := relocateState 3 (relocateState selectAndAdvanceDualSlackBlock.length after)
      let next := {t with pc := 0, nr := Function.update t.nr 30 (t.nr 30 + t.nr 34)}
      have fixed : next.nr 33 = after.nr 33 := by simp [next, t, relocateState]
      have snap : matchingStageSnapshot next = matchingStageSnapshot after := by
        simp only [next, matchingStageSnapshot_update, t, relocateState]
      have selectAtMost : selectTicks ≤ 30 * rowCap + 7 :=
        selectBound.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 30 rows) 7)
      have nextInv : inv (i + 1) next := by
        refine ⟨rfl, live, ?_, ?_, ?_, ?_, snap.symm ▸ nextFrame, ?_⟩
        · simp [next, t, relocateState, indexSame, oneSame, valid.indexAt, valid.one]
        · simpa [next, t, relocateState, limitSame] using valid.limit
        · simpa [next, t, relocateState, zeroSame] using valid.zero
        · simpa [next, t, relocateState, oneSame] using valid.one
        · intro stillActive
          rw [snap]
          rcases decision with ⟨finished, _⟩ | ⟨_, charge, transition, _⟩
          · exact (stillActive (fixed.trans finished)).elim
          · have consumed := transition.charge_le
            have positive := transition.charge_pos
            have before := valid.progress done
            omega
      refine ⟨t, 2 + (selectTicks + ticks), run, live, nextInv, ?_⟩
      change 2 + (selectTicks + ticks) + pot next ≤ (30 * rowCap + 9) + pot m
      have beforePotential : pot m = finishBudget + perCharge * (counts (matchingStageSnapshot m)).credit :=
        if_neg done
      rcases decision with ⟨finished, bound⟩ | ⟨stillActive, charge, transition, charged⟩
      · have afterPotential : pot next = 0 := if_pos (fixed.trans finished)
        rw [beforePotential, afterPotential]
        omega
      · have weighted := Nat.mul_le_mul_left perCharge transition.charge_le
        rw [Nat.mul_add] at weighted
        have afterPotential : pot next = finishBudget + perCharge * (counts (matchingStageSnapshot after)).credit := by
          calc
            _ = finishBudget + perCharge * (counts (matchingStageSnapshot next)).credit :=
              if_neg (fun inactive => stillActive (fixed.symm.trans inactive))
            _ = _ := by rw [snap]
        rw [beforePotential, afterPotential]
        omega
  obtain ⟨last, actual, final, cost, complete⟩ := countedLoopFromZero_amortized 34 30 31 (6 * n + 1)
    (30 * rowCap + 9) (matchingStageBody handler) inv pot entry running starts control iterate
  have leavesInactive : last.nr 33 = 0 := by
    by_contra unfinished
    have remaining := final.progress unfinished
    omega
  have potBound : pot seed ≤ finishBudget + perCharge * (6 * n) := by
    by_cases inactive : seed.nr 33 = 0
    · simp [pot, matchingStagePotential, inactive]
    · simp only [pot, matchingStagePotential, if_neg inactive, seed, matchingStageSnapshot_update]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left perCharge initialCredit) _
  refine ⟨_, actual, ?_, complete, final.running, leavesInactive, ?_⟩
  · change actual ≤ (6 * n + 1) * (30 * rowCap + 12) + finishBudget + perCharge * (6 * n) + 2
    change actual ≤ 1 + ((6 * n + 1) * (30 * rowCap + 9 + 3) + pot seed + 1) at cost
    have constants : 30 * rowCap + 9 + 3 = 30 * rowCap + 12 := by omega
    rw [constants] at cost
    omega
  · simpa only [relocateState, matchingStageSnapshot_pc] using final.payload

end VehicleRoutingSurvey.Routing
end RppSource_WeightedStageDriver

/-! matching/WeightedMatchingLoop.lean -/
section RppSource_WeightedMatchingLoop
namespace VehicleRoutingSurvey.Routing



private theorem matchingLoopSnapshot_update (s : ArithmeticState) (pc counter : ℕ) :
    matchingLoopSnapshot {s with pc := pc, nr := Function.update s.nr 40 counter} = matchingLoopSnapshot s := by
  simp [matchingLoopSnapshot]

private theorem matchingLoopSnapshot_pc (s : ArithmeticState) (pc : ℕ) :
    matchingLoopSnapshot {s with pc := pc} = matchingLoopSnapshot s := rfl





private structure MatchingOuterState (augmentations : ℕ) (view : ℕ → ArithmeticState → Prop)
    (index : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  indexAt : s.nr 40 = index
  one : s.nr 41 = 1
  count : s.nr 42 = augmentations
  payload : view index (matchingLoopSnapshot s)

/-- Execute the prepared augmenting stage once per required matching edge. With linear-size
cache tables and linear per-charge actions, this wrapper accounts for cubic matching time. -/
theorem weightedMatchingLoop_spec {n augmentations preparation rowCap perCharge finishBudget : ℕ}
    {prepare handler : List ArithmeticInstruction} {view frame : ℕ → ArithmeticState → Prop}
    {counts : ℕ → ArithmeticState → MatchingStageCounts}
    (checked : MatchingLoopInterface n augmentations preparation rowCap perCharge finishBudget
      prepare handler view frame counts)
    (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 41 = 1) (count : s.nr 42 = augmentations) (zero : view 0 (matchingLoopSnapshot s)) :
    let stageBudget := (6 * n + 1) * (30 * rowCap + 12) + finishBudget + perCharge * (6 * n) + 2
    ∃ result steps, steps ≤ augmentations * (preparation + stageBudget + 3) + 2 ∧
      BlockRuns (weightedMatchingLoop prepare handler) steps s result ∧ result.halted = false ∧
      view augmentations (matchingLoopSnapshot result) := by
  let stageBudget := (6 * n + 1) * (30 * rowCap + 12) + finishBudget + perCharge * (6 * n) + 2
  let inv := MatchingOuterState augmentations view
  have starts : inv 0 {s with pc := 0, nr := Function.update s.nr 40 0} := by
    refine ⟨rfl, running, by simp, ?_, ?_, ?_⟩
    · simpa using one
    · simpa using count
    · simpa only [matchingLoopSnapshot_update] using zero
  have control (i : ℕ) (m : ArithmeticState) (hm : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 40 = i ∧ m.nr 42 = augmentations :=
    ⟨hm.entry, hm.running, hm.indexAt, hm.count⟩
  have iterate (i : ℕ) (within : i < augmentations) (m : ArithmeticState) (hm : inv i m) :
      ∃ t steps, steps ≤ preparation + stageBudget ∧ BlockRuns (appendBlock prepare (matchingStageProgram handler)) steps m t ∧
        t.halted = false ∧ inv (i + 1) {t with pc := 0, nr := Function.update t.nr 40 (t.nr 40 + t.nr 41)} := by
    obtain ⟨stageInput, preparationSteps, prepBound, prepRun, openStage, limit, empty, increment, initialFrame, credit⟩ :=
      checked.initializeStage i within m hm.entry hm.running hm.indexAt hm.one hm.count hm.payload
    let ready := {stageInput with pc := 0}
    obtain ⟨result, stageSteps, stageBound, stageRun, live, finished, finalFrame⟩ :=
      matchingStageProgram_spec (checked.handlerChecked i within) ready rfl openStage limit empty increment
        (by simpa only [ready, matchingStageSnapshot_pc] using initialFrame)
        (by simpa only [ready, matchingStageSnapshot_pc] using credit)
    have combined := prepRun.append stageRun
    let t := relocateState prepare.length result
    have tFrame : frame i (matchingStageSnapshot t) := by
      simpa only [t, relocateState, matchingStageSnapshot_pc] using finalFrame
    obtain ⟨updated, indexSame, oneSame, countSame⟩ :=
      checked.augmented i within m t _ hm.payload combined tFrame finished
    let next := {t with pc := 0, nr := Function.update t.nr 40 (t.nr 40 + t.nr 41)}
    have snap : matchingLoopSnapshot next = matchingLoopSnapshot t := by
      simp only [next, matchingLoopSnapshot_update]
    refine ⟨t, preparationSteps + stageSteps, Nat.add_le_add prepBound stageBound,
      combined, live, rfl, live, ?_, ?_, ?_, snap.symm ▸ updated⟩
    · simp [next, indexSame, oneSame, hm.indexAt, hm.one]
    · simpa [next, oneSame] using hm.one
    · simpa [next, countSame] using hm.count
  obtain ⟨last, steps, matched, costs, run⟩ := countedLoopFromZero_bounded 41 40 42 augmentations
    (preparation + stageBudget) (appendBlock prepare (matchingStageProgram handler)) inv entry running starts control iterate
  refine ⟨_, steps, ?_, run, matched.running, ?_⟩
  · change steps ≤ augmentations * (preparation + stageBudget + 3) + 2
    omega
  · simpa only [relocateState, matchingLoopSnapshot_pc] using matched.payload

end VehicleRoutingSurvey.Routing
end RppSource_WeightedMatchingLoop

/-! matching/MatchingCubicBound.lean -/
section RppSource_MatchingCubicBound
namespace VehicleRoutingSurvey.Routing

/-- Bound the checked stage driver's exact expression after at most `k` augmentations.
The initial preparation, per-search preparation, and augmenting exit have quadratic
budgets, and each structural charge has a linear budget. -/
theorem weightedMatchingCost_le_cube {k stages initial preparation rowCap perCharge finishBudget I P H F : ℕ}
    (stageCount : stages ≤ k) (initialBound : initial ≤ I * (k ^ 2 + 1))
    (prepBound : preparation ≤ P * (k ^ 2 + 1)) (tableBound : rowCap ≤ 3 * k)
    (chargeBound : perCharge ≤ H * (k + 1)) (finishBound : finishBudget ≤ F * (k ^ 2 + 1)) :
    let stageBudget := (6 * k + 1) * (30 * rowCap + 12) + finishBudget + perCharge * (6 * k) + 2
    initial + (stages * (preparation + stageBudget + 3) + 2) + 4 ≤
      (I + 6 + 2 * (P + F + 12 * H + 719)) * (k ^ 3 + 1) := by
  intro stageBudget
  have linearSquare : k ≤ k ^ 2 := by
    by_cases empty : k = 0
    · simp [empty]
    · have positive : 1 ≤ k := by omega
      simpa only [pow_two, Nat.mul_one] using Nat.mul_le_mul_left k positive
  have squareCube : k ^ 2 ≤ k ^ 3 := by
    by_cases empty : k = 0
    · simp [empty]
    · have positive : 1 ≤ k := by omega
      calc
        k ^ 2 = k ^ 2 * 1 := (Nat.mul_one _).symm
        _ ≤ k ^ 2 * k := Nat.mul_le_mul_left _ positive
        _ = k ^ 3 := (pow_succ k 2).symm
  have selector : (6 * k + 1) * (30 * rowCap + 12) ≤ 702 * k ^ 2 + 12 := by
    calc
      _ ≤ (6 * k + 1) * (30 * (3 * k) + 12) := Nat.mul_le_mul_left _
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ tableBound) _)
      _ = 540 * k ^ 2 + 162 * k + 12 := by ring
      _ ≤ _ := by omega
  have charged : perCharge * (6 * k) ≤ (12 * H) * (k ^ 2 + 1) := by
    calc
      _ ≤ (H * (k + 1)) * (6 * k) := Nat.mul_le_mul_right _ chargeBound
      _ = H * (6 * (k ^ 2 + k)) := by ring
      _ ≤ H * (12 * (k ^ 2 + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  have perStage : preparation + stageBudget + 3 ≤ (P + F + 12 * H + 719) * (k ^ 2 + 1) := by
    dsimp only [stageBudget]
    calc
      _ ≤ P * (k ^ 2 + 1) + (702 * k ^ 2 + 12) + F * (k ^ 2 + 1) +
          (12 * H) * (k ^ 2 + 1) + 5 := by
        have estimated := Nat.add_le_add (Nat.add_le_add selector finishBound) charged
        have combined := Nat.add_le_add prepBound estimated
        omega
      _ = (P + F + 12 * H) * (k ^ 2 + 1) + (702 * k ^ 2 + 17) := by ring
      _ ≤ (P + F + 12 * H) * (k ^ 2 + 1) + 719 * (k ^ 2 + 1) := by
        apply Nat.add_le_add_left
        rw [Nat.mul_add, Nat.mul_one]
        omega
      _ = _ := by ring
  have scaled : k * (k ^ 2 + 1) ≤ 2 * (k ^ 3 + 1) := by
    calc
      _ = k ^ 3 + k := by ring
      _ ≤ _ := by omega
  have overall : stages * (preparation + stageBudget + 3) ≤
      (2 * (P + F + 12 * H + 719)) * (k ^ 3 + 1) := by
    calc
      _ ≤ k * ((P + F + 12 * H + 719) * (k ^ 2 + 1)) := Nat.mul_le_mul stageCount perStage
      _ = (P + F + 12 * H + 719) * (k * (k ^ 2 + 1)) := by ring
      _ ≤ (P + F + 12 * H + 719) * (2 * (k ^ 3 + 1)) := Nat.mul_le_mul_left _ scaled
      _ = _ := by ring
  have setup : initial ≤ I * (k ^ 3 + 1) :=
    initialBound.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right squareCube _))
  calc
    _ ≤ I * (k ^ 3 + 1) + (2 * (P + F + 12 * H + 719)) * (k ^ 3 + 1) + 6 := by omega
    _ ≤ I * (k ^ 3 + 1) + (2 * (P + F + 12 * H + 719)) * (k ^ 3 + 1) + 6 * (k ^ 3 + 1) := by
      apply Nat.add_le_add_left
      rw [Nat.mul_add, Nat.mul_one]
      omega
    _ = _ := by ring


end VehicleRoutingSurvey.Routing
end RppSource_MatchingCubicBound

/-! matching/MatchingProgram.lean -/
section RppSource_MatchingProgram
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory











set_option maxRecDepth 16384 in
/-- An invariant proof for the actual event handler gives the complete compact-matching
contract, including the instruction bound and an original-vertex optimality certificate. -/
theorem weightedBlossomMatchingBlock_spec_at_entry
    (refined : ∀ {k : ℕ} {cost : Fin k → Fin k → ℝ} {s : ArithmeticState},
      CompactMateInput cost s → s.pc = 0 → s.halted = false → Nonempty (WeightedMatchingRefinement k cost s)) :
    CompactMateBlockSpec weightedBlossomMatchingBlock 27648 := by
  constructor
  intro k cost s input entry running
  obtain ⟨proof⟩ := refined input entry running
  obtain ⟨a, initTicks, compact, auxiliary, initBound, setup, aLive, compactFrame, auxFrame,
    mapStart, mapStack, regionEnd, natural, real, reals, stable⟩ :=
    initializeWeightedMatchingBlock_correct input entry running
  let ready := {a with pc := 0}
  have one : ready.nr 41 = 1 := (stable 41 (by decide)).trans
    ((auxFrame.registers 41 (by decide)).trans compactFrame.outer.1)
  have stages : ready.nr 42 = k / 2 := (stable 42 (by decide)).trans
    ((auxFrame.registers 42 (by decide)).trans compactFrame.outer.2)
  have initView : proof.interstage 0 (matchingLoopSnapshot ready) := by
    simpa only [matchingLoopSnapshot, ready] using proof.initial a initTicks setup
  obtain ⟨b, loopTicks, loopBound, loopRun, bLive, finalView⟩ :=
    weightedMatchingLoop_spec proof.loop ready rfl aLive one stages initView
  let final := {b with pc := 0}
  have certified : Nonempty (MatchingTerminalCertificate k cost s final) := proof.certificate final (by
    simpa only [matchingLoopSnapshot, final] using finalView)
  obtain ⟨data⟩ := certified
  obtain ⟨c, publish, live, mapBase, dimension, mateAbove, mates, optimum, keep, keepNat, keepReal⟩ :=
    publishCertifiedCompactMateTableBlock_correct (s := final) (original := s) (mate := data.mate)
      (cost := cost) rfl bLive data.dimension data.mapBase data.mateAbove data.mateBytes data.validMate
      data.saved data.natural data.real data.cuts data.potential data.cutDual
      data.cutValid data.feasible data.tight data.internal
  have square : k ≤ k ^ 2 := by
    by_cases empty : k = 0
    · simp [empty]
    · simpa only [pow_two, Nat.mul_one] using Nat.mul_le_mul_left k (show 1 ≤ k by omega)
  have initEnvelope : initTicks ≤ 204 * (k ^ 2 + 1) := by
    simp only [pow_two, Nat.mul_assoc, Nat.mul_add, Nat.mul_one] at initBound square ⊢
    omega
  have prepEnvelope : 104 * k * k + 48 * k + 33 ≤ 200 * (k ^ 2 + 1) := by
    simp only [pow_two, Nat.mul_assoc, Nat.mul_add, Nat.mul_one] at square ⊢
    omega
  have envelope := weightedMatchingCost_le_cube (k := k) (stages := k / 2) (initial := initTicks)
    (preparation := 104 * k * k + 48 * k + 33) (rowCap := 3 * k) (perCharge := 1024 * (k + 1))
    (finishBudget := 512 * (k ^ 2 + 1)) (I := 204) (P := 200) (H := 1024) (F := 512)
    (Nat.div_le_self _ _) initEnvelope prepEnvelope le_rfl le_rfl le_rfl
  have allTicks : initTicks + (loopTicks + 4) ≤ 27648 * (k ^ 3 + 1) := by
    have normalized : 204 + 6 + 2 * (200 + 512 + 12 * 1024 + 719) = 27648 := by decide
    simp only [normalized] at envelope
    omega
  let loopCode := weightedMatchingLoop prepareWeightedMatchingStageBlock weightedBlossomEventHandler
  let published := relocateState loopCode.length c
  let result := relocateState initializeWeightedMatchingBlock.length published
  have staged : BlockRuns
      (appendBlock (weightedMatchingLoop prepareWeightedMatchingStageBlock weightedBlossomEventHandler)
        publishCompactMateTableBlock) (loopTicks + 4) ready published := loopRun.append publish
  have ran : BlockRuns weightedBlossomMatchingBlock (initTicks + (loopTicks + 4)) s result :=
    setup.append staged
  exact ⟨result, data.mate, _, ran, live, allTicks, mapBase, dimension, mateAbove, mates, optimum, keep, keepNat, keepReal⟩




end VehicleRoutingSurvey.Routing
end RppSource_MatchingProgram

open VehicleRoutingSurvey.Routing SupplyChainTheory in
theorem solution : (fun {P : Prop} (_ : P) => P) (@VehicleRoutingSurvey.Routing.weightedBlossomMatchingBlock_spec_at_entry) :=
  @VehicleRoutingSurvey.Routing.weightedBlossomMatchingBlock_spec_at_entry
