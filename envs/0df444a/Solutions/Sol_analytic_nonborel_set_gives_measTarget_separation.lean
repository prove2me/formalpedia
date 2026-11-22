-- Prove2me | solution 1 for analytic_nonborel_set_gives_measTarget_separation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:46:04.841041+00:00
-- url     : https://prove2.me/submissions/f367897c-4359-4d4a-a4ef-65bbceeabf9d

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_BorelAnalyticSeparation
public import Theorems.Thm_singleton_badEvent_not_measurable
public import Theorems.Thm_MeasurableConceptClass_hWB
public import Theorems.Thm_borel_param_wellBehavedVCMeasTarget


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
theorem _root_.solution
    (A : Set ℝ)
    (hA_an : MeasureTheory.AnalyticSet A)
    (hA_non : ¬ MeasurableSet A) :
    KrappWirthSeparationMeasTarget := by
  -- Step 1: Get Polish β and g : β → ℝ with range g = A
  rcases MeasureTheory.analyticSet_iff_exists_polishSpace_range.mp hA_an with
    ⟨β, hτ, hP, g, hg_cont, hg_range⟩
  -- Equip β with Borel σ-algebra to get MeasurableSpace and StandardBorelSpace
  let : MeasurableSpace β := @borel β hτ
  have : @BorelSpace β hτ (@borel β hτ) := ⟨rfl⟩
  have : @StandardBorelSpace β (@borel β hτ) := ⟨⟨hτ, ⟨rfl⟩, hP⟩⟩
  have hg_meas : Measurable g := hg_cont.measurable
  -- Step 2: A is nonempty
  have hA_ne : A.Nonempty := by
    by_contra h; exact hA_non (Set.not_nonempty_iff_eq_empty.mp h ▸ MeasurableSet.empty)
  obtain ⟨a0, ha0⟩ := hA_ne
  obtain ⟨θ0, hθ0⟩ : ∃ θ0, g θ0 = a0 := by
    have : a0 ∈ Set.range g := hg_range ▸ ha0; exact this
  -- Step 3: Define e : Bool × β → Concept ℝ Bool
  let e : Bool × β → Concept ℝ Bool := fun t x =>
    if t.1 then singletonConcept (g t.2) x else zeroConcept x
  -- Step 4: Joint measurability of e
  have he : Measurable (fun p : (Bool × β) × ℝ => e p.1 p.2) := by
    simp only [e, singletonConcept, zeroConcept]
    have hbool : MeasurableSet {p : (Bool × β) × ℝ | p.1.1 = true} :=
      (measurable_fst.comp measurable_fst) (measurableSet_singleton true)
    have htrue : Measurable (fun p : (Bool × β) × ℝ =>
        if p.2 = g p.1.2 then true else false) := by
      have hc1 : Continuous (fun p : (Bool × β) × ℝ => p.2) := continuous_snd
      have hc2 : Continuous (fun p : (Bool × β) × ℝ => g p.1.2) :=
        hg_cont.comp (continuous_snd.comp continuous_fst)
      have hset : MeasurableSet {p : (Bool × β) × ℝ | p.2 = g p.1.2} :=
        (isClosed_eq hc1 hc2).measurableSet
      exact Measurable.piecewise hset measurable_const measurable_const
    -- Goal: Measurable (fun p => if p.1.1 then (if p.2 = g p.1.2 then true else false) else false)
    exact Measurable.piecewise hbool htrue measurable_const
  -- Step 5: C = range e, MeasurableHypotheses
  let C : ConceptClass ℝ Bool := Set.range e
  have hC_meas : MeasurableHypotheses ℝ C := by
    refine ⟨fun h hh => ?_⟩
    obtain ⟨t, rfl⟩ := hh
    simp only [e]
    by_cases hb : t.1
    · simp only [hb, ↓reduceIte, singletonConcept]
      exact Measurable.piecewise (measurableSet_singleton _) measurable_const measurable_const
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, zeroConcept]; exact measurable_const
  -- Step 6: WellBehavedVCMeasTarget
  have hWB : WellBehavedVCMeasTarget ℝ C :=
    borel_param_wellBehavedVCMeasTarget e he
  -- Step 7: C = singletonClassOn (range g)
  have hC_eq : C = singletonClassOn (Set.range g) := by
    ext h; constructor
    · rintro ⟨⟨b, θ⟩, rfl⟩
      by_cases hb : b
      · exact Or.inr ⟨g θ, ⟨θ, rfl⟩, by funext x; simp [e, hb, singletonConcept]⟩
      · exact Or.inl (by funext x; simp [e, hb, zeroConcept])
    · rintro (rfl | ⟨a, ⟨θ, rfl⟩, rfl⟩)
      · exact ⟨(false, θ0), by funext x; simp [e, zeroConcept]⟩
      · exact ⟨(true, θ), by funext x; simp [e, singletonConcept]⟩
  -- Step 8: Separation - construct the witness
  refine ⟨C, hC_meas, hWB, ?_⟩
  intro hKW
  have hA_non' : ¬ MeasurableSet (Set.range g) := hg_range ▸ hA_non
  have hbad_non := singleton_badEvent_not_measurable (Set.range g) hA_non'
  apply hbad_non
  -- Show singletonBadEvent (range g) is MeasurableSet
  -- From KrappWirth V: ghostGapSup C zeroConcept 1 is Measurable
  have hV := hKW.V_measurable (zeroConcept) 1
  have hpre : MeasurableSet (ghostGapSup C zeroConcept 1 ⁻¹' Set.Ici ((1 : ℝ) / 2)) :=
    hV measurableSet_Ici
  -- singletonBadEvent = ghostGapSup preimage
  suffices hsuff : singletonBadEvent (Set.range g) =
      ghostGapSup C zeroConcept 1 ⁻¹' Set.Ici ((1 : ℝ) / 2) by
    rw [hsuff]; exact hpre
  -- Prove the set equality
  ext p
  simp only [singletonBadEvent, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ici,
    ghostGapSup, ghostGapVals, oneSidedGhostGap]
  -- C is nonempty (contains zeroConcept)
  have hC_ne : C.Nonempty := ⟨e (false, θ0), ⟨(false, θ0), rfl⟩⟩
  -- The value set is a subset of the finite grid, hence finite (used by both directions).
  have hfin : {r | ∃ h ∈ C, r =
      EmpiricalError ℝ Bool h (fun i => (p.2 i, zeroConcept (p.2 i)))
        (zeroOneLoss Bool) -
      EmpiricalError ℝ Bool h (fun i => (p.1 i, zeroConcept (p.1 i)))
        (zeroOneLoss Bool)}.Finite := by
    apply Set.Finite.subset (Finset.finite_toSet (ghostGapGrid 1))
    intro r ⟨h, _, hr⟩
    rw [hr]; exact oneSidedGhostGap_mem_grid h zeroConcept 1 p
  constructor
  · -- Forward: witness in singletonClassOn → sSup ≥ 1 / 2
    rintro ⟨h_wit, hh_wit, hge⟩
    have hmem : (EmpiricalError ℝ Bool h_wit
        (fun i => (p.2 i, zeroConcept (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError ℝ Bool h_wit (fun i => (p.1 i, zeroConcept (p.1 i))) (zeroOneLoss Bool)) ∈
      {r | ∃ h ∈ C, r =
        EmpiricalError ℝ Bool h (fun i => (p.2 i, zeroConcept (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError ℝ Bool h (fun i => (p.1 i, zeroConcept (p.1 i))) (zeroOneLoss Bool)} :=
      ⟨h_wit, hC_eq ▸ hh_wit, rfl⟩
    calc (1 : ℝ) / 2 ≤ _ := hge
      _ ≤ sSup _ := le_csSup hfin.bddAbove hmem
  · -- Backward: sSup ≥ 1 / 2 → witness in singletonClassOn
    intro hp
    have hne : {r | ∃ h ∈ C, r =
        EmpiricalError ℝ Bool h (fun i => (p.2 i, zeroConcept (p.2 i)))
          (zeroOneLoss Bool) -
        EmpiricalError ℝ Bool h (fun i => (p.1 i, zeroConcept (p.1 i)))
          (zeroOneLoss Bool)}.Nonempty := by
      obtain ⟨h0, hh0⟩ := hC_ne
      exact ⟨_, h0, hh0, rfl⟩
    obtain ⟨h_star, hh_star, h_eq⟩ := hne.csSup_mem hfin
    exact ⟨h_star, hC_eq ▸ hh_star, by rw [← h_eq]; exact hp⟩
