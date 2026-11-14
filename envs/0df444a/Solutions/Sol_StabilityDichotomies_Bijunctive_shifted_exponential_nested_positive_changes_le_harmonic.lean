-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.shifted_exponential_nested_positive_changes_le_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:10:35.720206+00:00
-- url     : https://prove2.me/submissions/7ed0a19b-6376-4522-9d16-dbf0cf05f719

import Theorems.Thm_StabilityDichotomies_Bijunctive_conditional_exponential_nested_group_changes_le_harmonic
import Theorems.Thm_StabilityDichotomies_Bijunctive_finite_partition_conditional_event_sum_bound
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Bijunctive

private def changeEvent {α κ : Type} (T S : Finset α) (d : α → ℝ) (label : α → κ) : Set (α → ℝ) :=
  {x | ∃ a ∈ T, ∃ b ∈ S, 0 < x a - d a ∧ 0 < x b - d b ∧
    (∀ j ∈ T, j ≠ a → x j - d j < x a - d a) ∧
    (∀ j ∈ S, x j - d j ≤ x b - d b) ∧ label a ≠ label b}
private theorem changeEvent_measurable {α κ : Type} [Fintype α]
    (T S : Finset α) (d : α → ℝ) (label : α → κ) : MeasurableSet (changeEvent T S d label) := by
  classical
  simp only [changeEvent,setOf_exists,setOf_and,setOf_forall]
  apply MeasurableSet.iUnion; intro a
  apply MeasurableSet.inter (by by_cases h : a ∈ T <;> simp [h])
  apply MeasurableSet.iUnion; intro b
  apply MeasurableSet.inter (by by_cases h : b ∈ S <;> simp [h])
  apply MeasurableSet.inter
  · exact measurableSet_lt measurable_const ((measurable_pi_apply a).sub_const _)
  apply MeasurableSet.inter
  · exact measurableSet_lt measurable_const ((measurable_pi_apply b).sub_const _)
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter; intro j
    apply MeasurableSet.iInter; intro hj
    apply MeasurableSet.iInter; intro hne
    exact measurableSet_lt ((measurable_pi_apply j).sub_const _) ((measurable_pi_apply a).sub_const _)
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter; intro j
    apply MeasurableSet.iInter; intro hj
    exact measurableSet_le ((measurable_pi_apply j).sub_const _) ((measurable_pi_apply b).sub_const _)
  · apply MeasurableSet.iInter; intro h
    exact MeasurableSet.empty

private theorem harmonic_real_mono {m n : ℕ} (hmn : m ≤ n) : (harmonic m : ℝ) ≤ harmonic n := by
  simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
  intro i hi hnot
  positivity

private theorem harmonic_real_nonneg (n : ℕ) : 0 ≤ (harmonic n : ℝ) := by
  simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  positivity

theorem solution
    {α κ : Type} [Fintype α] (sets : ℕ → Finset α) (k : ℕ)
    (hsub : ∀ i < k, sets (i+1) ⊆ sets i) (label : α → κ)
    (d : α → ℝ) (hd : ∀ a, 0 ≤ d a) (β : ℝ) (hβ : 0 < β) :
    (∑ i ∈ Finset.range k,
      (Measure.pi (fun _ : α => expMeasure β)
        {x : α → ℝ | ∃ a ∈ sets i, ∃ b ∈ sets (i+1),
          0 < x a - d a ∧ 0 < x b - d b ∧
          (∀ j ∈ sets i, j ≠ a → x j - d j < x a - d a) ∧
          (∀ j ∈ sets (i+1), x j - d j ≤ x b - d b) ∧ label a ≠ label b}).toReal) ≤
      (harmonic (sets 0).card : ℝ) := by
  classical
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  let μ : Measure (α → ℝ) := Measure.pi (fun _ => expMeasure β)
  haveI : IsProbabilityMeasure μ := by unfold μ; infer_instance
  let P : Finset α → Set (α → ℝ) := fun S => {x | ∀ a, a ∈ S ↔ d a < x a}
  let E : Fin k → Set (α → ℝ) := fun i => changeEvent (sets i.val) (sets (i.val+1)) d label
  let B : ℝ := harmonic (sets 0).card
  have hPmeas (S : Finset α) : MeasurableSet (P S) := by
    have he : P S = Set.univ.pi (fun a => if a ∈ S then Ioi (d a) else Iic (d a)) := by
      ext x
      simp only [P,mem_setOf_eq,mem_univ_pi]
      constructor
      · intro h a
        by_cases ha : a ∈ S
        · simp [ha,(h a).mp ha]
        · have hn : ¬ d a < x a := fun hx => ha ((h a).mpr hx)
          simp [ha,le_of_not_gt hn]
      · intro h a
        by_cases ha : a ∈ S
        · simp only [ha,true_iff]
          simpa [ha] using h a
        · simp only [ha,false_iff]
          have hh : x a ≤ d a := by simpa [ha] using h a
          exact not_lt_of_ge hh
    rw [he]
    apply MeasurableSet.univ_pi
    intro a
    split_ifs <;> first | exact measurableSet_Ioi | exact measurableSet_Iic
  have hdis : Pairwise (Disjoint on P) := by
    intro S T hne
    apply Set.disjoint_left.mpr
    intro x hxS hxT
    apply hne
    apply Finset.ext
    intro a
    exact (hxS a).trans (hxT a).symm
  have hcover : (⋃ S : Finset α, P S) = Set.univ := by
    ext x
    simp only [mem_iUnion,mem_univ,iff_true]
    refine ⟨Finset.univ.filter (fun a => d a < x a),?_⟩
    intro a
    simp
  have hEmeas (i : Fin k) : MeasurableSet (E i) := changeEvent_measurable _ _ _ _
  have hB : 0 ≤ B := harmonic_real_nonneg _
  have hcond (S : Finset α) (hcell : μ (P S) ≠ 0) :
      ∑ i : Fin k, (ProbabilityTheory.cond μ (P S)).real (E i) ≤ B := by
    let rect : α → Set ℝ := fun a => if a ∈ S then Ioi (d a) else Iic (d a)
    have hrect : P S = Set.univ.pi rect := by
      ext x
      simp only [P,mem_setOf_eq,mem_univ_pi,rect]
      constructor
      · intro h a
        by_cases ha : a ∈ S
        · simp [ha,(h a).mp ha]
        · have hn : ¬ d a < x a := fun hx => ha ((h a).mpr hx)
          simp [ha,le_of_not_gt hn]
      · intro h a
        by_cases ha : a ∈ S
        · simp only [ha,true_iff]
          simpa [ha] using h a
        · simp only [ha,false_iff]
          have hh : x a ≤ d a := by simpa [ha] using h a
          exact not_lt_of_ge hh
    have hrmeas (a : α) : MeasurableSet (rect a) := by
      dsimp [rect]
      split_ifs <;> first | exact measurableSet_Ioi | exact measurableSet_Iic
    have hrpos (a : α) : (expMeasure β) (rect a) ≠ 0 := by
      intro ha
      apply hcell
      rw [hrect,show μ = Measure.pi (fun _ : α => expMeasure β) from rfl, Measure.pi_pi]
      exact Finset.prod_eq_zero (Finset.mem_univ a) ha
    let active : ℕ → Finset ↥S := fun i => Finset.univ.filter (fun a => a.val ∈ sets i)
    have hactive (i : ℕ) : ∀ a : ↥S, a ∈ active i ↔ a.val ∈ sets i := by simp [active]
    have hnested : ∀ i < k, active (i+1) ⊆ active i := by
      intro i hi a ha
      exact (hactive i a).mpr (hsub i hi ((hactive (i+1) a).mp ha))
    have hsel : ∀ a ∈ S, rect a = Ioi (d a) := by intro a ha; simp [rect,ha]
    have hD : ∀ a ∈ S, 0 ≤ d a := fun a _ => hd a
    have hmain := conditional_exponential_nested_group_changes_le_harmonic S β hβ d rect hrmeas hrpos hD hsel
      active k hnested (fun a => label a.val)
    let ν := ProbabilityTheory.cond μ (P S)
    let E' : ℕ → Set (α → ℝ) := fun i => {x | ∃ a ∈ active i, ∃ b ∈ active (i+1),
      (∀ j ∈ active i, j ≠ a → x j - d j < x a - d a) ∧
      (∀ j ∈ active (i+1), x j - d j ≤ x b - d b) ∧ label a.val ≠ label b.val}
    have hPae : ∀ᵐ x ∂ν, x ∈ P S := ProbabilityTheory.ae_cond_mem (hPmeas S)
    haveI : IsProbabilityMeasure ν := cond_isProbabilityMeasure_of_finite hcell (measure_ne_top μ _)
    have hle (i : Fin k) : ν.real (E i) ≤ ν.real (E' i.val) := by
      apply ENNReal.toReal_mono (measure_ne_top ν _)
      apply measure_mono_ae
      filter_upwards [hPae] with x hx hEi
      obtain ⟨a,ha,b,hb,hpa,hpb,hmaxa,hmaxb,hlab⟩ := hEi
      have haS : a ∈ S := (hx a).mpr (by linarith)
      have hbS : b ∈ S := (hx b).mpr (by linarith)
      let aa : ↥S := ⟨a,haS⟩
      let bb : ↥S := ⟨b,hbS⟩
      refine ⟨aa,(hactive i.val aa).mpr ha,bb,(hactive (i.val+1) bb).mpr hb,?_,?_,hlab⟩
      · intro j hj hne
        have hjA := (hactive i.val j).mp hj
        have hjne : j.val ≠ a := by intro hh; apply hne; exact Subtype.ext hh
        exact hmaxa j.val hjA hjne
      · intro j hj
        exact hmaxb j.val ((hactive (i.val+1) j).mp hj)
    have hcard : (active 0).card ≤ (sets 0).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro a ha
        exact (hactive 0 a).mp ha
      · intro a _ b _ hab
        exact Subtype.ext hab
    have hmain' : (∑ i : Fin k, ν.real (E' i.val)) ≤ (harmonic (active 0).card : ℝ) := by
      rw [Fin.sum_univ_eq_sum_range (fun i => ν.real (E' i)) k]
      rw [← hrect] at hmain
      exact hmain
    calc
      _ ≤ ∑ i : Fin k, ν.real (E' i.val) := Finset.sum_le_sum (fun i _ => hle i)
      _ ≤ (harmonic (active 0).card : ℝ) := hmain'
      _ ≤ B := harmonic_real_mono hcard
  have h := finite_partition_conditional_event_sum_bound μ P E B hPmeas hEmeas hdis hcover hB hcond
  change (∑ i : Fin k, μ.real (changeEvent (sets i.val) (sets (i.val+1)) d label)) ≤ B at h
  rw [Fin.sum_univ_eq_sum_range (fun i => μ.real (changeEvent (sets i) (sets (i+1)) d label)) k] at h
  exact h
