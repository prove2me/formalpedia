-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.shifted_exponential_top_gap
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:27:25.831218+00:00
-- url     : https://prove2.me/submissions/56e81094-7b47-43a8-8d95-9f61f7b767b5

import Theorems.Thm_StabilityDichotomies_Bijunctive_exponential_coordinate_random_threshold_hazard
import Theorems.Thm_StabilityDichotomies_Bijunctive_shifted_exponential_pair_tie_null
noncomputable section
open scoped Classical BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set StabilityDichotomies.Bijunctive

private def restNonempty (n : ℕ) (hn : 0 < n) : (Finset.univ : Finset (Fin n)).Nonempty :=
  ⟨⟨0,hn⟩, Finset.mem_univ _⟩
private def restMax (n : ℕ) (hn : 0 < n) (i : Fin (n+1))
    (d : Fin (n+1) → ℝ) (y : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' (restNonempty n hn) (fun k : Fin n => y k - d (i.succAbove k))

private theorem restMax_continuous (n : ℕ) (hn : 0 < n) (i : Fin (n+1))
    (d : Fin (n+1) → ℝ) : Continuous (restMax n hn i d) := by
  unfold restMax
  apply Continuous.finset_sup'_apply
  intro k hk
  exact (continuous_apply k).sub continuous_const

private def winner (n : ℕ) (hn : 0 < n) (d : Fin (n+1) → ℝ) (i : Fin (n+1)) : Set (Fin (n+1) → ℝ) :=
  {δ | restMax n hn i d (i.removeNth δ) < δ i - d i}
private def closeWinner (n : ℕ) (hn : 0 < n) (d : Fin (n+1) → ℝ) (t : ℝ) (i : Fin (n+1)) : Set (Fin (n+1) → ℝ) :=
  {δ | restMax n hn i d (i.removeNth δ) < δ i - d i ∧
    δ i - d i ≤ restMax n hn i d (i.removeNth δ) + t}

private theorem winner_measurable (n : ℕ) (hn : 0 < n) (d : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    MeasurableSet (winner n hn d i) := by
  have hrest : Measurable (fun δ : Fin (n+1) → ℝ => restMax n hn i d (i.removeNth δ)) := by
    apply (restMax_continuous n hn i d).measurable.comp
    apply measurable_pi_lambda
    intro k
    simpa only [Fin.removeNth_apply] using measurable_pi_apply (X := fun _ : Fin (n+1) => ℝ) (i.succAbove k)
  exact measurableSet_lt hrest ((measurable_pi_apply (X := fun _ : Fin (n+1) => ℝ) i).sub_const _)

private theorem close_winner_bound (n : ℕ) (hn : 0 < n) (d : Fin (n+1) → ℝ)
    (β t : ℝ) (hβ : 0 < β) (ht : 0 ≤ t) (i : Fin (n+1)) :
    (Measure.pi (fun _ : Fin (n+1) => expMeasure β)) (closeWinner n hn d t i) ≤
      ENNReal.ofReal (1 - Real.exp (-β*t)) *
        (Measure.pi (fun _ : Fin (n+1) => expMeasure β)) (winner n hn d i) := by
  let a : (Fin n → ℝ) → ℝ := fun y => restMax n hn i d y + d i
  have ha : Measurable a := ((restMax_continuous n hn i d).add_const _).measurable
  have h := exponential_coordinate_random_threshold_hazard n i a ha β t hβ ht
  have hE : {δ : Fin (n+1) → ℝ | a (i.removeNth δ) < δ i ∧ δ i ≤ a (i.removeNth δ) + t} =
      closeWinner n hn d t i := by
    ext δ
    simp only [Set.mem_setOf_eq, closeWinner]
    dsimp [a]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  have hW : {δ : Fin (n+1) → ℝ | a (i.removeNth δ) < δ i} = winner n hn d i := by
    ext δ
    simp only [Set.mem_setOf_eq, winner]
    dsimp [a]
    constructor <;> intro h <;> linarith
  rw [hE,hW] at h
  exact h

private theorem winner_dominates (n : ℕ) (hn : 0 < n) (d : Fin (n+1) → ℝ)
    (i j : Fin (n+1)) (hji : j ≠ i) (δ : Fin (n+1) → ℝ)
    (hi : δ ∈ winner n hn d i) : δ j - d j < δ i - d i := by
  obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq hji
  have hmax := Finset.le_sup' (s := (Finset.univ : Finset (Fin n)))
    (fun k : Fin n => (i.removeNth δ) k - d (i.succAbove k)) (Finset.mem_univ k)
  have hw : restMax n hn i d (i.removeNth δ) < δ i - d i := hi
  apply lt_of_le_of_lt _ hw
  simpa only [restMax, Fin.removeNth_apply, hk] using hmax

private theorem winner_disjoint (n : ℕ) (hn : 0 < n) (d : Fin (n+1) → ℝ)
    (i j : Fin (n+1)) (hij : i ≠ j) : Disjoint (winner n hn d i) (winner n hn d j) := by
  apply Set.disjoint_left.mpr
  intro δ hi hj
  have h1 := winner_dominates n hn d i j (Ne.symm hij) δ hi
  have h2 := winner_dominates n hn d j i hij δ hj
  exact (lt_asymm h1) h2

private def tieEvent (n : ℕ) (d : Fin (n+1) → ℝ) : Set (Fin (n+1) → ℝ) :=
  ⋃ i : Fin (n+1), ⋃ j : Fin (n+1), if i = j then ∅ else {δ | δ i - d i = δ j - d j}

private theorem tieEvent_null (n : ℕ) (d : Fin (n+1) → ℝ) (β : ℝ) (hβ : 0 < β) :
    (Measure.pi (fun _ : Fin (n+1) => expMeasure β)) (tieEvent n d) = 0 := by
  unfold tieEvent
  rw [measure_iUnion_null_iff]
  intro i
  rw [measure_iUnion_null_iff]
  intro j
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, ↓reduceIte]
    exact shifted_exponential_pair_tie_null (n+1) β hβ d i j hij

private def gapEvent (n : ℕ) (d : Fin (n+1) → ℝ) (t : ℝ) : Set (Fin (n+1) → ℝ) :=
  {δ | ∃ i j : Fin (n+1), i ≠ j ∧
    (∀ k, δ k - d k ≤ δ i - d i) ∧
    (∀ k, k ≠ i → δ k - d k ≤ δ j - d j) ∧
    (δ i - d i) - (δ j - d j) ≤ t}

private theorem gap_subset_winners_or_tie (n : ℕ) (hn : 0 < n) (d : Fin (n+1) → ℝ) (t : ℝ) :
    gapEvent n d t ⊆ (⋃ i : Fin (n+1), closeWinner n hn d t i) ∪ tieEvent n d := by
  intro δ hδ
  by_cases htie : δ ∈ tieEvent n d
  · exact Or.inr htie
  · obtain ⟨i,j,hij,htop,hsecond,hgap⟩ := hδ
    have hstrict (k : Fin (n+1)) (hki : k ≠ i) : δ k - d k < δ i - d i := by
      apply lt_of_le_of_ne (htop k)
      intro heq
      apply htie
      unfold tieEvent
      apply Set.mem_iUnion.mpr
      refine ⟨k, ?_⟩
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      simp [hki,heq]
    apply Or.inl
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change restMax n hn i d (i.removeNth δ) < δ i - d i ∧
      δ i - d i ≤ restMax n hn i d (i.removeNth δ) + t
    constructor
    · unfold restMax
      apply (Finset.sup'_lt_iff (restNonempty n hn)).mpr
      intro k hk
      simpa [Fin.removeNth_apply] using hstrict (i.succAbove k) (Fin.succAbove_ne i k)
    · obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
      have hmax := Finset.le_sup' (s := (Finset.univ : Finset (Fin n)))
        (fun k : Fin n => (i.removeNth δ) k - d (i.succAbove k)) (Finset.mem_univ k)
      have hmax' : δ j - d j ≤ restMax n hn i d (i.removeNth δ) := by
        simpa only [restMax, Fin.removeNth_apply, hk] using hmax
      linarith

private theorem shifted_exponential_top_gap_succ (n : ℕ) (hn : 0 < n) (β t : ℝ)
    (hβ : 0 < β) (ht : 0 ≤ t) (d : Fin (n+1) → ℝ) :
    ((Measure.pi (fun _ : Fin (n+1) => expMeasure β)) (gapEvent n d t)).toReal ≤
      1 - Real.exp (-β*t) ∧ 1 - Real.exp (-β*t) ≤ β*t := by
  let μ : Measure (Fin (n+1) → ℝ) := Measure.pi (fun _ => expMeasure β)
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  haveI : IsProbabilityMeasure μ := by unfold μ; infer_instance
  let c : ENNReal := ENNReal.ofReal (1 - Real.exp (-β*t))
  have hdis : (↑(Finset.univ : Finset (Fin (n+1))) : Set (Fin (n+1))).PairwiseDisjoint (winner n hn d) := by
    intro i hi j hj hij
    exact winner_disjoint n hn d i j hij
  have hunion : μ (⋃ i : Fin (n+1), winner n hn d i) = ∑ i, μ (winner n hn d i) := by
    have h := measure_biUnion_finset (μ := μ) hdis (by intro i hi; exact winner_measurable n hn d i)
    simpa using h
  have hsum : (∑ i, μ (winner n hn d i)) ≤ 1 := by
    rw [← hunion, ← measure_univ (μ := μ)]
    exact measure_mono (Set.subset_univ _)
  have htie : μ (tieEvent n d) = 0 := tieEvent_null n d β hβ
  have hgap : μ (gapEvent n d t) ≤ c := by
    calc
      _ ≤ μ ((⋃ i : Fin (n+1), closeWinner n hn d t i) ∪ tieEvent n d) :=
        measure_mono (gap_subset_winners_or_tie n hn d t)
      _ ≤ μ (⋃ i : Fin (n+1), closeWinner n hn d t i) + μ (tieEvent n d) := measure_union_le _ _
      _ = μ (⋃ i : Fin (n+1), closeWinner n hn d t i) := by rw [htie,add_zero]
      _ ≤ ∑ i, μ (closeWinner n hn d t i) := measure_iUnion_fintype_le μ _
      _ ≤ ∑ i, c * μ (winner n hn d i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact close_winner_bound n hn d β t hβ ht i
      _ = c * ∑ i, μ (winner n hn d i) := by rw [Finset.mul_sum]
      _ ≤ c * 1 := by gcongr
      _ = c := mul_one _
  have hcoef : 0 ≤ 1 - Real.exp (-β*t) := by
    have he : Real.exp (-β*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith
  constructor
  · change (μ (gapEvent n d t)).toReal ≤ 1 - Real.exp (-β*t)
    have hc : c ≠ ⊤ := ENNReal.ofReal_ne_top
    have h := ENNReal.toReal_mono hc hgap
    rw [show c.toReal = 1 - Real.exp (-β*t) by exact ENNReal.toReal_ofReal hcoef] at h
    exact h
  · have h := Real.add_one_le_exp (-β*t)
    nlinarith

theorem solution (q : ℕ) (hq : 2 ≤ q) (β t : ℝ)
    (hβ : 0 < β) (ht : 0 ≤ t) (d : Fin q → ℝ) :
    ((Measure.pi (fun _ : Fin q => expMeasure β))
      {δ : Fin q → ℝ | ∃ i j : Fin q, i ≠ j ∧
        (∀ k, δ k - d k ≤ δ i - d i) ∧
        (∀ k, k ≠ i → δ k - d k ≤ δ j - d j) ∧
        (δ i - d i) - (δ j - d j) ≤ t}).toReal ≤ 1 - Real.exp (-β * t) ∧
      1 - Real.exp (-β * t) ≤ β * t := by
  cases q with
  | zero => omega
  | succ n =>
    have hn : 0 < n := by omega
    exact shifted_exponential_top_gap_succ n hn β t hβ ht d
