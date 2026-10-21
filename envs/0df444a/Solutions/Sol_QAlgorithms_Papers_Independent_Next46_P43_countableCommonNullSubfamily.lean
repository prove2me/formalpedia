-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P43.countableCommonNullSubfamily
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:01:12.448986+00:00
-- url     : https://prove2.me/submissions/9d5b11da-e994-4c28-abf8-0ecf8e8eba00

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P43
noncomputable section

open MeasureTheory Filter

open scoped ENNReal BigOperators

open QAlgorithms.Papers.Independent.Next46.P43

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsTraceClass IsDensity State tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (homogeneousEntropy generalizedRelativeEntropy traceFirst traceSecond)

theorem solution
    {X Theta : Type*} [MeasurableSpace X] [Nonempty Theta]
    (P : Theta → Measure X) (hProb : ∀ theta, IsProbabilityMeasure (P theta))
    (mu : Measure X) [SigmaFinite mu]
    (hDom : ∀ theta, P theta ≪ mu) :
    ∃ selected : ℕ → Theta, ∀ A, MeasurableSet A →
      ((∀ theta, P theta A = 0) ↔ ∀ n, P (selected n) A = 0) := by
  classical
  set ν := mu.toFinite with hν
  have hD : ∀ theta, P theta ≪ ν := fun theta =>
    (hDom theta).trans (absolutelyContinuous_toFinite mu)
  let S : Theta → Set X := fun theta => {x | (P theta).rnDeriv ν x ≠ 0}
  have hSm : ∀ theta, MeasurableSet (S theta) := fun theta =>
    (Measure.measurable_rnDeriv _ _) (measurableSet_singleton 0).compl
  have hnull : ∀ theta A, P theta A = 0 ↔ ν (S theta ∩ A) = 0 := by
    intro theta A
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ (hD theta)]
    exact withDensity_apply_eq_zero' (Measure.measurable_rnDeriv _ _).aemeasurable
  let U : (ℕ → Theta) → Set X := fun f => ⋃ n, S (f n)
  let s : (ℕ → Theta) → ℝ≥0∞ := fun f => ν (U f)
  have hbdd : BddAbove (Set.range s) := ⟨ν Set.univ, by
    rintro _ ⟨f, rfl⟩; exact measure_mono (Set.subset_univ _)⟩
  obtain ⟨u, -, hu, hmem⟩ := exists_seq_tendsto_sSup (Set.range_nonempty s) hbdd
  choose F hF using hmem
  let g : ℕ → Theta := fun m => F (Nat.unpair m).1 (Nat.unpair m).2
  have hUg : ∀ k, U (F k) ⊆ U g := by
    intro k x hx
    simp only [U, Set.mem_iUnion] at hx ⊢
    obtain ⟨n, hn⟩ := hx
    exact ⟨Nat.pair k n, by simp [g, Nat.unpair_pair, hn]⟩
  have hge : sSup (Set.range s) ≤ s g :=
    le_of_tendsto' hu (fun k => by rw [← hF k]; exact measure_mono (hUg k))
  have hdiff : ∀ theta, ν (S theta \ U g) = 0 := by
    intro theta
    let g' : ℕ → Theta := fun m => match m with | 0 => theta | m + 1 => g m
    have hsub : U g ∪ (S theta \ U g) ⊆ U g' := by
      intro x hx
      simp only [U, Set.mem_union, Set.mem_sdiff, Set.mem_iUnion] at hx ⊢
      rcases hx with ⟨n, hn⟩ | ⟨hx, -⟩
      · exact ⟨n + 1, hn⟩
      · exact ⟨0, hx⟩
    have hUm : MeasurableSet (U g) := MeasurableSet.iUnion (fun n => hSm _)
    have h1 : ν (U g) + ν (S theta \ U g) ≤ ν (U g) + 0 := by
      rw [← measure_union Set.disjoint_sdiff_right ((hSm theta).diff hUm), add_zero]
      calc ν (U g ∪ (S theta \ U g)) ≤ ν (U g') := measure_mono hsub
        _ ≤ sSup (Set.range s) := le_csSup hbdd ⟨g', rfl⟩
        _ ≤ ν (U g) := hge
    exact le_antisymm ((ENNReal.add_le_add_iff_left (measure_ne_top _ _)).1 h1) bot_le
  refine ⟨g, fun A hA => ⟨fun h n => h _, fun h theta => ?_⟩⟩
  have hUA : ν (U g ∩ A) = 0 := by
    simp only [U, Set.iUnion_inter]
    exact measure_iUnion_null (fun n => (hnull _ _).1 (h n))
  rw [hnull]
  refine le_antisymm ?_ bot_le
  calc ν (S theta ∩ A) ≤ ν ((S theta \ U g) ∪ (U g ∩ A)) := by
        apply measure_mono
        intro x ⟨hx1, hx2⟩
        by_cases hx : x ∈ U g
        · exact Or.inr ⟨hx, hx2⟩
        · exact Or.inl ⟨hx1, hx⟩
    _ ≤ ν (S theta \ U g) + ν (U g ∩ A) := measure_union_le _ _
    _ = 0 := by rw [hdiff, hUA, add_zero]
