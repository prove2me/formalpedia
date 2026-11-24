-- Prove2me | solution 1 for SPHardness.FixedRecourse.vol_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T00:17:33.529486+00:00
-- url     : https://prove2.me/submissions/e399fa36-6b37-4f7c-bc58-5019e231f8dc

import Mathlib
import Definitions.Def_SPHardness_FixedRecourse_Model

noncomputable section
open MeasureTheory
open scoped BigOperators

open SPHardness.FixedRecourse

theorem solution {k : ℕ} (hk : 0 < k) (α : Fin k → ℝ)
    (hα : ∀ j, 0 ≤ α j) (hαk : 0 < lastWeight hk α) :
    ∀ β β' : ℝ, β ≤ β' →
      0 ≤ vol α β' - vol α β ∧
      vol α β' - vol α β ≤ (β' - β) / lastWeight hk α := by
  intro β β' hββ
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hlast : lastWeight hk α = α (Fin.last n) := by
    unfold lastWeight; congr 1
  rw [hlast] at hαk ⊢
  have hcube : ∀ m : ℕ, volume (cube m) = 1 := by
    intro m
    rw [cube, volume_pi_pi]
    simp
  have hcubeM : ∀ m : ℕ, MeasurableSet (cube m) := fun m =>
    MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hmeasK : ∀ γ, MeasurableSet (knapsack α γ) := by
    intro γ
    have h2 : MeasurableSet {ξ : Fin (n + 1) → ℝ | ∑ j, α j * ξ j ≤ γ} :=
      measurableSet_le (by fun_prop) measurable_const
    exact (hcubeM (n + 1)).inter h2
  have hfin : ∀ γ, volume (knapsack α γ) ≠ ⊤ := fun γ =>
    ne_top_of_le_ne_top (by rw [hcube]; exact ENNReal.one_ne_top) (measure_mono (fun ξ hξ => hξ.1))
  have hsub : knapsack α β ⊆ knapsack α β' := fun ξ hξ => ⟨hξ.1, hξ.2.trans hββ⟩
  have hdiff : vol α β' - vol α β = (volume (knapsack α β' \ knapsack α β)).toReal := by
    unfold vol
    rw [measure_diff hsub (hmeasK β).nullMeasurableSet (hfin β),
      ENNReal.toReal_sub_of_le (measure_mono hsub) (hfin β')]
  rw [hdiff]
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have hδ : 0 ≤ (β' - β) / α (Fin.last n) := div_nonneg (by linarith) hαk.le
  apply ENNReal.toReal_le_of_le_ofReal hδ
  set a := α (Fin.last n) with ha
  let c : (Fin n → ℝ) → ℝ := fun y => ∑ j : Fin n, α ((Fin.last n).succAbove j) * y j
  let E : Set (ℝ × (Fin n → ℝ)) :=
    {p | p.2 ∈ cube n ∧ β < a * p.1 + c p.2 ∧ a * p.1 + c p.2 ≤ β'}
  have memE : ∀ x y, (x, y) ∈ E ↔ (y ∈ cube n ∧ β < a * x + c y ∧ a * x + c y ≤ β') :=
    fun _ _ => Iff.rfl
  have hc_meas : Measurable c := by
    show Measurable (fun y : Fin n → ℝ => ∑ j : Fin n, α ((Fin.last n).succAbove j) * y j)
    fun_prop
  have hf : Measurable (fun p : ℝ × (Fin n → ℝ) => a * p.1 + c p.2) :=
    (measurable_const.mul measurable_fst).add (hc_meas.comp measurable_snd)
  have hE : MeasurableSet E :=
    (measurable_snd (hcubeM n)).inter
      ((measurableSet_lt measurable_const hf).inter (measurableSet_le hf measurable_const))
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have hDsub : knapsack α β' \ knapsack α β ⊆
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)) ⁻¹' E := by
    rintro ξ ⟨⟨hcube', hle⟩, hnot⟩
    have hlt : β < ∑ j, α j * ξ j := by
      by_contra h
      push_neg at h
      exact hnot ⟨hcube', h⟩
    have hsplit : ∑ j, α j * ξ j = a * ξ (Fin.last n) +
        ∑ j : Fin n, α ((Fin.last n).succAbove j) * ξ ((Fin.last n).succAbove j) :=
      Fin.sum_univ_succAbove _ (Fin.last n)
    show (fun j => ξ ((Fin.last n).succAbove j)) ∈ cube n ∧
      β < a * ξ (Fin.last n) +
        ∑ j : Fin n, α ((Fin.last n).succAbove j) * ξ ((Fin.last n).succAbove j) ∧
      a * ξ (Fin.last n) +
        ∑ j : Fin n, α ((Fin.last n).succAbove j) * ξ ((Fin.last n).succAbove j) ≤ β'
    refine ⟨fun j _ => hcube' _ (Set.mem_univ _), ?_, ?_⟩
    · linarith
    · linarith
  calc volume (knapsack α β' \ knapsack α β)
      ≤ volume ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)) ⁻¹' E) :=
        measure_mono hDsub
    _ = (volume : Measure (ℝ × (Fin n → ℝ))) E := hmp.measure_preimage hE.nullMeasurableSet
    _ = ∫⁻ y, volume ((fun x => (x, y)) ⁻¹' E) ∂(volume : Measure (Fin n → ℝ)) := by
        rw [Measure.volume_eq_prod]
        exact Measure.prod_apply_symm hE
    _ ≤ ∫⁻ y, (cube n).indicator (fun _ => ENNReal.ofReal ((β' - β) / a)) y
          ∂(volume : Measure (Fin n → ℝ)) := by
        apply lintegral_mono
        intro y
        by_cases hy : y ∈ cube n
        · rw [Set.indicator_of_mem hy]
          calc volume ((fun x => (x, y)) ⁻¹' E)
              ≤ volume (Set.Ioc ((β - c y) / a) ((β' - c y) / a)) := by
                apply measure_mono
                intro x hx
                obtain ⟨_, h1, h2⟩ := (memE x y).mp hx
                constructor
                · rw [div_lt_iff₀ hαk]; linarith
                · rw [le_div_iff₀ hαk]; linarith
            _ = ENNReal.ofReal ((β' - β) / a) := by
                rw [Real.volume_Ioc]
                congr 1
                ring
        · rw [Set.indicator_of_notMem hy]
          exact (measure_mono_null (fun x hx => (hy ((memE x y).mp hx).1).elim)
            measure_empty).le
    _ = ENNReal.ofReal ((β' - β) / a) * volume (cube n) := lintegral_indicator_const (hcubeM n) _
    _ = ENNReal.ofReal ((β' - β) / a) := by rw [hcube, mul_one]
