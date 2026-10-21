-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P02.measureSupport_exists
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:38:16.002757+00:00
-- url     : https://prove2.me/submissions/1c02022a-f2a4-450e-8915-84bc31bb3c23

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P02
noncomputable section

open MeasureTheory Set

open scoped ENNReal Topology CompactlySupported

open QAlgorithms.Papers.Independent.Renew46.P02

universe u v

lemma g64i_part1 {X : Type u} [MeasurableSpace X] (mu : Measure X) (hfin : mu Set.univ < ⊤)
    (nu : Measure X) (_hac : nu ≪ mu) : HasMeasureSupport mu nu := by
  let A : Set ℝ≥0∞ := {r | ∃ N, MeasurableSet N ∧ nu N = 0 ∧ mu N = r}
  have hA : A.Nonempty := ⟨0, ∅, MeasurableSet.empty, by simp, by simp⟩
  obtain ⟨u, -, hlim, hmem⟩ := exists_seq_tendsto_sSup hA (OrderTop.bddAbove A)
  choose N hNm hNn hNmu using hmem
  let M := ⋃ i, N i
  have hMm : MeasurableSet M := MeasurableSet.iUnion hNm
  have hMn : nu M = 0 := measure_iUnion_null hNn
  have hMle : mu M ≤ sSup A := le_sSup ⟨M, hMm, hMn, rfl⟩
  have hMge : sSup A ≤ mu M := by
    refine le_of_tendsto' hlim fun i => ?_
    rw [← hNmu i]; exact measure_mono (subset_iUnion N i)
  have hMfin : mu M < ⊤ := lt_of_le_of_lt (measure_mono (subset_univ _)) hfin
  refine ⟨Mᶜ, hMm.compl, by rw [compl_compl]; exact hMn, fun E hE hES hpos => ?_⟩
  rw [pos_iff_ne_zero]
  intro hE0
  have hU : nu (M ∪ E) = 0 := measure_union_null hMn hE0
  have h1 : mu (M ∪ E) ≤ sSup A := le_sSup ⟨M ∪ E, hMm.union hE, hU, rfl⟩
  have hdisj : Disjoint M E := by
    rw [Set.disjoint_left]; intro x hxM hxE; exact hES hxE hxM
  have h2 : mu (M ∪ E) = mu M + mu E := measure_union hdisj hE
  have h3 : mu M < mu M + mu E := ENNReal.lt_add_right hMfin.ne hpos.ne'
  have := le_antisymm hMle hMge
  rw [h2] at h1
  exact absurd (lt_of_lt_of_le h3 (this ▸ h1)) (lt_irrefl _)

lemma g64i_part2 {X : Type u} [MeasurableSpace X] (mu : Measure X) (f : X → ℝ≥0∞)
    (hf : Measurable f) : HasMeasureSupport mu (mu.withDensity f) := by
  have hS : MeasurableSet (Function.support f) := measurableSet_support hf
  refine ⟨Function.support f, hS, ?_, fun E hE hES hpos => ?_⟩
  · rw [withDensity_apply _ hS.compl]
    rw [setLIntegral_congr_fun hS.compl (fun x hx => by
      simpa [Function.mem_support] using hx)]
    simp
  · rw [withDensity_apply _ hE, lintegral_pos_iff_support hf, Measure.restrict_apply hS,
      Set.inter_eq_right.mpr hES]
    exact hpos

theorem solution {X : Type u} [MeasurableSpace X] (mu : Measure X) :
    ((mu Set.univ < ⊤) → ∀ nu : Measure X, nu ≪ mu → HasMeasureSupport mu nu) ∧
    (∀ f : X → ℝ≥0∞, Measurable f → HasMeasureSupport mu (mu.withDensity f)) :=
  ⟨fun h nu hac => g64i_part1 mu h nu hac, fun f hf => g64i_part2 mu f hf⟩

end
