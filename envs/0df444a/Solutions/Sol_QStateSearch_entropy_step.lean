-- Prove2me | solution 1 for QStateSearch.entropy_step
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T07:31:30.385868+00:00
-- url     : https://prove2.me/submissions/c9d1e561-9e7e-467e-aebc-f169519db22d

import Mathlib
open MeasureTheory

theorem solution {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (C : Set α) (hC : MeasurableSet C) (hpos : 0 < μ C) (b : ℕ) (f : α → Fin (2 ^ b))
    (hf : ∀ z, MeasurableSet (f ⁻¹' {z})) :
    ∑ z, ((μ (C ∩ f ⁻¹' {z})).toReal / (μ C).toReal) * Real.log (1 / (μ (C ∩ f ⁻¹' {z})).toReal)
        = Real.log (1 / (μ C).toReal) +
          ∑ z, ((μ (C ∩ f ⁻¹' {z})).toReal / (μ C).toReal) *
            Real.log (1 / ((μ (C ∩ f ⁻¹' {z})).toReal / (μ C).toReal)) ∧
    ∑ z, ((μ (C ∩ f ⁻¹' {z})).toReal / (μ C).toReal) * Real.log (1 / (μ (C ∩ f ⁻¹' {z})).toReal)
        ≤ Real.log (1 / (μ C).toReal) + b * Real.log 2 := by
  set m : ℝ := (μ C).toReal with hm
  set c : Fin (2 ^ b) → ℝ := fun z => (μ (C ∩ f ⁻¹' {z})).toReal with hc
  have hm_pos : 0 < m := by
    rw [hm]
    exact ENNReal.toReal_pos hpos.ne' (measure_ne_top μ C)
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hc_nonneg : ∀ z, 0 ≤ c z := by
    intro z
    rw [hc]
    exact ENNReal.toReal_nonneg
  -- The cells partition C.
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin (2 ^ b))) : Set (Fin (2 ^ b)))
      (fun z => C ∩ f ⁻¹' {z}) := by
    intro z _ z' _ hzz'
    change Disjoint (C ∩ f ⁻¹' {z}) (C ∩ f ⁻¹' {z'})
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at hx hx'
    exact hzz' (hx.2.symm.trans hx'.2)
  have hunion : (⋃ z ∈ (Finset.univ : Finset (Fin (2 ^ b))), (C ∩ f ⁻¹' {z})) = C := by
    ext x
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_prop, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff, true_and]
    constructor
    · rintro ⟨z, hx, -⟩
      exact hx
    · intro hx
      exact ⟨f x, hx, rfl⟩
  have hmeasure : μ C = ∑ z : Fin (2 ^ b), μ (C ∩ f ⁻¹' {z}) := by
    conv_lhs => rw [← hunion]
    rw [measure_biUnion_finset (s := Finset.univ) (f := fun z => C ∩ f ⁻¹' {z}) hdisj
      (fun z _ => hC.inter (hf z))]
  have hsumc : ∑ z, c z = m := by
    rw [hm, hc]
    simp only
    rw [hmeasure]
    exact (ENNReal.toReal_sum (fun z _ => measure_ne_top μ _)).symm
  have hsum_p : ∑ z, c z / m = 1 := by
    rw [← Finset.sum_div, hsumc, div_self hm_ne]
  -- Cell-by-cell log identity.
  have hcell : ∀ z : Fin (2 ^ b),
      c z / m * Real.log (1 / c z) =
        c z / m * Real.log (1 / m) + c z / m * Real.log (1 / (c z / m)) := by
    intro z
    by_cases hz : c z = 0
    · rw [hz]
      simp
    · have hlog : Real.log (1 / c z) = Real.log (1 / m) + Real.log (1 / (c z / m)) := by
        have e : (1 : ℝ) / (c z / m) = m / c z := by
          field_simp
        rw [e, Real.log_div one_ne_zero hz, Real.log_div one_ne_zero hm_ne,
          Real.log_div hm_ne hz, Real.log_one]
        ring
      rw [hlog]
      ring
  have part1 : ∑ z, c z / m * Real.log (1 / c z) =
      Real.log (1 / m) + ∑ z, c z / m * Real.log (1 / (c z / m)) := by
    calc ∑ z, c z / m * Real.log (1 / c z)
        = ∑ z, (c z / m * Real.log (1 / m) +
            c z / m * Real.log (1 / (c z / m))) := by
          apply Finset.sum_congr rfl
          intro z _
          exact hcell z
      _ = ∑ z, c z / m * Real.log (1 / m) +
            ∑ z, c z / m * Real.log (1 / (c z / m)) := Finset.sum_add_distrib
      _ = (∑ z, c z / m) * Real.log (1 / m) +
            ∑ z, c z / m * Real.log (1 / (c z / m)) := by
          rw [Finset.sum_mul]
      _ = 1 * Real.log (1 / m) + ∑ z, c z / m * Real.log (1 / (c z / m)) := by
          rw [hsum_p]
      _ = Real.log (1 / m) + ∑ z, c z / m * Real.log (1 / (c z / m)) := by
          rw [one_mul]
  -- Gibbs' inequality: the entropy is at most log of the support size.
  have hgibbs : ∑ z, c z / m * Real.log (1 / (c z / m)) ≤ (b : ℝ) * Real.log 2 := by
    set p : Fin (2 ^ b) → ℝ := fun z => c z / m with hp
    have hp_nonneg : ∀ z, 0 ≤ p z := by
      intro z
      rw [hp]
      exact div_nonneg (hc_nonneg z) hm_pos.le
    have hp_sum : ∑ z, p z = 1 := by
      rw [hp]
      exact hsum_p
    have hw : ∀ z ∈ (Finset.univ : Finset (Fin (2 ^ b))), 0 ≤ p z :=
      fun z _ => hp_nonneg z
    have hz : ∀ z ∈ (Finset.univ : Finset (Fin (2 ^ b))), 0 ≤ (1 : ℝ) / p z :=
      fun z _ => div_nonneg zero_le_one (hp_nonneg z)
    have hgm := Real.geom_mean_le_arith_mean_weighted
      (Finset.univ : Finset (Fin (2 ^ b))) p (fun z => 1 / p z) hw hp_sum hz
    have hprod_pos : 0 < ∏ z : Fin (2 ^ b), (1 / p z) ^ (p z) := by
      apply Finset.prod_pos
      intro z _
      by_cases hz0 : p z = 0
      · rw [hz0, div_zero, Real.rpow_zero]
        exact one_pos
      · have hpz : 0 < p z := lt_of_le_of_ne (hp_nonneg z) (Ne.symm hz0)
        exact Real.rpow_pos_of_pos (div_pos one_pos hpz) _
    have hsum_pos : 0 < ∑ z : Fin (2 ^ b), p z * (1 / p z) := by
      have hex : ∃ z : Fin (2 ^ b), 0 < p z := by
        by_contra hcon
        push Not at hcon
        have hzero : ∑ z : Fin (2 ^ b), p z = 0 :=
          Finset.sum_eq_zero (fun z _ => le_antisymm (hcon z) (hp_nonneg z))
        rw [hp_sum] at hzero
        exact one_ne_zero hzero
      obtain ⟨z, hzpos⟩ := hex
      apply Finset.sum_pos'
      · intro z _
        exact mul_nonneg (hp_nonneg z) (div_nonneg zero_le_one (hp_nonneg z))
      · exact ⟨z, Finset.mem_univ z, by
          rw [mul_one_div, div_self (ne_of_gt hzpos)]
          exact one_pos⟩
    have hterm_le : ∀ z : Fin (2 ^ b), p z * (1 / p z) ≤ 1 := by
      intro z
      by_cases hz0 : p z = 0
      · rw [hz0, div_zero, mul_zero]
        exact zero_le_one
      · have hpz : 0 < p z := lt_of_le_of_ne (hp_nonneg z) (Ne.symm hz0)
        rw [mul_one_div, div_self (ne_of_gt hpz)]
    have hsum_le : ∑ z : Fin (2 ^ b), p z * (1 / p z) ≤ (2 ^ b : ℝ) := by
      calc ∑ z : Fin (2 ^ b), p z * (1 / p z) ≤ ∑ z : Fin (2 ^ b), (1 : ℝ) :=
            Finset.sum_le_sum (fun z _ => hterm_le z)
        _ = (2 ^ b : ℝ) := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have hprod_log : Real.log (∏ z : Fin (2 ^ b), (1 / p z) ^ (p z)) =
        ∑ z : Fin (2 ^ b), p z * Real.log (1 / p z) := by
      rw [Real.log_prod (fun z _ => by
        by_cases hz0 : p z = 0
        · rw [hz0, div_zero, Real.rpow_zero]
          exact one_ne_zero
        · have hpz : 0 < p z := lt_of_le_of_ne (hp_nonneg z) (Ne.symm hz0)
          exact ne_of_gt (Real.rpow_pos_of_pos (div_pos one_pos hpz) _))]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz0 : p z = 0
      · rw [hz0, div_zero, Real.rpow_zero, Real.log_one, zero_mul]
      · have hpz : 0 < p z := lt_of_le_of_ne (hp_nonneg z) (Ne.symm hz0)
        rw [Real.log_rpow (div_pos one_pos hpz)]
    have hlog2 : Real.log ((2 : ℝ) ^ b) = (b : ℝ) * Real.log 2 := by
      rw [Real.log_pow]
    calc ∑ z : Fin (2 ^ b), p z * Real.log (1 / p z)
        = Real.log (∏ z : Fin (2 ^ b), (1 / p z) ^ (p z)) := hprod_log.symm
      _ ≤ Real.log (∑ z : Fin (2 ^ b), p z * (1 / p z)) :=
          Real.log_le_log hprod_pos hgm
      _ ≤ Real.log ((2 : ℝ) ^ b) := by
          apply Real.log_le_log hsum_pos hsum_le
      _ = (b : ℝ) * Real.log 2 := hlog2
  have part2 : ∑ z, c z / m * Real.log (1 / c z) ≤
      Real.log (1 / m) + (b : ℝ) * Real.log 2 := by
    rw [part1]
    linarith [hgibbs]
  exact ⟨part1, part2⟩
