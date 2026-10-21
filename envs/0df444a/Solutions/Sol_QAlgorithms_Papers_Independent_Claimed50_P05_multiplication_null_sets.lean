-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P05.multiplication_null_sets
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T11:22:33.8207+00:00
-- url     : https://prove2.me/submissions/3f8ff3b6-66ec-4b5e-b399-b4f0aba53b48

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped Topology ENNReal InnerProductSpace
open QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P05
universe u v w
variable {k : Type*} [RCLike k]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

theorem g58b_mult_null (mu : Measure X) (hmu : Semifinite mu)
    (A : Set X) (hA : MeasurableSet A) :
    mu A = 0 ↔ Null (multiplication (k := k) mu) A := by
  constructor
  · intro h0
    refine ⟨hA, ?_⟩
    have hae : ∀ᵐ x ∂mu, x ∉ A := measure_eq_zero_iff_ae_notMem.mp h0
    ext ⟨u, v⟩
    simp only [multiplication, zeroGraph, Set.mem_setOf_eq]
    rw [Lp.eq_zero_iff_ae_eq_zero]
    constructor
    · intro h
      filter_upwards [h, hae] with x hx hxA
      rw [hx]
      simp [P05.indicator, Set.indicator, hxA]
    · intro h
      filter_upwards [h, hae] with x hx hxA
      rw [hx]
      simp [P05.indicator, Set.indicator, hxA]
  · rintro ⟨hA', hz⟩
    by_contra hne
    obtain ⟨B, hB, hBA, hB0, hBfin⟩ : ∃ B : Set X, MeasurableSet B ∧ B ⊆ A ∧ 0 < mu B ∧ mu B < ⊤ := by
      by_cases htop : mu A = ⊤
      · exact hmu A hA htop
      · exact ⟨A, hA, le_rfl, pos_iff_ne_zero.mpr hne, lt_top_iff_ne_top.mpr htop⟩
    set u : Lp k 2 mu := indicatorConstLp 2 hB hBfin.ne (1 : k)
    have hu : (u, u) ∈ multiplication (k := k) mu (P05.indicator A hA') := by
      show ∀ᵐ x ∂mu, u x = (P05.indicator A hA').val x * u x
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hB) (hμs := hBfin.ne) (c := (1 : k))]
        with x hx
      rw [hx]
      by_cases hxB : x ∈ B
      · simp [P05.indicator, Set.indicator, hxB, hBA hxB]
      · simp [Set.indicator, hxB]
    rw [hz] at hu
    have hu0 : u = 0 := hu
    have hn := norm_indicatorConstLp (p := (2 : ℝ≥0∞)) (hs := hB) (hμs := hBfin.ne) (c := (1 : k))
      (by norm_num) (by norm_num)
    change ‖u‖ = _ at hn
    rw [hu0, norm_zero, norm_one, one_mul] at hn
    have hr : mu.real B = 0 := by
      have h2 : (0 : ℝ) ≤ mu.real B := measureReal_nonneg
      by_contra hne'
      have : 0 < mu.real B ^ (1 / (2 : ℝ≥0∞).toReal) :=
        Real.rpow_pos_of_pos (lt_of_le_of_ne h2 (Ne.symm hne')) _
      linarith
    rw [measureReal_eq_zero_iff hBfin.ne] at hr
    exact (ne_of_gt hB0) hr

theorem solution (mu : Measure X) (hmu : Semifinite mu)
    (A : Set X) (hA : MeasurableSet A) :
    mu A = 0 ↔ Null (multiplication (k := k) mu) A := g58b_mult_null mu hmu A hA
