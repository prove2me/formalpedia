-- Prove2me | solution 1 for ServiceParts.RealTime.largest_cn_solution
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T09:37:23.853548+00:00
-- url     : https://prove2.me/submissions/cd73cad4-5c94-4cac-bd45-b4a7f503dc2b

import Mathlib
import Definitions.Def_ServiceParts_RealTime_Model

open MeasureTheory


namespace ServiceParts.RealTime

variable {J : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma sp_meas (M : ItemModel J Ω P) (j : J) (t : ℕ) (S : ℤ) :
    MeasurableSet {ω | ((M.X j t ω : ℕ) : ℤ) ≤ S} :=
  (M.X_measurable j t) (MeasurableSet.of_discrete (s := {n : ℕ | (n : ℤ) ≤ S}))

lemma sp_int1 [IsProbabilityMeasure P] (M : ItemModel J Ω P) (j : J) (t : ℕ) (S : ℤ) :
    Integrable (fun ω => max ((S : ℝ) - (M.X j t ω : ℝ)) 0) P :=
  ((integrable_const _).sub (M.X_integrable j t)).sup (integrable_zero _ _ _)

lemma sp_int2 [IsProbabilityMeasure P] (M : ItemModel J Ω P) (j : J) (t : ℕ) (S : ℤ) :
    Integrable (fun ω => max ((M.X j t ω : ℝ) - (S : ℝ)) 0) P :=
  ((M.X_integrable j t).sub (integrable_const _)).sup (integrable_zero _ _ _)

lemma sp_dG [IsProbabilityMeasure P] (M : ItemModel J Ω P) (j : J) (t : ℕ) (S : ℤ) :
    M.G j t (S + 1) - M.G j t S = (M.h j + M.b j) * M.demandCDF j t S - M.b j := by
  set E := {ω | ((M.X j t ω : ℕ) : ℤ) ≤ S} with hEdef
  have hE : MeasurableSet E := sp_meas M j t S
  have hF : M.demandCDF j t S = P.real E := rfl
  have hA : (∫ ω, max (((S + 1 : ℤ) : ℝ) - (M.X j t ω : ℝ)) 0 ∂P)
      - ∫ ω, max ((S : ℝ) - (M.X j t ω : ℝ)) 0 ∂P = P.real E := by
    rw [← integral_sub (sp_int1 M j t (S+1)) (sp_int1 M j t S), ← integral_indicator_one hE]
    congr 1; funext ω
    simp only [Set.indicator, hEdef, Set.mem_setOf_eq, Pi.one_apply]
    split_ifs with h
    · have : (M.X j t ω : ℝ) ≤ (S : ℝ) := by exact_mod_cast h
      push_cast
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring
    · have : (S : ℝ) + 1 ≤ (M.X j t ω : ℝ) := by
        have : S + 1 ≤ ((M.X j t ω : ℕ) : ℤ) := by omega
        exact_mod_cast this
      push_cast
      rw [max_eq_right (by linarith), max_eq_right (by linarith)]; ring
  have hB : (∫ ω, max ((M.X j t ω : ℝ) - ((S + 1 : ℤ) : ℝ)) 0 ∂P)
      - ∫ ω, max ((M.X j t ω : ℝ) - (S : ℝ)) 0 ∂P = P.real E - 1 := by
    rw [← integral_sub (sp_int2 M j t (S+1)) (sp_int2 M j t S)]
    have : (fun ω => max ((M.X j t ω : ℝ) - ((S + 1 : ℤ) : ℝ)) 0
        - max ((M.X j t ω : ℝ) - (S : ℝ)) 0) = fun ω => E.indicator 1 ω - 1 := by
      funext ω
      simp only [Set.indicator, hEdef, Set.mem_setOf_eq, Pi.one_apply]
      split_ifs with h
      · have : (M.X j t ω : ℝ) ≤ (S : ℝ) := by exact_mod_cast h
        push_cast
        rw [max_eq_right (by linarith), max_eq_right (by linarith)]; ring
      · have : (S : ℝ) + 1 ≤ (M.X j t ω : ℝ) := by
          have : S + 1 ≤ ((M.X j t ω : ℕ) : ℤ) := by omega
          exact_mod_cast this
        push_cast
        rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring
    rw [this, integral_sub ((integrable_const 1).indicator hE) (integrable_const 1),
      integral_indicator_one hE]
    simp
  simp only [ItemModel.G]
  rw [hF]
  linear_combination M.h j * hA + M.b j * hB

lemma sp_cdf_mono [IsProbabilityMeasure P] (M : ItemModel J Ω P) (j : J) (t : ℕ) :
    Monotone (M.demandCDF j t) := by
  intro a b hab
  unfold ItemModel.demandCDF
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro ω h; simp only [Set.mem_setOf_eq] at *; omega

lemma sp_cdf_neg [IsProbabilityMeasure P] (M : ItemModel J Ω P) (j : J) (t : ℕ) (S : ℤ)
    (hS : S < 0) : M.demandCDF j t S = 0 := by
  unfold ItemModel.demandCDF
  have : {ω | ((M.X j t ω : ℕ) : ℤ) ≤ S} = ∅ := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]; omega
  simp [this]

lemma sp_cdf_large [IsProbabilityMeasure P] (M : ItemModel J Ω P) (j : J) (t : ℕ) (β : ℝ)
    (hβ : β < 1) : ∃ S : ℤ, β < M.demandCDF j t S := by
  have hm : Monotone (fun n : ℕ => {ω | ((M.X j t ω : ℕ) : ℤ) ≤ (n : ℤ)}) := by
    intro a b hab ω h; simp only [Set.mem_setOf_eq] at *; omega
  have hU : (⋃ n : ℕ, {ω | ((M.X j t ω : ℕ) : ℤ) ≤ (n : ℤ)}) = Set.univ := by
    ext ω; simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨M.X j t ω, le_rfl⟩
  have ht := tendsto_measure_iUnion_atTop (μ := P) hm
  rw [hU, measure_univ] at ht
  have ht2 := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp ht
  simp only [ENNReal.toReal_one] at ht2
  obtain ⟨n, hn⟩ := (ht2.eventually (lt_mem_nhds hβ)).exists
  exact ⟨n, hn⟩

lemma sp_up (f : ℤ → ℝ) (s0 : ℤ) (h : ∀ S, s0 ≤ S → f S < f (S + 1)) :
    ∀ A B, s0 ≤ A → A < B → f A < f B := by
  intro A B hA hAB
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr (show A + 1 ≤ B by omega))
  have hB : B = A + 1 + k := by omega
  subst hB
  induction k with
  | zero => simpa using h A hA
  | succ k ih =>
    have := h (A + 1 + k) (by omega)
    have e : A + 1 + ((k + 1 : ℕ) : ℤ) = A + 1 + k + 1 := by push_cast; ring
    rw [e]; exact lt_trans (ih (by omega) (by omega)) this

lemma sp_down (f : ℤ → ℝ) (s0 : ℤ) (h : ∀ S, S < s0 → f (S + 1) ≤ f S) :
    ∀ A B, A ≤ B → B ≤ s0 → f B ≤ f A := by
  intro A B hAB hB
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hAB)
  have hB' : B = A + k := by omega
  subst hB'
  induction k with
  | zero => simp
  | succ k ih =>
    have := h (A + k) (by push_cast at hB; omega)
    have e : A + ((k + 1 : ℕ) : ℤ) = A + k + 1 := by push_cast; ring
    rw [e]; exact le_trans this (ih (by omega) (by push_cast at hB ⊢; omega) (by omega))

theorem sp_lcn_core [IsProbabilityMeasure P] (M : ItemModel J Ω P) (j : J) (t : ℕ) :
    (∃ s0 : ℤ, IsLeast {s : ℤ | M.b j / (M.b j + M.h j) < M.demandCDF j t s} s0) ∧
      ∀ s0 : ℤ, IsLeast {s : ℤ | M.b j / (M.b j + M.h j) < M.demandCDF j t s} s0 →
        M.IsLargestCNSolution j t (max (M.baseSupply j t) s0) := by
  have hb := M.b_pos j
  have hh := M.h_pos j
  have hbh : 0 < M.b j + M.h j := by linarith
  have hβ0 : 0 < M.b j / (M.b j + M.h j) := div_pos hb hbh
  have hβ1 : M.b j / (M.b j + M.h j) < 1 := by rw [div_lt_one hbh]; linarith
  constructor
  · obtain ⟨S, hS⟩ := sp_cdf_large M j t _ hβ1
    obtain ⟨lb, hlb, hlb2⟩ := Int.exists_least_of_bdd
      (P := fun s => M.b j / (M.b j + M.h j) < M.demandCDF j t s)
      ⟨0, fun z hz => by
        by_contra hneg
        rw [sp_cdf_neg M j t z (by omega)] at hz; linarith⟩ ⟨S, hS⟩
    exact ⟨lb, hlb, hlb2⟩
  · intro s0 hs0
    set f := M.G j t
    have hup : ∀ S, s0 ≤ S → f S < f (S + 1) := by
      intro S hS
      have h1 : M.b j / (M.b j + M.h j) < M.demandCDF j t S :=
        lt_of_lt_of_le hs0.1 (sp_cdf_mono M j t hS)
      have h2 := sp_dG M j t S
      rw [div_lt_iff₀ hbh] at h1
      have : 0 < f (S + 1) - f S := by rw [h2]; nlinarith
      linarith
    have hdown : ∀ S, S < s0 → f (S + 1) ≤ f S := by
      intro S hS
      have h1 : ¬ (M.b j / (M.b j + M.h j) < M.demandCDF j t S) := fun h =>
        absurd (hs0.2 h) (by omega)
      push_neg at h1
      rw [le_div_iff₀ hbh] at h1
      have h2 := sp_dG M j t S
      have : f (S + 1) - f S ≤ 0 := by rw [h2]; nlinarith
      linarith
    have U := sp_up f s0 hup
    have D := sp_down f s0 hdown
    refine ⟨le_max_left _ _, ?_, ?_⟩
    · intro S hS
      rcases lt_trichotomy S (max (M.baseSupply j t) s0) with h | h | h
      · have hs : max (M.baseSupply j t) s0 = s0 := by
          rcases le_total (M.baseSupply j t) s0 with h' | h'
          · exact max_eq_right h'
          · rw [max_eq_left h'] at h ⊢; omega
        rw [hs] at h ⊢
        exact D S s0 h.le le_rfl
      · rw [h]
      · exact (U _ _ (le_max_right _ _) h).le
    · intro S _ hS
      by_contra hc
      push_neg at hc
      have := U _ _ (le_max_right _ _) hc
      linarith

end ServiceParts.RealTime

open ServiceParts.RealTime


theorem solution {J : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ItemModel J Ω P) (j : J) (t : ℕ) :
    (∃ s0 : ℤ, IsLeast {s : ℤ | M.b j / (M.b j + M.h j) < M.demandCDF j t s} s0) ∧
      ∀ s0 : ℤ, IsLeast {s : ℤ | M.b j / (M.b j + M.h j) < M.demandCDF j t s} s0 →
        M.IsLargestCNSolution j t (max (M.baseSupply j t) s0) := by
  exact sp_lcn_core M j t
