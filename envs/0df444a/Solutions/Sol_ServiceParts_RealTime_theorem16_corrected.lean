-- Prove2me | solution 1 for ServiceParts.RealTime.theorem16_corrected
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T09:45:50.80741+00:00
-- url     : https://prove2.me/submissions/844812c7-2c64-455f-8a00-3fe8648592b0

import Mathlib
import Definitions.Def_ServiceParts_RealTime_Model
import Definitions.Def_ServiceParts_RealTime_ESAM

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


lemma sp_unique (M : ItemModel J Ω P) (j : J) (t : ℕ) (s s' : ℤ)
    (hs : M.IsLargestCNSolution j t s) (hs' : M.IsLargestCNSolution j t s') : s = s' := by
  have h1 := hs.2.2 s' hs'.1 (hs'.2.1 s hs.1)
  have h2 := hs'.2.2 s hs.1 (hs.2.1 s' hs'.1)
  omega

lemma sp_eq_max [IsProbabilityMeasure P] (M : ItemModel J Ω P) (j : J) (t : ℕ) (s : ℤ)
    (hs : M.IsLargestCNSolution j t s) :
    ∃ s0, IsLeast {s : ℤ | M.b j / (M.b j + M.h j) < M.demandCDF j t s} s0 ∧
      s = max (M.baseSupply j t) s0 := by
  obtain ⟨⟨s0, hs0⟩, h⟩ := sp_lcn_core M j t
  exact ⟨s0, hs0, sp_unique M j t _ _ hs (h s0 hs0)⟩

theorem sp_mono_core [IsProbabilityMeasure P] (M : ItemModel J Ω P) (j : J) (t : ℕ)
    (ht₁ : M.Tr j ≤ t) (s s' : ℤ)
    (hs : M.IsLargestCNSolution j (t - 1) s) (hs' : M.IsLargestCNSolution j t s') :
    s ≤ s' := by
  obtain ⟨a, ha, rfl⟩ := sp_eq_max M j _ s hs
  obtain ⟨a', ha', rfl⟩ := sp_eq_max M j _ s' hs'
  have hL : M.baseSupply j (t - 1) = M.baseSupply j t := by
    rw [M.baseSupply_const j t ht₁]
    rcases Nat.lt_or_ge (t - 1) (M.Tr j) with h | h
    · have : t - 1 = M.Tr j - 1 := by omega
      rw [this]
    · exact M.baseSupply_const j _ h
  have hcdf : M.demandCDF j t a' ≤ M.demandCDF j (t - 1) a' := by
    unfold ItemModel.demandCDF
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro ω h
    simp only [Set.mem_setOf_eq] at *
    have := M.X_mono j ω (Nat.sub_le t 1)
    simp only at this
    omega
  have : a ≤ a' := ha.2 (lt_of_lt_of_le ha'.1 hcdf)
  rw [hL]
  exact max_le_max le_rfl this


lemma sp_Q_mono [IsProbabilityMeasure P] (M : ItemModel J Ω P) (j : J) (S S' : ℤ)
    (h : S ≤ S') : M.Q j S ≤ M.Q j S' := by
  unfold ItemModel.Q
  apply mul_le_mul_of_nonneg_left _ (M.h_pos j).le
  apply Summable.tsum_le_tsum _ (M.Q_summable j S) (M.Q_summable j S')
  intro n
  apply integral_mono (sp_int1 M j _ S) (sp_int1 M j _ S')
  intro ω
  have : (S : ℝ) ≤ (S' : ℝ) := by exact_mod_cast h
  simp only
  exact max_le_max (by linarith) le_rfl

lemma sp_up_step [IsProbabilityMeasure P] (M : ItemModel J Ω P) (j : J) (t : ℕ) (s0 : ℤ)
    (hs0 : IsLeast {s : ℤ | M.b j / (M.b j + M.h j) < M.demandCDF j t s} s0)
    (S : ℤ) (hS : s0 ≤ S) : M.G j t S < M.G j t (S + 1) := by
  have hb := M.b_pos j
  have hh := M.h_pos j
  have hbh : 0 < M.b j + M.h j := by linarith
  have h1 : M.b j / (M.b j + M.h j) < M.demandCDF j t S :=
    lt_of_lt_of_le hs0.1 (sp_cdf_mono M j t hS)
  have h2 := sp_dG M j t S
  rw [div_lt_iff₀ hbh] at h1
  have : 0 < M.G j t (S + 1) - M.G j t S := by rw [h2]; nlinarith
  linarith

lemma sp_G_drop [IsProbabilityMeasure P] (M : ItemModel J Ω P) (j : J) (k : ℕ) (s : ℤ)
    (hs : M.IsLargestCNSolution j k s) (S : ℤ) (hS : s < S) :
    M.G j k (S - 1) < M.G j k S := by
  obtain ⟨s0, hs0, rfl⟩ := sp_eq_max M j k s hs
  have := sp_up_step M j k s0 hs0 (S - 1) (by have := le_max_right (M.baseSupply j k) s0; omega)
  simpa using this

def dly (f : ℕ → ℕ) (m : ℕ) : ℕ → ℕ := fun i =>
  if i = m then f i - 1 else if i = m + 1 then f i + 1 else f i

def bmp (f : ℕ → ℕ) (m : ℕ) : ℕ → ℕ := fun i => if i = m then f i + 1 else f i

lemma cum_dly (f : ℕ → ℕ) (m : ℕ) (hm : 1 ≤ f m) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (dly f m i : ℤ) = ∑ i ∈ Finset.range (n + 1), (f i : ℤ)
      - (if m ≤ n then 1 else 0) + (if m + 1 ≤ n then 1 else 0) := by
  have hp : ∀ i, (dly f m i : ℤ) = (f i : ℤ) - (if i = m then 1 else 0)
      + (if i = m + 1 then 1 else 0) := by
    intro i; unfold dly
    split_ifs with h1 h2 <;> (try subst h1) <;> push_cast <;> omega
  simp only [hp, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_range]
  split_ifs <;> omega

lemma cum_bmp (f : ℕ → ℕ) (m : ℕ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (bmp f m i : ℤ) = ∑ i ∈ Finset.range (n + 1), (f i : ℤ)
      + (if m ≤ n then 1 else 0) := by
  have hp : ∀ i, (bmp f m i : ℤ) = (f i : ℤ) + (if i = m then 1 else 0) := by
    intro i; unfold bmp
    split_ifs with h1 <;> push_cast <;> omega
  simp only [hp, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs <;> omega

lemma sp_cost (e : ℝ) (f : ℕ → ℕ) (N : ℕ) :
    ∑ i ∈ Finset.range N, e * (f i : ℝ) = e * (((∑ i ∈ Finset.range N, (f i : ℤ)) : ℤ) : ℝ) := by
  push_cast; rw [Finset.mul_sum]

section
variable {J : Type*} [Fintype J] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]

lemma sp_improve (M : ItemModel J Ω P) (Shat : J → ℕ → ℤ)
    (hShat : ∀ j k, M.Te j ≤ k → k ≤ M.Tr j + M.T0 → M.IsLargestCNSolution j k (Shat j k))
    (yr ye : J → ℕ → ℕ) (hy : IsESAMOptimal M yr ye) (j : J) (k1 : ℕ)
    (hk1 : M.Te j ≤ k1) (hk2 : k1 ≤ M.Tr j + M.T0)
    (hgt : Shat j k1 < esamStock M yr ye j k1) (yr' ye' : J → ℕ → ℕ)
    (hf : ESAMFeasible M yr' ye') (ho : ∀ j', j' ≠ j → yr' j' = yr j' ∧ ye' j' = ye j')
    (hk : ∀ k, M.Te j ≤ k → k ≤ M.Tr j + M.T0 → k ≠ k1 →
      esamStock M yr' ye' j k = esamStock M yr ye j k)
    (h1 : esamStock M yr' ye' j k1 = esamStock M yr ye j k1 - 1)
    (hc : ∑ t ∈ Finset.range (M.T0 + 1), M.e j * (ye' j t : ℝ) ≤
      ∑ t ∈ Finset.range (M.T0 + 1), M.e j * (ye j t : ℝ)) : False := by
  have hGle : ∀ k ∈ Finset.Icc (M.Te j) (M.Tr j + M.T0),
      M.G j k (esamStock M yr' ye' j k) ≤ M.G j k (esamStock M yr ye j k) := by
    intro k hk'
    rw [Finset.mem_Icc] at hk'
    by_cases hkk : k = k1
    · subst hkk; rw [h1]; exact (sp_G_drop M j k _ (hShat j k hk1 hk2) _ hgt).le
    · rw [hk k hk'.1 hk'.2 hkk]
  have hQ : M.Q j (esamStock M yr' ye' j (M.Tr j + M.T0)) ≤
      M.Q j (esamStock M yr ye j (M.Tr j + M.T0)) := by
    apply sp_Q_mono
    by_cases hkk : M.Tr j + M.T0 = k1
    · rw [hkk, h1]; omega
    · rw [hk _ (by have := M.Te_lt_Tr j; omega) le_rfl hkk]
  have hlt : esamObjective M yr' ye' < esamObjective M yr ye := by
    unfold esamObjective
    apply Finset.sum_lt_sum
    · intro j' _
      by_cases hj : j' = j
      · subst hj
        exact add_le_add (add_le_add (Finset.sum_le_sum hGle) hQ) hc
      · obtain ⟨a, b⟩ := ho j' hj
        have : esamStock M yr' ye' j' = esamStock M yr ye j' := by
          funext k; unfold esamStock; rw [a, b]
        rw [this, b]
    · refine ⟨j, Finset.mem_univ _, ?_⟩
      apply add_lt_add_of_lt_of_le _ hc
      apply add_lt_add_of_lt_of_le _ hQ
      apply Finset.sum_lt_sum hGle
      refine ⟨k1, Finset.mem_Icc.mpr ⟨hk1, hk2⟩, ?_⟩
      rw [h1]; exact sp_G_drop M j k1 _ (hShat j k1 hk1 hk2) _ hgt
  have := hy.2 yr' ye' hf
  linarith

lemma sp_caseR (M : ItemModel J Ω P) (Shat : J → ℕ → ℤ)
    (hShat : ∀ j k, M.Te j ≤ k → k ≤ M.Tr j + M.T0 → M.IsLargestCNSolution j k (Shat j k))
    (yr ye : J → ℕ → ℕ) (hy : IsESAMOptimal M yr ye) (j : J) (t : ℕ)
    (ht₁ : M.Te j ≤ t) (ht₂ : t ≤ M.Tr j + M.T0) (hTr : M.Tr j ≤ t)
    (hpos : 1 ≤ yr j (t - M.Tr j)) (hgt : Shat j t < esamStock M yr ye j t) : False := by
  classical
  set m := t - M.Tr j with hm
  set yr' : J → ℕ → ℕ := fun j' => if j' = j then dly (yr j') m else yr j' with hyr'
  have hYj : yr' j = dly (yr j) m := by simp [hyr']
  have hYo : ∀ j', j' ≠ j → yr' j' = yr j' := fun j' h => by simp [hyr', h]
  apply sp_improve M Shat hShat yr ye hy j t ht₁ ht₂ hgt yr' ye
  · intro s hs
    refine le_trans ?_ (hy.1 s hs)
    apply Finset.sum_le_sum
    intro j' _
    by_cases hj : j' = j
    · subst hj
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hYj, cum_dly _ _ hpos]
      split_ifs <;> omega
    · rw [hYo j' hj]
  · intro j' hj; exact ⟨hYo j' hj, rfl⟩
  · intro k _ _ hkt
    unfold esamStock
    rw [hYj]
    split_ifs with hk
    · rfl
    · rw [cum_dly _ _ hpos]; split_ifs <;> omega
  · unfold esamStock
    rw [hYj, if_neg (by omega), cum_dly _ _ hpos]
    split_ifs <;> omega
  · exact le_rfl

lemma sp_caseE (M : ItemModel J Ω P) (Shat : J → ℕ → ℤ)
    (hShat : ∀ j k, M.Te j ≤ k → k ≤ M.Tr j + M.T0 → M.IsLargestCNSolution j k (Shat j k))
    (yr ye : J → ℕ → ℕ) (hy : IsESAMOptimal M yr ye) (j : J) (t : ℕ)
    (ht₁ : M.Te j ≤ t) (ht₂ : t ≤ M.Tr j + M.T0) (hlt : t - M.Te j < M.T0)
    (hpos : 1 ≤ ye j (t - M.Te j)) (hgt : Shat j t < esamStock M yr ye j t) : False := by
  classical
  set m := t - M.Te j with hm
  set ye' : J → ℕ → ℕ := fun j' => if j' = j then dly (ye j') m else ye j' with hye'
  have hYj : ye' j = dly (ye j) m := by simp [hye']
  have hYo : ∀ j', j' ≠ j → ye' j' = ye j' := fun j' h => by simp [hye', h]
  apply sp_improve M Shat hShat yr ye hy j t ht₁ ht₂ hgt yr ye'
  · intro s hs
    refine le_trans ?_ (hy.1 s hs)
    apply Finset.sum_le_sum
    intro j' _
    by_cases hj : j' = j
    · subst hj
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hYj, cum_dly _ _ hpos]
      split_ifs <;> omega
    · rw [hYo j' hj]
  · intro j' hj; exact ⟨rfl, hYo j' hj⟩
  · intro k _ _ hkt
    unfold esamStock
    rw [hYj]
    split_ifs with hk
    · rw [cum_dly _ _ hpos]; split_ifs <;> omega
    · rw [cum_dly _ _ hpos]; split_ifs <;> omega
  · unfold esamStock
    rw [hYj]
    split_ifs with hk
    · rw [cum_dly _ _ hpos]; split_ifs <;> omega
    · rw [cum_dly _ _ hpos]; split_ifs <;> omega
  · rw [hYj, sp_cost, sp_cost, cum_dly _ _ hpos]
    apply le_of_eq
    congr 2
    split_ifs <;> omega

lemma sp_caseC (M : ItemModel J Ω P) (Shat : J → ℕ → ℤ)
    (hShat : ∀ j k, M.Te j ≤ k → k ≤ M.Tr j + M.T0 → M.IsLargestCNSolution j k (Shat j k))
    (yr ye : J → ℕ → ℕ) (hy : IsESAMOptimal M yr ye) (j : J) (t : ℕ)
    (ht : t = M.Te j + M.T0) (hTr : M.Tr j = M.Te j + 1)
    (hpos : 1 ≤ ye j M.T0) (hgt : Shat j t < esamStock M yr ye j t) : False := by
  classical
  set ye' : J → ℕ → ℕ := fun j' => if j' = j then dly (ye j') M.T0 else ye j' with hye'
  have hYj : ye' j = dly (ye j) M.T0 := by simp [hye']
  have hYo : ∀ j', j' ≠ j → ye' j' = ye j' := fun j' h => by simp [hye', h]
  set yr' : J → ℕ → ℕ := fun j' => if j' = j then bmp (yr j') M.T0 else yr j' with hyr'
  have hRj : yr' j = bmp (yr j) M.T0 := by simp [hyr']
  have hRo : ∀ j', j' ≠ j → yr' j' = yr j' := fun j' h => by simp [hyr', h]
  apply sp_improve M Shat hShat yr ye hy j t (by omega) (by omega) hgt yr' ye'
  · intro s hs
    refine le_trans ?_ (hy.1 s hs)
    apply Finset.sum_le_sum
    intro j' _
    by_cases hj : j' = j
    · subst hj
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hYj, hRj, cum_dly _ _ hpos, cum_bmp]
      split_ifs <;> omega
    · rw [hYo j' hj, hRo j' hj]
  · intro j' hj; exact ⟨hRo j' hj, hYo j' hj⟩
  · intro k _ _ hkt
    unfold esamStock
    rw [hYj, hRj]
    split_ifs with hk
    · rw [cum_dly _ _ hpos]; split_ifs <;> omega
    · rw [cum_dly _ _ hpos, cum_bmp]; split_ifs <;> omega
  · unfold esamStock
    rw [hYj, hRj]
    split_ifs with hk
    · rw [cum_dly _ _ hpos]; split_ifs <;> omega
    · rw [cum_dly _ _ hpos, cum_bmp]; split_ifs <;> omega
  · rw [hYj, sp_cost, sp_cost, cum_dly _ _ hpos]
    rw [if_pos le_rfl, if_neg (by omega)]
    have := M.e_nonneg j
    push_cast
    nlinarith

end

section
variable {J : Type*} [Fintype J] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]

lemma sp_step (M : ItemModel J Ω P) (Shat : J → ℕ → ℤ)
    (hShat : ∀ j k, M.Te j ≤ k → k ≤ M.Tr j + M.T0 → M.IsLargestCNSolution j k (Shat j k))
    (yr ye : J → ℕ → ℕ) (hy : IsESAMOptimal M yr ye) (j : J) (t : ℕ)
    (ht₁ : M.Te j ≤ t) (ht₂ : t ≤ M.Tr j + M.T0)
    (hprov : M.Tr j = M.Te j + 1 ∨ t < M.Te j + M.T0)
    (hgt : Shat j t < esamStock M yr ye j t) :
    M.Te j < t ∧ esamStock M yr ye j t - M.baseSupply j t =
      esamStock M yr ye j (t - 1) - M.baseSupply j (t - 1) := by
  have hTeTr := M.Te_lt_Tr j
  by_cases a1 : M.Tr j ≤ t ∧ 1 ≤ yr j (t - M.Tr j)
  · exact (sp_caseR M Shat hShat yr ye hy j t ht₁ ht₂ a1.1 a1.2 hgt).elim
  by_cases a2 : t - M.Te j ≤ M.T0 ∧ 1 ≤ ye j (t - M.Te j)
  · rcases Nat.lt_or_ge (t - M.Te j) M.T0 with h | h
    · exact (sp_caseE M Shat hShat yr ye hy j t ht₁ ht₂ h a2.2 hgt).elim
    · have ht : t = M.Te j + M.T0 := by omega
      have hTr : M.Tr j = M.Te j + 1 := by rcases hprov with h' | h' <;> omega
      have hp : 1 ≤ ye j M.T0 := by
        have := a2.2; rwa [show t - M.Te j = M.T0 by omega] at this
      exact (sp_caseC M Shat hShat yr ye hy j t ht hTr hp hgt).elim
  have hyr0 : M.Tr j ≤ t → yr j (t - M.Tr j) = 0 := by
    intro h; by_contra hc; exact a1 ⟨h, by omega⟩
  have hye0 : t - M.Te j ≤ M.T0 → ye j (t - M.Te j) = 0 := by
    intro h; by_contra hc; exact a2 ⟨h, by omega⟩
  rcases eq_or_lt_of_le ht₁ with h | h
  · exfalso
    subst h
    have hL := (hShat j (M.Te j) le_rfl ht₂).1
    have : esamStock M yr ye j (M.Te j) = M.baseSupply j (M.Te j) := by
      unfold esamStock
      rw [if_pos hTeTr]
      have := hye0 (by omega)
      rw [Nat.sub_self] at this
      simp only [Nat.sub_self, Nat.zero_min, zero_add, Finset.sum_range_one]
      rw [this]; simp
    omega
  refine ⟨h, ?_⟩
  have hE : ∑ t' ∈ Finset.range (min (t - M.Te j) M.T0 + 1), (ye j t' : ℤ) =
      ∑ t' ∈ Finset.range (min (t - 1 - M.Te j) M.T0 + 1), (ye j t' : ℤ) := by
    by_cases hc : t - M.Te j ≤ M.T0
    · rw [show min (t - M.Te j) M.T0 + 1 = (min (t - 1 - M.Te j) M.T0 + 1) + 1 by omega,
        Finset.sum_range_succ, show min (t - 1 - M.Te j) M.T0 + 1 = t - M.Te j by omega,
        hye0 hc]
      simp
    · rw [show min (t - M.Te j) M.T0 = min (t - 1 - M.Te j) M.T0 by omega]
  unfold esamStock
  by_cases c1 : t < M.Tr j
  · rw [if_pos c1, if_pos (by omega), hE]; ring
  rw [if_neg c1, hE, M.baseSupply_const j t (by omega)]
  by_cases c2 : t - 1 < M.Tr j
  · rw [if_pos c2]
    have e1 : t - M.Tr j = 0 := by omega
    have e2 : t - 1 = M.Tr j - 1 := by omega
    have := hyr0 (by omega)
    rw [e1] at this ⊢
    rw [e2]
    simp [this]
  · rw [if_neg c2, M.baseSupply_const j (t - 1) (by omega),
      show t - M.Tr j + 1 = (t - 1 - M.Tr j + 1) + 1 by omega, Finset.sum_range_succ,
      show t - 1 - M.Tr j + 1 = t - M.Tr j by omega, hyr0 (by omega)]
    simp

theorem sp_t16_core (M : ItemModel J Ω P) (Shat : J → ℕ → ℤ)
    (hShat : ∀ j k, M.Te j ≤ k → k ≤ M.Tr j + M.T0 → M.IsLargestCNSolution j k (Shat j k))
    (yr ye : J → ℕ → ℕ) (hy : IsESAMOptimal M yr ye) (j : J) (t : ℕ)
    (ht₁ : M.Te j ≤ t) (ht₂ : t ≤ M.Tr j + M.T0) :
    M.baseSupply j t ≤ esamStock M yr ye j t ∧
      (M.Tr j = M.Te j + 1 ∨ t < M.Te j + M.T0 →
        esamStock M yr ye j t ≤ M.baseSupply j t +
          (Finset.Icc (M.Te j) t).sup' ⟨M.Te j, Finset.left_mem_Icc.mpr ht₁⟩
            (fun k => Shat j k - M.baseSupply j k)) := by
  constructor
  · unfold esamStock
    have h1 : (0 : ℤ) ≤ ∑ t' ∈ Finset.range (min (t - M.Te j) M.T0 + 1), (ye j t' : ℤ) :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    have h2 : (0 : ℤ) ≤ ∑ t' ∈ Finset.range (t - M.Tr j + 1), (yr j t' : ℤ) :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    split_ifs with h
    · linarith
    · rw [M.baseSupply_const j t (by omega)]; linarith
  intro hprov
  have key : ∀ n : ℕ, M.Te j + n ≤ M.Tr j + M.T0 →
      (M.Tr j = M.Te j + 1 ∨ M.Te j + n < M.Te j + M.T0) →
      ∃ k, M.Te j ≤ k ∧ k ≤ M.Te j + n ∧
        esamStock M yr ye j (M.Te j + n) - M.baseSupply j (M.Te j + n) ≤
          Shat j k - M.baseSupply j k := by
    intro n
    induction n with
    | zero =>
      intro h1 h2
      refine ⟨M.Te j, le_rfl, by omega, ?_⟩
      by_contra hc
      push_neg at hc
      have := sp_step M Shat hShat yr ye hy j (M.Te j + 0) (by omega) h1 h2 (by simp at hc ⊢; linarith)
      omega
    | succ n ih =>
      intro h1 h2
      by_cases hc : esamStock M yr ye j (M.Te j + (n + 1)) - M.baseSupply j (M.Te j + (n + 1)) ≤
          Shat j (M.Te j + (n + 1)) - M.baseSupply j (M.Te j + (n + 1))
      · exact ⟨_, by omega, le_rfl, hc⟩
      push_neg at hc
      obtain ⟨_, hx⟩ := sp_step M Shat hShat yr ye hy j (M.Te j + (n + 1)) (by omega) h1 h2
        (by linarith)
      obtain ⟨k, hk1, hk2, hk3⟩ := ih (by omega) (by omega)
      refine ⟨k, hk1, by omega, ?_⟩
      rw [hx, show M.Te j + (n + 1) - 1 = M.Te j + n by omega]
      exact hk3
  obtain ⟨k, hk1, hk2, hk3⟩ := key (t - M.Te j) (by omega) (by omega)
  rw [show M.Te j + (t - M.Te j) = t by omega] at hk3 hk2
  have := Finset.le_sup' (fun k => Shat j k - M.baseSupply j k)
    (Finset.mem_Icc.mpr ⟨hk1, hk2⟩)
  linarith

end

end ServiceParts.RealTime

open ServiceParts.RealTime


theorem solution {J : Type*} [Fintype J] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (M : ItemModel J Ω P) (Shat : J → ℕ → ℤ)
    (hShat : ∀ j k, M.Te j ≤ k → k ≤ M.Tr j + M.T0 → M.IsLargestCNSolution j k (Shat j k))
    (yr ye : J → ℕ → ℕ) (hy : IsESAMOptimal M yr ye) (j : J) (t : ℕ)
    (ht₁ : M.Te j ≤ t) (ht₂ : t ≤ M.Tr j + M.T0) :
    M.baseSupply j t ≤ esamStock M yr ye j t ∧
      (M.Tr j = M.Te j + 1 ∨ t < M.Te j + M.T0 →
        esamStock M yr ye j t ≤ M.baseSupply j t +
          (Finset.Icc (M.Te j) t).sup' ⟨M.Te j, Finset.left_mem_Icc.mpr ht₁⟩
            (fun k => Shat j k - M.baseSupply j k)) := by
  exact sp_t16_core M Shat hShat yr ye hy j t ht₁ ht₂
