-- Prove2me | solution 1 for ServiceParts.RealTime.theorem15
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T09:40:20.80799+00:00
-- url     : https://prove2.me/submissions/494b665d-ca63-4ab3-9097-70bc6fac9331

import Mathlib
import Definitions.Def_ServiceParts_RealTime_Model
import Definitions.Def_ServiceParts_RealTime_SAM

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


def spY (D : ℕ → ℤ) : ℕ → ℕ
  | 0 => (D 0).toNat
  | (m + 1) => (D (m + 1) - D m).toNat

lemma sp_tele (D : ℕ → ℤ) (hD : Monotone D) (h0 : 0 ≤ D 0) (m : ℕ) :
    ∑ t' ∈ Finset.range (m + 1), (spY D t' : ℤ) = D m := by
  induction m with
  | zero => simp [spY, Int.toNat_of_nonneg h0]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [spY]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr (hD (Nat.le_succ m)))]
    ring

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

theorem sp_t15_core {J : Type*} [Fintype J] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ItemModel J Ω P) (Shat : J → ℕ → ℤ)
    (hShat : ∀ j k, M.Tr j ≤ k → k ≤ M.Tr j + M.T0 → M.IsLargestCNSolution j k (Shat j k))
    (y : J → ℕ → ℕ) (hy : IsSAMOptimal M y) (j : J) (t : ℕ)
    (ht₁ : M.Tr j ≤ t) (ht₂ : t ≤ M.Tr j + M.T0) :
    M.baseSupply j (M.Tr j - 1) ≤ samStock M y j t ∧ samStock M y j t ≤ Shat j t := by
  classical
  constructor
  · unfold samStock
    have : (0 : ℤ) ≤ ∑ t' ∈ Finset.range (t - M.Tr j + 1), (y j t' : ℤ) :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    linarith
  by_contra hcon
  push_neg at hcon
  set L := M.baseSupply j (M.Tr j - 1) with hLdef
  have hbsk : ∀ k, M.Tr j ≤ k → M.baseSupply j k = L := fun k hk => M.baseSupply_const j k hk
  have hLS : ∀ k, M.Tr j ≤ k → k ≤ M.Tr j + M.T0 → L ≤ Shat j k := by
    intro k h1 h2; rw [← hbsk k h1]; exact (hShat j k h1 h2).1
  set g : ℕ → ℤ := fun m => Shat j (M.Tr j + min m M.T0) - L with hg
  have hg0 : ∀ m, 0 ≤ g m := by
    intro m; simp only [hg]
    have := hLS (M.Tr j + min m M.T0) (by omega) (by omega); linarith
  have hgm : Monotone g := by
    apply monotone_nat_of_le_succ
    intro m
    simp only [hg]
    rcases Nat.lt_or_ge m M.T0 with h | h
    · rw [min_eq_left h.le, min_eq_left (show m + 1 ≤ M.T0 by omega)]
      have := sp_mono_core M j (M.Tr j + (m + 1)) (by omega) _ _
        (by
          have e : M.Tr j + (m + 1) - 1 = M.Tr j + m := by omega
          rw [e]; exact hShat j _ (by omega) (by omega))
        (hShat j _ (by omega) (by omega))
      have e2 : M.Tr j + m + 1 = M.Tr j + (m + 1) := by omega
      linarith
    · rw [min_eq_right h, min_eq_right (show M.T0 ≤ m + 1 by omega)]
  set C : ℕ → ℤ := fun m => ∑ t' ∈ Finset.range (m + 1), (y j t' : ℤ) with hC
  have hC0 : ∀ m, 0 ≤ C m := fun m => Finset.sum_nonneg (fun _ _ => by positivity)
  have hCm : Monotone C := by
    intro a b hab
    simp only [hC]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
    intro _ _ _; positivity
  set D : ℕ → ℤ := fun m => min (C m) (g m) with hD
  have hDm : Monotone D := fun a b hab => min_le_min (hCm hab) (hgm hab)
  have hD0 : 0 ≤ D 0 := le_min (hC0 0) (hg0 0)
  set Y := Function.update y j (spY D) with hY
  have hYj : Y j = spY D := by simp [hY]
  have hYo : ∀ j', j' ≠ j → Y j' = y j' := fun j' h => by simp [hY, h]
  have hsumY : ∀ m, ∑ t' ∈ Finset.range (m + 1), (Y j t' : ℤ) = D m := by
    intro m; rw [hYj]; exact sp_tele D hDm hD0 m
  -- feasibility
  have hfeas : SAMFeasible M Y := by
    intro s hs
    refine le_trans ?_ (hy.1 s hs)
    apply Finset.sum_le_sum
    intro j' _
    by_cases hj : j' = j
    · subst hj; rw [hsumY]; exact min_le_left _ _
    · rw [hYo j' hj]
  -- stocks
  have hstockY : ∀ k, M.Tr j ≤ k → k ≤ M.Tr j + M.T0 →
      samStock M Y j k = min (samStock M y j k) (Shat j k) := by
    intro k h1 h2
    unfold samStock
    rw [hsumY]
    simp only [hD, hC, hg]
    rw [min_eq_left (show k - M.Tr j ≤ M.T0 by omega),
      show M.Tr j + (k - M.Tr j) = k by omega]
    rw [← hLdef]
    rcases le_total (∑ t' ∈ Finset.range (k - M.Tr j + 1), (y j t' : ℤ)) (Shat j k - L) with h | h
    · rw [min_eq_left h, min_eq_left (by linarith)]
    · rw [min_eq_right h, min_eq_right (by linarith)]; ring
  have hGle : ∀ k, M.Tr j ≤ k → k ≤ M.Tr j + M.T0 →
      M.G j k (samStock M Y j k) ≤ M.G j k (samStock M y j k) := by
    intro k h1 h2
    rw [hstockY k h1 h2]
    rcases le_total (samStock M y j k) (Shat j k) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h]
      apply (hShat j k h1 h2).2.1
      rw [hbsk k h1]
      exact le_trans (hLS k h1 h2) h
  have hGlt : M.G j t (samStock M Y j t) < M.G j t (samStock M y j t) := by
    rw [hstockY t ht₁ ht₂, min_eq_right hcon.le]
    by_contra hc
    push_neg at hc
    have := (hShat j t ht₁ ht₂).2.2 (samStock M y j t)
      (by rw [hbsk t ht₁]; exact le_trans (hLS t ht₁ ht₂) hcon.le) hc
    omega
  have hQ : M.Q j (samStock M Y j (M.Tr j + M.T0)) ≤ M.Q j (samStock M y j (M.Tr j + M.T0)) := by
    apply sp_Q_mono
    rw [hstockY _ (by omega) le_rfl]; exact min_le_left _ _
  have hlt : samObjective M Y < samObjective M y := by
    unfold samObjective
    apply Finset.sum_lt_sum
    · intro j' _
      by_cases hj : j' = j
      · subst hj
        apply add_le_add _ hQ
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_Icc] at hk
        exact hGle k hk.1 hk.2
      · have : samStock M Y j' = samStock M y j' := by
          funext k; unfold samStock; rw [hYo j' hj]
        rw [this]
    · refine ⟨j, Finset.mem_univ _, ?_⟩
      apply add_lt_add_of_lt_of_le _ hQ
      apply Finset.sum_lt_sum
      · intro k hk
        rw [Finset.mem_Icc] at hk
        exact hGle k hk.1 hk.2
      · exact ⟨t, Finset.mem_Icc.mpr ⟨ht₁, ht₂⟩, hGlt⟩
  have := hy.2 Y hfeas
  linarith

end ServiceParts.RealTime

open ServiceParts.RealTime


theorem solution {J : Type*} [Fintype J] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ItemModel J Ω P) (Shat : J → ℕ → ℤ)
    (hShat : ∀ j k, M.Tr j ≤ k → k ≤ M.Tr j + M.T0 → M.IsLargestCNSolution j k (Shat j k))
    (y : J → ℕ → ℕ) (hy : IsSAMOptimal M y) (j : J) (t : ℕ)
    (ht₁ : M.Tr j ≤ t) (ht₂ : t ≤ M.Tr j + M.T0) :
    M.baseSupply j (M.Tr j - 1) ≤ samStock M y j t ∧ samStock M y j t ≤ Shat j t := by
  exact sp_t15_core M Shat hShat y hy j t ht₁ ht₂
