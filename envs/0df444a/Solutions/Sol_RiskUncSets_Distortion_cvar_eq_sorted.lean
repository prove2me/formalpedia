-- Prove2me | solution 1 for RiskUncSets.Distortion.cvar_eq_sorted
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T19:00:29.557268+00:00
-- url     : https://prove2.me/submissions/a7ac6713-aea3-4814-a789-96eee995a929

import Mathlib
import Definitions.Def_RiskUncSets_Distortion_Setting

open RiskUncSets.Distortion Finset MeasureTheory



/-- rearrangement: antitone weights, sorted (monotone) arrangement is maximal for `∑ q_i (-X_i)`. -/
theorem ru83_rearr {N : ℕ} (q X : Fin N → ℝ) (hq : Antitone q) (π σ : Equiv.Perm (Fin N))
    (hπ : Monotone (X ∘ π)) :
    ∑ i, q i * (-X (σ i)) ≤ ∑ i, q i * (-X (π i)) := by
  have hg : Antitone (fun i => -X (π i)) := fun a b hab => by
    have := hπ hab; simp only [Function.comp] at this; linarith
  have hmv : Monovary q (fun i => -X (π i)) := hq.monovary hg
  have := hmv.sum_mul_comp_perm_le_sum_mul (σ := σ.trans π.symm)
  simpa using this

theorem ru83_reindex {N : ℕ} (f h : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    ∑ i, f (σ i) * h i = ∑ j, f j * h (σ.symm j) := by
  rw [← Equiv.sum_comp σ.symm]; simp

theorem ru83_muQ_generates {N : ℕ} (q : Fin N → ℝ) (hq : q ∈ restrictedSimplex N) :
    Generates (Set.range fun σ : Equiv.Perm (Fin N) => q ∘ σ) (muQ q) := by
  obtain ⟨⟨hq0, hq1⟩, hqa⟩ := hq
  refine ⟨?_, fun X => ?_⟩
  · rintro _ ⟨σ, rfl⟩
    refine ⟨fun i => hq0 _, ?_⟩
    simp only [Function.comp]
    rw [Equiv.sum_comp σ q, hq1]
  · have hτ : Monotone (X ∘ Tuple.sort X) := Tuple.monotone_sort X
    have hS : muQ q X = ∑ i, q i * (-X (Tuple.sort X i)) := by
      simp [muQ, mul_neg, sum_neg_distrib]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
      simp only [Function.comp]
      rw [ru83_reindex q (fun i => -X i) σ, hS]
      exact ru83_rearr q X hqa _ _ hτ
    · intro b hb
      apply hb
      refine ⟨q ∘ (Tuple.sort X).symm, ⟨(Tuple.sort X).symm, rfl⟩, ?_⟩
      simp only [Function.comp]
      rw [ru83_reindex q (fun i => -X i) (Tuple.sort X).symm, hS]
      simp



theorem ru83_w_facts {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : α ∈ Set.Ioc (0 : ℝ) 1) :
    (∀ i, 0 ≤ cvarWeight N α i) ∧ (∀ i, cvarWeight N α i ≤ 1 / ((N : ℝ) * α)) ∧
      Antitone (cvarWeight N α) ∧ ∑ i, cvarWeight N α i = 1 := by
  obtain ⟨hα0, hα1⟩ := hα
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set a : ℝ := (N : ℝ) * α with ha
  have ha0 : 0 < a := mul_pos hNr hα0
  have haN : a ≤ N := by rw [ha]; nlinarith
  set k := ⌊a⌋₊ with hk
  have hka : (k : ℝ) ≤ a := Nat.floor_le ha0.le
  have hak : a < k + 1 := Nat.lt_floor_add_one a
  have hkN : k ≤ N := by
    have : (k : ℝ) ≤ N := hka.trans haN
    exact_mod_cast this
  have hc : 0 < 1 / a := by positivity
  have hr0 : 0 ≤ (a - k) / a := div_nonneg (by linarith) ha0.le
  have hr1 : (a - k) / a ≤ 1 / a := div_le_div_of_nonneg_right (by linarith) ha0.le
  have hw : ∀ i : Fin N, cvarWeight N α i =
      if (i : ℕ) + 1 ≤ k then 1 / a else if (i : ℕ) = k then (a - k) / a else 0 := fun i => rfl
  refine ⟨fun i => ?_, fun i => ?_, fun i j hij => ?_, ?_⟩
  · rw [hw]; split_ifs <;> linarith
  · rw [hw]; split_ifs <;> linarith
  · rw [hw, hw]
    have : (i : ℕ) ≤ j := hij
    split_ifs <;> first | linarith | omega
  · have hsum : ∑ i : Fin N, cvarWeight N α i = ∑ n ∈ range N,
        (if n + 1 ≤ k then 1 / a else if n = k then (a - k) / a else 0) :=
      Fin.sum_univ_eq_sum_range (fun n => if n + 1 ≤ k then 1 / a else if n = k then (a - k) / a else 0) N
    rw [hsum]
    have hfirst : ∀ m, m ≤ k → ∑ n ∈ range m,
        (if n + 1 ≤ k then 1 / a else if n = k then (a - k) / a else 0) = m * (1 / a) := by
      intro m hm
      rw [sum_congr rfl (g := fun _ => 1 / a)]
      · simp
      · intro n hn; rw [mem_range] at hn; rw [if_pos (by omega)]
    rcases Nat.lt_or_ge k N with hlt | hge
    · obtain ⟨d, hd⟩ : ∃ d, N = (k + 1) + d := ⟨N - (k+1), by omega⟩
      rw [hd, sum_range_add, sum_range_succ, hfirst k le_rfl]
      rw [sum_eq_zero (fun x _ => by rw [if_neg (by omega), if_neg (by omega)])]
      rw [if_neg (by omega), if_pos rfl]
      field_simp; ring
    · have hkN' : k = N := le_antisymm hkN hge
      rw [hfirst N (by omega)]
      have : a = N := le_antisymm haN (by rw [← hkN']; exact hka)
      rw [this]; field_simp



theorem ru83_cvar_lower {N : ℕ} (α : ℝ) (hα : 0 < α) (X q : Fin N → ℝ)
    (hq : q ∈ stdSimplex ℝ (Fin N)) (hqc : ∀ i, q i ≤ 1 / ((N : ℝ) * α)) (v : ℝ) :
    ∑ i, q i * (-X i) ≤ v + (1 / α) * ∑ i, uniform N i * max (-v - X i) 0 := by
  obtain ⟨hq0, hq1⟩ := hq
  have hc : 1 / ((N : ℝ) * α) = (1 / α) * (1 / (N : ℝ)) := by
    rw [mul_comm (N : ℝ) α]; field_simp
  have key : ∀ i, q i * (-X i) ≤ q i * v + (1 / α) * (uniform N i * max (-v - X i) 0) := by
    intro i
    have h1 : q i * (-X i - v) ≤ q i * max (-v - X i) 0 :=
      mul_le_mul_of_nonneg_left (by rw [le_max_iff]; left; linarith) (hq0 i)
    have h2 : q i * max (-v - X i) 0 ≤ (1 / α) * (1 / (N : ℝ)) * max (-v - X i) 0 :=
      mul_le_mul_of_nonneg_right (hc ▸ hqc i) (le_max_right _ _)
    simp only [uniform]
    nlinarith
  calc ∑ i, q i * (-X i) ≤ ∑ i, (q i * v + (1 / α) * (uniform N i * max (-v - X i) 0)) :=
        sum_le_sum fun i _ => key i
    _ = v + (1 / α) * ∑ i, uniform N i * max (-v - X i) 0 := by
        rw [sum_add_distrib, ← sum_mul, hq1, mul_sum]; ring

theorem ru83_cvar_main {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    (X : Fin N → ℝ) :
    IsLUB ((fun q : Fin N → ℝ => ∑ i, q i * (-X i)) ''
        {q | q ∈ stdSimplex ℝ (Fin N) ∧ ∀ i, q i ≤ 1 / ((N : ℝ) * α)})
        (cvar (uniform N) α X) ∧
      cvar (uniform N) α X = -∑ i, cvarWeight N α i * X (Tuple.sort X i) ∧
      cvarWeight N α ∈ restrictedSimplex N := by
  obtain ⟨hw0, hwc, hwa, hw1⟩ := ru83_w_facts hN α hα
  obtain ⟨hα0, hα1⟩ := hα
  set w := cvarWeight N α with hwdef
  set τ := Tuple.sort X with hτdef
  set S := -∑ i, w i * X (τ i) with hSdef
  set F : ℝ → ℝ := fun v => v + (1 / α) * ∑ i, uniform N i * max (-v - X i) 0 with hF
  have hcv : cvar (uniform N) α X = ⨅ v, F v := rfl
  -- q* attains S
  set qs : Fin N → ℝ := fun i => w (τ.symm i) with hqs
  have hqs_mem : qs ∈ {q | q ∈ stdSimplex ℝ (Fin N) ∧ ∀ i, q i ≤ 1 / ((N : ℝ) * α)} := by
    refine ⟨⟨fun i => hw0 _, ?_⟩, fun i => hwc _⟩
    simp only [hqs]; rw [Equiv.sum_comp τ.symm w, hw1]
  have hqs_val : ∑ i, qs i * (-X i) = S := by
    simp only [hqs]
    rw [ru83_reindex w (fun i => -X i) τ.symm]
    simp [hSdef, mul_neg, sum_neg_distrib]
  -- F v* = S
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set a : ℝ := (N : ℝ) * α with ha
  set k := ⌊a⌋₊ with hk
  have hmN : min k (N - 1) < N := by omega
  set m : Fin N := ⟨min k (N - 1), hmN⟩ with hm
  set Y : Fin N → ℝ := fun j => -X (τ j) with hY
  have hYa : Antitone Y := fun i j hij => by
    have := Tuple.monotone_sort X hij; simp only [Function.comp] at this
    simp only [hY]; linarith
  have hterm : ∀ j : Fin N, (1 / α) * (uniform N j * max (Y j - Y m) 0) = w j * (Y j - Y m) := by
    intro j
    have hwj : w j = if (j : ℕ) + 1 ≤ k then 1 / a else if (j : ℕ) = k then (a - k) / a else 0 := rfl
    have hc : (1 / α) * (1 / (N : ℝ)) = 1 / a := by rw [ha]; field_simp
    simp only [uniform]
    rcases lt_trichotomy j m with hjm | hjm | hjm
    · have hle : Y m ≤ Y j := hYa hjm.le
      have hjk : (j : ℕ) + 1 ≤ k := by
        have : (j : ℕ) < min k (N - 1) := hjm
        omega
      rw [hwj, if_pos hjk, max_eq_left (by linarith), ← hc]; ring
    · subst hjm; simp
    · have hle : Y j ≤ Y m := hYa hjm.le
      have hjk : k < (j : ℕ) := by
        have : min k (N - 1) < (j : ℕ) := hjm
        have : (j : ℕ) < N := j.2
        omega
      rw [hwj, if_neg (by omega), if_neg (by omega), max_eq_right (by linarith)]; ring
  have hFm : F (Y m) = S := by
    simp only [hF]
    have : ∀ i, -Y m - X i = Y (τ.symm i) - Y m := fun i => by simp [hY]; ring
    simp_rw [this]
    rw [mul_sum]
    rw [← Equiv.sum_comp τ (fun i => (1 / α) * (uniform N i * max (Y (τ.symm i) - Y m) 0))]
    have h2 : ∀ j, (1 / α) * (uniform N (τ j) * max (Y (τ.symm (τ j)) - Y m) 0)
        = w j * (Y j - Y m) := fun j => by
      rw [Equiv.symm_apply_apply]; simpa [uniform] using hterm j
    simp_rw [h2]
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hw1, hSdef, hY, mul_neg, sum_neg_distrib]
    ring
  have hlow : ∀ v, S ≤ F v := fun v => by
    rw [← hqs_val]; exact ru83_cvar_lower α hα0 X qs hqs_mem.1 hqs_mem.2 v
  have hbdd : BddBelow (Set.range F) := ⟨S, by rintro _ ⟨v, rfl⟩; exact hlow v⟩
  have hcvS : cvar (uniform N) α X = S := by
    rw [hcv]
    exact le_antisymm (hFm ▸ ciInf_le hbdd (Y m)) (le_ciInf hlow)
  refine ⟨?_, hcvS, ⟨⟨hw0, hw1⟩, hwa⟩⟩
  rw [hcvS]
  refine IsGreatest.isLUB ⟨⟨qs, hqs_mem, hqs_val⟩, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  rw [← hFm]
  exact ru83_cvar_lower α hα0 X q hq.1 hq.2 _


theorem solution {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    (X : Fin N → ℝ) :
    IsLUB ((fun q : Fin N → ℝ => ∑ i, q i * (-X i)) ''
        {q | q ∈ stdSimplex ℝ (Fin N) ∧ ∀ i, q i ≤ 1 / ((N : ℝ) * α)})
        (cvar (uniform N) α X) ∧
      cvar (uniform N) α X = -∑ i, cvarWeight N α i * X (Tuple.sort X i) ∧
      cvarWeight N α ∈ restrictedSimplex N := by


  exact ru83_cvar_main hN α hα X
