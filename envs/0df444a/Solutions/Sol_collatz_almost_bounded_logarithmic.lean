-- Prove2me | solution 1 for collatz_almost_bounded_logarithmic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-09T05:09:57.685182+00:00
-- url     : https://prove2.me/submissions/0720cb4f-6ff3-4178-809e-a2317607661c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna.
-/

import Mathlib
import Definitions.Def_weightedLogMass
import Definitions.Def_weightedLogMassReal
import Definitions.Def_collatzStepMap
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_almost_bounded_logarithmic
import Theorems.Thm_collatz_reaches_syracuse_iterate

open scoped BigOperators
open scoped Topology
open Filter
open Classical

noncomputable section

/-!
# Standalone Tao 1.3 logarithmic-density consumer

All proof components are inlined in dependency order.  The full Syracuse
1.6 statement is consumed from its published mirror; no local Solutions
module is imported and no new axiom is introduced here.
-/

theorem platform_odd_harmonic_sum_eq (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      if 0 < k ∧ Odd k then 1 / (k : ℝ) else 0) =
      (harmonic n : ℝ) - (1 / 2 : ℝ) * (harmonic (n / 2) : ℝ) := by
  induction n with
  | zero => simp [harmonic]
  | succ n ih =>
      calc
        (∑ k ∈ Finset.range (n + 1 + 1),
            if 0 < k ∧ Odd k then 1 / ((k : ℕ) : ℝ) else 0) =
            (∑ k ∈ Finset.range (n + 1),
              if 0 < k ∧ Odd k then 1 / (k : ℝ) else 0) +
              (if 0 < n + 1 ∧ Odd (n + 1) then 1 / ((n + 1 : ℕ) : ℝ) else 0) := by
                rw [Finset.sum_range_succ]
        _ = (harmonic n : ℝ) - (1 / 2 : ℝ) * (harmonic (n / 2) : ℝ) +
              (if 0 < n + 1 ∧ Odd (n + 1) then 1 / ((n + 1 : ℕ) : ℝ) else 0) := by
                rw [ih]
        _ = (harmonic (n + 1) : ℝ) -
              (1 / 2 : ℝ) * (harmonic ((n + 1) / 2) : ℝ) := by
                rcases Nat.even_or_odd n with hn | hn
                · obtain ⟨k, rfl⟩ := hn
                  have hdiv₁ : (k + k) / 2 = k := by omega
                  have hdiv₂ : (k + k + 1) / 2 = k := by omega
                  have hodd : Odd (k + k + 1) := by
                    rw [Nat.odd_iff]
                    omega
                  simp [hdiv₁, hdiv₂, hodd, harmonic_succ]
                  ring
                · obtain ⟨k, rfl⟩ := hn
                  have hdiv₁ : (2 * k + 1) / 2 = k := by omega
                  have hdiv₂ : (2 * k + 1 + 1) / 2 = k + 1 := by omega
                  have hnotodd : ¬ Odd (2 * k + 1 + 1) := by
                    rw [Nat.odd_iff]
                    omega
                  simp [hdiv₁, hdiv₂, hnotodd, harmonic_succ]
                  field_simp
                  ring

theorem platform_tendsto_harmonic_div_log :
    Tendsto (fun n : ℕ => (harmonic n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herror :
      Tendsto
        (fun n : ℕ =>
          ((harmonic n : ℝ) - Real.log (n : ℝ)) / Real.log (n : ℝ))
        atTop (𝓝 0) := by
    exact Real.tendsto_harmonic_sub_log.div_atTop hlog
  have hself :
      Tendsto (fun n : ℕ => Real.log (n : ℝ) / Real.log (n : ℝ))
        atTop (𝓝 (1 : ℝ)) := by
    refine (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hpos : 0 < Real.log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < n by omega)
    simp [hpos.ne']
  simpa [sub_div] using herror.add hself

theorem platform_tendsto_log_nat_div_two_div_log_nat :
    Tendsto
      (fun n : ℕ => Real.log ((n / 2 : ℕ) : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconstdiv :
      Tendsto (fun n : ℕ => Real.log (4 : ℝ) / Real.log (n : ℝ))
        atTop (𝓝 0) := hlog.const_div_atTop (Real.log 4)
  have hbounds : ∀ᶠ n : ℕ in atTop,
      0 ≤ 1 - Real.log ((n / 2 : ℕ) : ℝ) / Real.log (n : ℝ) ∧
        1 - Real.log ((n / 2 : ℕ) : ℝ) / Real.log (n : ℝ) ≤
          Real.log (4 : ℝ) / Real.log (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnpos : 0 < n := by omega
    have hmpos : 0 < n / 2 := by omega
    have hlogn : 0 < Real.log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < n by omega)
    have hlogm_le : Real.log ((n / 2 : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
      exact Real.log_le_log (by exact_mod_cast hmpos)
        (by exact_mod_cast (Nat.div_le_self n 2))
    have hmul : n ≤ 4 * (n / 2) := by omega
    have hlog_bound : Real.log (n : ℝ) ≤
        Real.log (4 : ℝ) + Real.log ((n / 2 : ℕ) : ℝ) := by
      calc
        Real.log (n : ℝ) ≤ Real.log ((4 : ℝ) * (n / 2 : ℕ)) := by
          exact Real.log_le_log (by exact_mod_cast hnpos) (by exact_mod_cast hmul)
        _ = Real.log (4 : ℝ) + Real.log ((n / 2 : ℕ) : ℝ) := by
          rw [Real.log_mul]
          · norm_num
          · exact_mod_cast hmpos.ne'
    have hratio_lower :
        1 - Real.log (4 : ℝ) / Real.log (n : ℝ) ≤
          Real.log ((n / 2 : ℕ) : ℝ) / Real.log (n : ℝ) := by
      calc
        1 - Real.log (4 : ℝ) / Real.log (n : ℝ) =
            (Real.log (n : ℝ) - Real.log (4 : ℝ)) / Real.log (n : ℝ) := by
              field_simp [hlogn.ne']
        _ ≤ Real.log ((n / 2 : ℕ) : ℝ) / Real.log (n : ℝ) := by
          exact div_le_div_of_nonneg_right (by linarith) hlogn.le
    have hratio_upper :
        Real.log ((n / 2 : ℕ) : ℝ) / Real.log (n : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hlogn]
      linarith
    constructor <;> linarith
  have hzero := squeeze_zero'
    (hbounds.mono fun _ h => h.1)
    (hbounds.mono fun _ h => h.2)
    hconstdiv
  have hone := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hzero
  simpa only [sub_sub_cancel, sub_zero] using hone

theorem platform_tendsto_harmonic_nat_div_two_div_log :
    Tendsto
      (fun n : ℕ => (harmonic (n / 2) : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
  have hdiv : Tendsto (fun n : ℕ => n / 2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro m
    filter_upwards [eventually_ge_atTop (2 * m)] with n hn
    exact (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hharmonic :
      Tendsto
        (fun n : ℕ =>
          (harmonic (n / 2) : ℝ) / Real.log ((n / 2 : ℕ) : ℝ))
        atTop (𝓝 (1 : ℝ)) := by
    simpa [Function.comp_def] using platform_tendsto_harmonic_div_log.comp hdiv
  have hprod := hharmonic.mul platform_tendsto_log_nat_div_two_div_log_nat
  have hprod' := hprod.congr' (show
      (fun n : ℕ =>
        (harmonic (n / 2) : ℝ) / Real.log ((n / 2 : ℕ) : ℝ) *
          (Real.log ((n / 2 : ℕ) : ℝ) / Real.log (n : ℝ))) =ᶠ[atTop]
        (fun n : ℕ => (harmonic (n / 2) : ℝ) / Real.log (n : ℝ)) by
    filter_upwards [eventually_ge_atTop 4] with n hn
    have hlogm : 0 < Real.log ((n / 2 : ℕ) : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < n / 2 by omega)
    exact div_mul_div_cancel₀ hlogm.ne')
  simpa using hprod'

theorem platform_weightedLogMass_odd_positive_true_tendsto_half :
    Tendsto
      (fun n : ℕ =>
        weightedLogMass
          (fun k => 0 < k ∧ Odd k)
          (fun _ => True)
          (fun k => 1 / (k : ℝ)) n)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hmass : ∀ n : ℕ,
      weightedLogMass
          (fun k => 0 < k ∧ Odd k)
          (fun _ => True)
          (fun k => 1 / (k : ℝ)) n =
        (harmonic n : ℝ) / Real.log (n : ℝ) -
          (1 / 2 : ℝ) * ((harmonic (n / 2) : ℝ) / Real.log (n : ℝ)) := by
    intro n
    unfold weightedLogMass
    simp only [and_true]
    rw [platform_odd_harmonic_sum_eq]
    ring
  have hlim := platform_tendsto_harmonic_div_log.sub
    ((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2))).mul
      platform_tendsto_harmonic_nat_div_two_div_log)
  have hlim' : Tendsto
      (fun n : ℕ =>
        (harmonic n : ℝ) / Real.log (n : ℝ) -
          (1 / 2 : ℝ) * ((harmonic (n / 2) : ℝ) / Real.log (n : ℝ)))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    convert hlim using 1
    norm_num
  apply hlim'.congr'
  filter_upwards [] with n
  exact (hmass n).symm

theorem platform_tendsto_log_nat_floor_div_log_real :
    Tendsto
      (fun x : ℝ => Real.log (⌊x⌋₊ : ℝ) / Real.log x)
      atTop (𝓝 (1 : ℝ)) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop
  have hconstdiv :
      Tendsto (fun x : ℝ => Real.log (2 : ℝ) / Real.log x)
        atTop (𝓝 0) := hlog.const_div_atTop (Real.log 2)
  have hbounds : ∀ᶠ x : ℝ in atTop,
      0 ≤ 1 - Real.log (⌊x⌋₊ : ℝ) / Real.log x ∧
        1 - Real.log (⌊x⌋₊ : ℝ) / Real.log x ≤
          Real.log (2 : ℝ) / Real.log x := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx_nonneg : (0 : ℝ) ≤ x := by linarith
    have hfloor_two : 2 ≤ ⌊x⌋₊ := by
      exact (Nat.le_floor_iff' (by omega : 2 ≠ 0)).2 (by exact_mod_cast hx)
    have hfloor_pos : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by
      exact_mod_cast (show 0 < ⌊x⌋₊ by omega)
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hlogfloor : 0 < Real.log (⌊x⌋₊ : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < ⌊x⌋₊ by omega))
    have hfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx_nonneg
    have hlogfloor_le : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
      Real.log_le_log hfloor_pos hfloor_le
    have hxfloor : x ≤ 2 * (⌊x⌋₊ : ℝ) := by
      have hlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      have hone : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by linarith
      linarith
    have hlog_bound : Real.log x ≤
        Real.log (2 : ℝ) + Real.log (⌊x⌋₊ : ℝ) := by
      calc
        Real.log x ≤ Real.log ((2 : ℝ) * (⌊x⌋₊ : ℝ)) :=
          Real.log_le_log (by linarith) hxfloor
        _ = Real.log (2 : ℝ) + Real.log (⌊x⌋₊ : ℝ) := by
          rw [Real.log_mul]
          · norm_num
          · exact hfloor_pos.ne'
    have hratio_lower : 1 - Real.log (2 : ℝ) / Real.log x ≤
        Real.log (⌊x⌋₊ : ℝ) / Real.log x := by
      calc
        1 - Real.log (2 : ℝ) / Real.log x =
            (Real.log x - Real.log (2 : ℝ)) / Real.log x := by
              field_simp [hlogx.ne']
        _ ≤ Real.log (⌊x⌋₊ : ℝ) / Real.log x :=
          div_le_div_of_nonneg_right (by linarith) hlogx.le
    have hratio_upper : Real.log (⌊x⌋₊ : ℝ) / Real.log x ≤ 1 := by
      rw [div_le_iff₀ hlogx]
      linarith
    constructor <;> linarith
  have hzero := squeeze_zero'
    (hbounds.mono fun _ h => h.1)
    (hbounds.mono fun _ h => h.2)
    hconstdiv
  have hone := (tendsto_const_nhds :
    Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub hzero
  simpa only [sub_sub_cancel, sub_zero] using hone

theorem platform_weightedLogMassReal_eq_nat_floor_mul_log_ratio
    (D E : ℕ → Prop) (w : ℕ → ℝ) :
    ∀ᶠ x : ℝ in atTop,
      weightedLogMassReal D E w x =
        weightedLogMass D E w ⌊x⌋₊ *
          (Real.log (⌊x⌋₊ : ℝ) / Real.log x) := by
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx_nonneg : (0 : ℝ) ≤ x := by linarith
  have hfloor_two : 2 ≤ ⌊x⌋₊ := by
    exact (Nat.le_floor_iff' (by omega : 2 ≠ 0)).2 (by exact_mod_cast hx)
  have hlogfloor : Real.log (⌊x⌋₊ : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < ⌊x⌋₊ by omega))).ne'
  have hlogx : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
  unfold weightedLogMassReal weightedLogMass
  field_simp [hlogfloor, hlogx]

theorem platform_weightedLogMass_nat_limit_to_real_of_limit
    (D E : ℕ → Prop) (w : ℕ → ℝ) (L : ℝ)
    (hlim : Tendsto (fun n : ℕ => weightedLogMass D E w n) atTop (𝓝 L)) :
    Tendsto (fun x : ℝ => weightedLogMassReal D E w x) atTop (𝓝 L) := by
  have hfloor : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop
  have hmass : Tendsto
      (fun x : ℝ => weightedLogMass D E w ⌊x⌋₊) atTop (𝓝 L) :=
    hlim.comp hfloor
  have hprod : Tendsto
      (fun x : ℝ => weightedLogMass D E w ⌊x⌋₊ *
        (Real.log (⌊x⌋₊ : ℝ) / Real.log x))
      atTop (𝓝 (L * 1)) :=
    hmass.mul platform_tendsto_log_nat_floor_div_log_real
  have hprod' := hprod.congr'
    ((platform_weightedLogMassReal_eq_nat_floor_mul_log_ratio D E w).mono
      fun _ h => h.symm)
  simpa using hprod'



theorem platform_weightedLogMassReal_odd_positive_true_tendsto_half :
    Tendsto
      (fun x : ℝ =>
        weightedLogMassReal
          (fun k => 0 < k ∧ Odd k)
          (fun _ => True)
          (fun k => 1 / (k : ℝ)) x)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  exact platform_weightedLogMass_nat_limit_to_real_of_limit
    (fun k => 0 < k ∧ Odd k)
    (fun _ => True)
    (fun k => 1 / (k : ℝ))
    (1 / 2 : ℝ)
    platform_weightedLogMass_odd_positive_true_tendsto_half


theorem positive_harmonic_sum_eq (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      if 0 < k then 1 / (k : ℝ) else 0) =
      (harmonic n : ℝ) := by
  induction n with
  | zero => simp [harmonic]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, harmonic_succ]
      simp

theorem weightedLogMass_positive_true_tendsto_one :
    Tendsto
      (fun n : ℕ =>
        weightedLogMass
          (fun k => 0 < k)
          (fun _ => True)
          (fun k => 1 / (k : ℝ)) n)
      atTop (𝓝 (1 : ℝ)) := by
  have hmass : ∀ n : ℕ,
      weightedLogMass
          (fun k => 0 < k)
          (fun _ => True)
          (fun k => 1 / (k : ℝ)) n =
        (harmonic n : ℝ) / Real.log (n : ℝ) := by
    intro n
    unfold weightedLogMass
    simp only [and_true]
    rw [positive_harmonic_sum_eq]
  apply platform_tendsto_harmonic_div_log.congr'
  filter_upwards [] with n
  exact (hmass n).symm

theorem weightedLogMassReal_positive_true_tendsto_one :
    Tendsto
      (fun x : ℝ =>
        weightedLogMassReal
          (fun k => 0 < k)
          (fun _ => True)
          (fun k => 1 / (k : ℝ)) x)
      atTop (𝓝 (1 : ℝ)) := by
  exact platform_weightedLogMass_nat_limit_to_real_of_limit
    (fun k => 0 < k)
    (fun _ => True)
    (fun k => 1 / (k : ℝ))
    (1 : ℝ)
    weightedLogMass_positive_true_tendsto_one


theorem reciprocal_sum_natMulImage
    (d : ℕ) (hd : 0 < d) (P : ℕ → Prop) (x : ℝ) :
    (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
      if (∃ m, n = d * m ∧ P m) then 1 / (n : ℝ) else 0)
      =
    (1 / (d : ℝ)) *
      (∑ m ∈ Finset.range (⌊x / (d : ℝ)⌋₊ + 1),
        if P m then 1 / (m : ℝ) else 0) := by
  let s := (Finset.range (⌊x⌋₊ / d + 1)).filter P
  let t := (Finset.range (⌊x⌋₊ + 1)).filter (fun n => ∃ m, n = d * m ∧ P m)
  have hfloor : ⌊x / (d : ℝ)⌋₊ = ⌊x⌋₊ / d := by
    exact Nat.floor_div_natCast x d
  have hmem (m : ℕ) :
      m ∈ s ↔ d * m ∈ t := by
    simp only [s, t, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hm
      constructor
      · have hm' : m ≤ ⌊x⌋₊ / d := by omega
        have hmul : m * d ≤ ⌊x⌋₊ :=
          (Nat.le_div_iff_mul_le hd).mp hm'
        simpa [Nat.mul_comm] using (Nat.lt_succ_of_le hmul)
      · exact ⟨m, rfl, hm.2⟩
    · intro hm
      rcases hm.2 with ⟨k, hk, hPk⟩
      have hmk : m = k := by
        apply Nat.mul_left_cancel hd
        exact hk
      subst hmk
      constructor
      · have hmul : d * m ≤ ⌊x⌋₊ := Nat.le_of_lt_succ hm.1
        have hmul' : m * d ≤ ⌊x⌋₊ := by simpa [Nat.mul_comm] using hmul
        have hm' : m ≤ ⌊x⌋₊ / d :=
          (Nat.le_div_iff_mul_le hd).mpr hmul'
        omega
      · exact hPk
  have hmap :
      (∑ m ∈ s, 1 / ((d * m : ℕ) : ℝ)) =
        ∑ n ∈ t, 1 / (n : ℝ) := by
    refine Finset.sum_bij (fun m _ => d * m) ?_ ?_ ?_ ?_
    · intro m hm
      exact (hmem m).mp hm
    · intro m₁ hm₁ m₂ hm₂ heq
      apply Nat.mul_left_cancel hd
      exact heq
    · intro n hn
      simp only [t, Finset.mem_filter, Finset.mem_range] at hn
      rcases hn.2 with ⟨m, hnm, hPm⟩
      subst n
      have hm : m ∈ s := by
        simp only [s, Finset.mem_filter, Finset.mem_range]
        have hmul : d * m ≤ ⌊x⌋₊ := Nat.le_of_lt_succ hn.1
        have hmul' : m * d ≤ ⌊x⌋₊ := by simpa [Nat.mul_comm] using hmul
        have hmdiv : m ≤ ⌊x⌋₊ / d :=
          (Nat.le_div_iff_mul_le hd).mpr hmul'
        exact ⟨by omega, hPm⟩
      exact ⟨m, hm, rfl⟩
    · intro m hm
      rfl
  have hfilter :
      (∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        if (∃ m, n = d * m ∧ P m) then 1 / (n : ℝ) else 0) =
        ∑ n ∈ t, 1 / (n : ℝ) := by
    exact (Finset.sum_filter _ _).symm
  have hfilter' :
      (∑ m ∈ Finset.range (⌊x⌋₊ / d + 1),
        if P m then 1 / (m : ℝ) else 0) =
        ∑ m ∈ s, 1 / (m : ℝ) := by
    exact (Finset.sum_filter _ _).symm
  rw [hfilter, ← hmap, hfloor, hfilter', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  push_cast
  ring

theorem tendsto_log_natMul_div_log
    (d : ℕ) (hd : 0 < d) :
    Tendsto
      (fun x : ℝ => Real.log (x / (d : ℝ)) / Real.log x)
      atTop (𝓝 (1 : ℝ)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : Tendsto (fun x : ℝ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop
  have hconstdiv :
      Tendsto (fun x : ℝ => Real.log (d : ℝ) / Real.log x)
        atTop (𝓝 0) := by
    exact hlog.const_div_atTop (Real.log (d : ℝ))
  have hsub :
      Tendsto
        (fun x : ℝ => 1 - Real.log (d : ℝ) / Real.log x)
        atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub hconstdiv :
        Tendsto
          (fun x : ℝ => (1 : ℝ) - Real.log (d : ℝ) / Real.log x)
          atTop (𝓝 (1 - 0)))
  apply hsub.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hxpos : 0 < x := by linarith
  have hlogx : Real.log x ≠ 0 :=
    (Real.log_pos (by linarith)).ne'
  rw [Real.log_div hxpos.ne' hd'.ne']
  field_simp

theorem weightedLogMassReal_natMulImage_eq
    (d : ℕ) (hd : 0 < d) (P : ℕ → Prop) :
    ∀ᶠ x : ℝ in atTop,
      weightedLogMassReal
          (fun n => ∃ m, n = d * m ∧ P m)
          (fun _ => True)
          (fun n => 1 / (n : ℝ)) x
        =
      (1 / (d : ℝ)) *
        weightedLogMassReal P (fun _ => True) (fun m => 1 / (m : ℝ))
          (x / (d : ℝ)) *
        (Real.log (x / (d : ℝ)) / Real.log x) := by
  filter_upwards [eventually_ge_atTop (2 * (d : ℝ))] with x hx
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hdone : (1 : ℝ) ≤ d := by
    exact_mod_cast (show 1 ≤ d by omega)
  have hxpos : 0 < x := by nlinarith
  have hx2 : (2 : ℝ) ≤ x := by nlinarith
  have hxdpos : 0 < x / (d : ℝ) := div_pos hxpos hd'
  have hxd2 : (2 : ℝ) ≤ x / (d : ℝ) := by
    exact (le_div_iff₀ hd').2 (by nlinarith)
  have hxd_floor : ⌊x / (d : ℝ)⌋₊ = ⌊x⌋₊ / d :=
    Nat.floor_div_natCast x d
  have hsum := reciprocal_sum_natMulImage d hd P x
  have hlogx : Real.log x ≠ 0 :=
    (Real.log_pos (by linarith [hx2])).ne'
  have hlogxd : Real.log (x / (d : ℝ)) ≠ 0 := by
    exact (Real.log_pos (by linarith [hxd2])).ne'
  unfold weightedLogMassReal
  simp only [and_true]
  rw [hsum]
  rw [hxd_floor]
  field_simp [hlogx, hlogxd]

theorem weightedLogMassReal_natMulImage_tendsto
    (d : ℕ) (hd : 0 < d) (P : ℕ → Prop) (L : ℝ)
    (hP :
      Tendsto
        (fun x : ℝ =>
          weightedLogMassReal P (fun _ => True) (fun m => 1 / (m : ℝ)) x)
        atTop (𝓝 L)) :
    Tendsto
      (fun x : ℝ =>
        weightedLogMassReal
          (fun n => ∃ m, n = d * m ∧ P m)
          (fun _ => True)
          (fun n => 1 / (n : ℝ)) x)
      atTop (𝓝 ((1 / (d : ℝ)) * L)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hscale :
      Tendsto (fun x : ℝ => x / (d : ℝ)) atTop atTop := by
    simpa [div_eq_mul_inv, mul_comm] using
      (show Tendsto (fun x : ℝ => (1 / (d : ℝ)) * x) atTop atTop from
        (Filter.tendsto_const_mul_atTop_of_pos (by positivity)).mpr tendsto_id)
  have hPscale := hP.comp hscale
  have hlogratio := tendsto_log_natMul_div_log d hd
  have hfactor :
      Tendsto
        (fun x : ℝ =>
          (1 / (d : ℝ)) *
            weightedLogMassReal P (fun _ => True) (fun m => 1 / (m : ℝ))
              (x / (d : ℝ)) *
            (Real.log (x / (d : ℝ)) / Real.log x))
        atTop (𝓝 ((1 / (d : ℝ)) * L)) := by
    simpa only [Function.comp_apply, mul_one] using
      (tendsto_const_nhds.mul hPscale).mul hlogratio
  exact hfactor.congr'
    ((weightedLogMassReal_natMulImage_eq d hd P).mono fun _ h => h.symm)


/-- Multiplication by a fixed power of two preserves divergence on positive
inputs, in particular when the new input is restricted to positive odds. -/
theorem threshold_diverges_on_odd_after_pow_two
    (f : ℕ → ℝ)
    (hf : ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < n → M < f n)
    (a : ℕ) :
    ∀ M : ℝ, ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      (0 < m ∧ Odd m) → M < f (2 ^ a * m) := by
  intro M
  obtain ⟨N, hN⟩ := hf M
  refine ⟨N, ?_⟩
  intro m hNm hm
  have hp : 0 < (2 : ℕ) ^ a := pow_pos (by decide) a
  have hle : m ≤ 2 ^ a * m := by
    simpa using Nat.mul_le_mul_right m (Nat.succ_le_of_lt hp)
  exact hN (2 ^ a * m) (hNm.trans hle) (Nat.mul_pos hp hm.1)


theorem collatz_iterate_pow_two_mul (a m : ℕ) :
    collatzStep^[a] (2 ^ a * m) = m := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Function.iterate_succ_apply]
      have heven : Even (2 ^ (a + 1) * m) := by
        refine ⟨2 ^ a * m, ?_⟩
        ring
      rw [collatzStep, if_pos heven]
      rw [pow_succ]
      have hdiv : (2 ^ a * 2 * m) / 2 = 2 ^ a * m := by
        rw [show 2 ^ a * 2 * m = 2 * (2 ^ a * m) by ring]
        exact Nat.mul_div_cancel_left _ (by positivity)
      rw [hdiv]
      exact ih

/-- A positive odd Syracuse input is reached by the ordinary Collatz orbit. -/
theorem collatz_reaches_syracuse_iterate_of_positive_odd
    (m t : ℕ) (_hm : 0 < m) (hodd : ¬Even m) :
    ∃ M : ℕ, collatzStep^[M] m = syracuseStep^[t] m := by
  exact collatz_reaches_syracuse_iterate m hodd t

/-- Lift an odd Syracuse threshold hit to a threshold hit by the Collatz orbit. -/
theorem collatz_threshold_hit_of_positive_odd
    (m t Q : ℕ) (hm : 0 < m) (hodd : ¬Even m)
    (hsyr : syracuseStep^[t] m < Q) :
    ∃ M : ℕ, collatzStep^[M] m < Q := by
  obtain ⟨M, hM⟩ := collatz_reaches_syracuse_iterate_of_positive_odd m t hm hodd
  exact ⟨M, hM ▸ hsyr⟩

/-- Lift an odd Syracuse iterate to an arbitrary positive Collatz input. -/
theorem collatz_reaches_syracuse_iterate_of_positive
    (n t : ℕ) (hn : 0 < n) :
    ∃ a m M : ℕ, Odd m ∧ n = 2 ^ a * m ∧
      collatzStep^[M + a] n = syracuseStep^[t] m := by
  obtain ⟨a, m, hodd, hnrep⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.ne_of_gt hn)
  have hm : 0 < m := by
    rcases hodd with ⟨r, hr⟩
    omega
  obtain ⟨M, hM⟩ := collatz_reaches_syracuse_iterate_of_positive_odd m t
    hm (Nat.not_even_iff_odd.mpr hodd)
  refine ⟨a, m, M, hodd, hnrep, ?_⟩
  rw [Function.iterate_add_apply, hnrep, collatz_iterate_pow_two_mul, hM]

/-- Lift an odd Syracuse threshold hit to an arbitrary positive Collatz input. -/
theorem collatz_threshold_hit_of_positive
    (n t Q : ℕ) (hn : 0 < n)
    (hsyr : ∀ a m : ℕ, Odd m → n = 2 ^ a * m → syracuseStep^[t] m < Q) :
    ∃ a m M : ℕ, Odd m ∧ n = 2 ^ a * m ∧
      syracuseStep^[t] m < Q ∧ collatzStep^[M + a] n < Q := by
  obtain ⟨a, m, hodd, hnrep⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.ne_of_gt hn)
  have hm : 0 < m := by
    rcases hodd with ⟨r, hr⟩
    omega
  obtain ⟨M, hM⟩ := collatz_reaches_syracuse_iterate_of_positive_odd m t
    hm (Nat.not_even_iff_odd.mpr hodd)
  refine ⟨a, m, M, hodd, hnrep, ?_, ?_⟩
  · exact hsyr a m hodd hnrep
  · rw [Function.iterate_add_apply, hnrep, collatz_iterate_pow_two_mul, hM]
    exact hsyr a m hodd hnrep

/-- A real threshold hit by a fixed odd Syracuse orbit lifts through a fixed
    power-of-two prefix to a real threshold hit by the Collatz orbit. -/
theorem collatz_real_threshold_hit_of_power_two_odd
    (a m : ℕ) (hodd : Odd m) (b : ℝ)
    (hsyr : ∃ t : ℕ, (syracuseStep^[t] m : ℝ) < b) :
    ∃ q : ℕ, (collatzStep^[q] (2 ^ a * m) : ℝ) < b := by
  obtain ⟨t, ht⟩ := hsyr
  have hm : 0 < m := by
    rcases hodd with ⟨r, hr⟩
    omega
  obtain ⟨M, hM⟩ := collatz_reaches_syracuse_iterate_of_positive_odd m t hm
    (Nat.not_even_iff_odd.mpr hodd)
  refine ⟨M + a, ?_⟩
  rw [Function.iterate_add_apply, collatz_iterate_pow_two_mul, hM]
  exact ht


theorem power_two_odd_exponent_unique
    (a₁ a₂ m₁ m₂ : ℕ) (hm₁ : Odd m₁) (hm₂ : Odd m₂)
    (h : 2 ^ a₁ * m₁ = 2 ^ a₂ * m₂) : a₁ = a₂ := by
  rcases lt_trichotomy a₁ a₂ with hlt | heq | hgt
  · have hcancel : m₁ = 2 ^ (a₂ - a₁) * m₂ := by
      apply Nat.mul_left_cancel (by positivity : 0 < 2 ^ a₁)
      calc
        2 ^ a₁ * m₁ = 2 ^ a₂ * m₂ := h
        _ = (2 ^ a₁ * 2 ^ (a₂ - a₁)) * m₂ := by
          rw [← pow_add, show a₁ + (a₂ - a₁) = a₂ by omega]
        _ = 2 ^ a₁ * (2 ^ (a₂ - a₁) * m₂) := by ring
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_ne_zero_of_lt hlt)
    have hdiv : 2 ∣ m₁ := by
      refine ⟨2 ^ r * m₂, ?_⟩
      rw [hcancel, hr, pow_succ]
      ring
    exact (hm₁.not_two_dvd_nat hdiv).elim
  · exact heq
  · have hcancel : m₂ = 2 ^ (a₁ - a₂) * m₁ := by
      apply Nat.mul_left_cancel (by positivity : 0 < 2 ^ a₂)
      calc
        2 ^ a₂ * m₂ = 2 ^ a₁ * m₁ := h.symm
        _ = (2 ^ a₂ * 2 ^ (a₁ - a₂)) * m₁ := by
          rw [← pow_add, show a₂ + (a₁ - a₂) = a₁ by omega]
        _ = 2 ^ a₂ * (2 ^ (a₁ - a₂) * m₁) := by ring
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_ne_zero_of_lt hgt)
    have hdiv : 2 ∣ m₂ := by
      refine ⟨2 ^ r * m₁, ?_⟩
      rw [hcancel, hr, pow_succ]
      ring
    exact (hm₂.not_two_dvd_nat hdiv).elim

/-- The fixed-`n` form of `power_two_odd_exponent_unique`. -/
theorem power_two_odd_representation_unique
    (n a₁ a₂ m₁ m₂ : ℕ)
    (hm₁ : 0 < m₁) (hodd₁ : Odd m₁)
    (hm₂ : 0 < m₂) (hodd₂ : Odd m₂)
    (h₁ : n = 2 ^ a₁ * m₁) (h₂ : n = 2 ^ a₂ * m₂) :
    a₁ = a₂ := by
  exact power_two_odd_exponent_unique a₁ a₂ m₁ m₂ hodd₁ hodd₂ (h₁.symm.trans h₂)


def powerTwoOddStratum (a n : ℕ) : Prop :=
  ∃ m : ℕ, n = 2 ^ a * m ∧ Odd m

noncomputable instance powerTwoOddStratumDecidable (a n : ℕ) :
    Decidable (powerTwoOddStratum a n) := Classical.propDecidable _

/-- A finite family of these disjoint stratum indicators has mass at most the
positive-number indicator.  This is an elementary finite-union bound, not a
claim that every positive number belongs to a selected finite family. -/
lemma finset_power_two_odd_strata_sum_le_positive
    (s : Finset ℕ) (n : ℕ) :
    (∑ a ∈ s, if powerTwoOddStratum a n then (1 : ℝ) else 0) ≤
      if 0 < n then 1 else 0 := by
  classical
  by_cases hn : 0 < n
  · by_cases hactive : ∃ a ∈ s, powerTwoOddStratum a n
    · obtain ⟨a, ha, m, hmrep, hmodd⟩ := hactive
      have hsum : (∑ a ∈ s, if powerTwoOddStratum a n then (1 : ℝ) else 0) = 1 := by
        rw [Finset.sum_eq_single a]
        · simp [powerTwoOddStratum, hmrep, hmodd]
        · intro b hb hba
          have hnot : ¬ powerTwoOddStratum b n := by
            intro hbactive
            obtain ⟨m₂, hm₂rep, hm₂odd⟩ := hbactive
            have hab : a = b := power_two_odd_exponent_unique a b m m₂ hmodd hm₂odd
              (hmrep.symm.trans hm₂rep)
            exact hba hab.symm
          simp [hnot]
        · exact fun ha' => (ha' ha).elim
      rw [hsum]
      simp [hn]
    · have hzero : ∀ a ∈ s, ¬ powerTwoOddStratum a n := by
        intro a ha haactive
        exact hactive ⟨a, ha, haactive⟩
      have hsum : (∑ a ∈ s, if powerTwoOddStratum a n then (1 : ℝ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        simp [hzero a ha]
      rw [hsum]
      simp [hn]
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have hzero : ∀ a ∈ s, ¬ powerTwoOddStratum a n := by
      intro a ha haactive
      obtain ⟨m, hmrep, hmodd⟩ := haactive
      have hm : 0 < m := by
        rcases hmodd with ⟨r, hr⟩
        omega
      have hpos : 0 < 2 ^ a * m := by positivity
      omega
    have hsum : (∑ a ∈ s, if powerTwoOddStratum a n then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      simp [hzero a ha]
    rw [hsum]
    simp [hn]


theorem collatz_fixed_stratum_logarithmic_density_of_full_one_six
    (hfull16 : ∀ g : ℕ → ℝ,
      (∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (0 < n ∧ Odd n) → M < g n) →
      Tendsto
        (fun x : ℝ =>
          weightedLogMassReal
            (fun n => 0 < n ∧ Odd n)
            (fun n => ∃ k : ℕ,
              ((syracuseStep^[k] n : ℕ) : ℝ) < g n)
            (fun n => 1 / (n : ℝ)) x)
        atTop (𝓝 (1 / 2 : ℝ)))
    (a : ℕ) (f : ℕ → ℝ)
    (hf : ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < n → M < f n) :
    Tendsto
      (fun x : ℝ =>
        weightedLogMassReal
          (fun n => ∃ m : ℕ, n = 2 ^ a * m ∧ 0 < m ∧ Odd m)
          (fun n => ∃ k : ℕ,
            ((collatzStep^[k] n : ℕ) : ℝ) < f n)
          (fun n => 1 / (n : ℝ)) x)
      atTop (𝓝 (((2 : ℝ) ^ (a + 1))⁻¹)) := by
  let d : ℕ := 2 ^ a
  let D : ℕ → Prop := fun m => 0 < m ∧ Odd m
  let Gs : ℕ → Prop := fun m => ∃ k : ℕ,
    ((syracuseStep^[k] m : ℕ) : ℝ) < f (2 ^ a * m)
  let P : ℕ → Prop := fun m => D m ∧ Gs m
  let Gc : ℕ → Prop := fun n => ∃ k : ℕ,
    ((collatzStep^[k] n : ℕ) : ℝ) < f n
  let Sgood : ℝ → ℝ := fun x =>
    weightedLogMassReal
      (fun n => ∃ m : ℕ, n = d * m ∧ P m)
      (fun _ => True) (fun n => 1 / (n : ℝ)) x
  let Stotal : ℝ → ℝ := fun x =>
    weightedLogMassReal
      (fun n => ∃ m : ℕ, n = d * m ∧ D m)
      (fun _ => True) (fun n => 1 / (n : ℝ)) x
  let T : ℝ → ℝ := fun x =>
    weightedLogMassReal
      (fun n => ∃ m : ℕ, n = d * m ∧ D m) Gc
      (fun n => 1 / (n : ℝ)) x
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hfa : ∀ M : ℝ, ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      (0 < m ∧ Odd m) → M < f (2 ^ a * m) :=
    threshold_diverges_on_odd_after_pow_two f hf a
  have hsyr := hfull16 (fun m => f (2 ^ a * m)) hfa
  have hP : Tendsto
      (fun x : ℝ => weightedLogMassReal P (fun _ => True)
        (fun m => 1 / (m : ℝ)) x)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    refine hsyr.congr' (Filter.Eventually.of_forall (fun x => ?_))
    unfold weightedLogMassReal
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hD' : D m <;> by_cases hGs : Gs m <;> simp [P, D, Gs, hD', hGs]
  have hscaledGood := weightedLogMassReal_natMulImage_tendsto
    d hd P (1 / 2 : ℝ) hP
  have hD : Tendsto
      (fun x : ℝ => weightedLogMassReal D (fun _ => True)
        (fun m => 1 / (m : ℝ)) x)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa [D] using platform_weightedLogMassReal_odd_positive_true_tendsto_half
  have hscaledTotal := weightedLogMassReal_natMulImage_tendsto
    d hd D (1 / 2 : ℝ) hD
  have hvalue : (1 / (d : ℝ)) * (1 / 2 : ℝ) =
      ((2 : ℝ) ^ (a + 1))⁻¹ := by
    dsimp [d]
    norm_num [Nat.cast_pow, one_div, inv_pow, pow_succ]
    ring
  have hgoodlim : Tendsto Sgood atTop
      (𝓝 (((2 : ℝ) ^ (a + 1))⁻¹)) := by
    have h := hscaledGood
    rw [hvalue] at h
    simpa [Sgood] using h
  have htotallim : Tendsto Stotal atTop
      (𝓝 (((2 : ℝ) ^ (a + 1))⁻¹)) := by
    have h := hscaledTotal
    rw [hvalue] at h
    simpa [Stotal] using h
  have hlower : ∀ᶠ x : ℝ in atTop, Sgood x ≤ T x := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    dsimp [Sgood, T]
    unfold weightedLogMassReal
    apply div_le_div_of_nonneg_right
    · apply Finset.sum_le_sum
      intro n hn
      by_cases hS : ∃ m : ℕ, n = d * m ∧ P m
      · obtain ⟨m, hnm, hmP⟩ := hS
        have htargetD : ∃ m : ℕ, n = d * m ∧ D m :=
          ⟨m, hnm, hmP.1⟩
        have hcollatz : Gc n := by
          obtain ⟨k, hk⟩ := hmP.2
          obtain ⟨q, hq⟩ := collatz_real_threshold_hit_of_power_two_odd
            a m hmP.1.2 (f n) (by exact ⟨k, by simpa [d, hnm] using hk⟩)
          exact ⟨q, by simpa [d, hnm] using hq⟩
        have hS' : ∃ m : ℕ, n = d * m ∧ P m := ⟨m, hnm, hmP⟩
        simp [hS', htargetD, hcollatz]
      · by_cases hT : (∃ m : ℕ, n = d * m ∧ D m) ∧ Gc n
        · simp [hS, hT]
        · simp [hS, hT]
    · exact (Real.log_pos (by linarith)).le
  have hupper : ∀ᶠ x : ℝ in atTop, T x ≤ Stotal x := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    dsimp [T, Stotal]
    unfold weightedLogMassReal
    apply div_le_div_of_nonneg_right
    · apply Finset.sum_le_sum
      intro n hn
      by_cases hT : (∃ m : ℕ, n = d * m ∧ D m) ∧ Gc n
      · simp [hT]
      · by_cases hD' : ∃ m : ℕ, n = d * m ∧ D m
        · have hGc : ¬ Gc n := by
            intro hGc'
            exact hT ⟨hD', hGc'⟩
          simp [hGc]
          positivity
        · simp [hT, hD']
    · exact (Real.log_pos (by linarith)).le
  have hTlim : Tendsto T atTop
      (𝓝 (((2 : ℝ) ^ (a + 1))⁻¹)) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro r hr
      have hgood := hgoodlim.eventually (Ioi_mem_nhds hr)
      filter_upwards [hgood, hlower] with x hxgood hxlower
      exact lt_of_lt_of_le hxgood hxlower
    · intro r hr
      have htotal := htotallim.eventually (Iio_mem_nhds hr)
      filter_upwards [hupper, htotal] with x hxupper hxtotal
      exact lt_of_le_of_lt hxupper hxtotal
  simpa [T, d, D, Gc] using hTlim

/- Compatibility wrapper for existing local consumers.  New standalone
   assemblies should call the explicit-parameter producer above with the
   published full-1.6 theorem instead. -/
theorem collatz_fixed_stratum_logarithmic_density
    (a : ℕ) (f : ℕ → ℝ)
    (hf : ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < n → M < f n) :
    Tendsto
      (fun x : ℝ =>
        weightedLogMassReal
          (fun n => ∃ m : ℕ, n = 2 ^ a * m ∧ 0 < m ∧ Odd m)
          (fun n => ∃ k : ℕ,
            ((collatzStep^[k] n : ℕ) : ℝ) < f n)
          (fun n => 1 / (n : ℝ)) x)
      atTop (𝓝 (((2 : ℝ) ^ (a + 1))⁻¹)) := by
  exact collatz_fixed_stratum_logarithmic_density_of_full_one_six
    syracuse_almost_bounded_logarithmic a f hf

theorem finite_strata_squeeze_to_one
    (good total : ℝ → ℝ) (stratum : ℕ → ℝ → ℝ)
    (hupper : ∀ᶠ x : ℝ in atTop, good x ≤ total x)
    (htotal : Tendsto total atTop (𝓝 (1 : ℝ)))
    (hfinite : ∀ A : ℕ, ∀ᶠ x : ℝ in atTop,
      (∑ a ∈ Finset.range (A + 1), stratum a x) ≤ good x)
    (hstratum : ∀ a : ℕ,
      Tendsto (fun x : ℝ => stratum a x) atTop
        (𝓝 (((2 : ℝ) ^ (a + 1))⁻¹)))
    (hpartial : Tendsto
      (fun A : ℕ =>
        ∑ a ∈ Finset.range (A + 1), ((2 : ℝ) ^ (a + 1))⁻¹)
      atTop (𝓝 (1 : ℝ))) :
    Tendsto good atTop (𝓝 (1 : ℝ)) := by
  have hsum : ∀ A : ℕ,
      Tendsto
        (fun x : ℝ => ∑ a ∈ Finset.range (A + 1), stratum a x)
        atTop
        (𝓝 (∑ a ∈ Finset.range (A + 1), ((2 : ℝ) ^ (a + 1))⁻¹)) := by
    intro A
    induction A with
    | zero =>
        simpa using hstratum 0
    | succ A ih =>
        simpa only [Finset.sum_range_succ] using
          (ih.add (hstratum (A + 1)))
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    have hpartial_a : ∀ᶠ A : ℕ in atTop,
        a < ∑ j ∈ Finset.range (A + 1), ((2 : ℝ) ^ (j + 1))⁻¹ := by
      exact hpartial.eventually (Ioi_mem_nhds ha)
    obtain ⟨A, hA⟩ := eventually_atTop.1 hpartial_a
    have hpartialA : a <
        ∑ j ∈ Finset.range (A + 1), ((2 : ℝ) ^ (j + 1))⁻¹ :=
      hA A le_rfl
    have hsum_a : ∀ᶠ x : ℝ in atTop,
        a < ∑ j ∈ Finset.range (A + 1), stratum j x := by
      exact (hsum A).eventually (Ioi_mem_nhds hpartialA)
    filter_upwards [hsum_a, hfinite A] with x hxsum hxfinite
    exact lt_of_lt_of_le hxsum hxfinite
  · intro b hb
    have htotal_b : ∀ᶠ x : ℝ in atTop, total x < b := by
      exact htotal.eventually (Iio_mem_nhds hb)
    filter_upwards [hupper, htotal_b] with x hxupper hxtotal
    exact lt_of_le_of_lt hxupper hxtotal

theorem collatz_almost_bounded_logarithmic_of_stratum_transfer
    (f : ℕ → ℝ)
    (hf : ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < n → M < f n)
    (hstratum : ∀ a : ℕ,
      Tendsto
        (fun x : ℝ =>
          weightedLogMassReal
            (fun n => ∃ m : ℕ, n = 2 ^ a * m ∧ 0 < m ∧ Odd m)
            (fun n => ∃ k : ℕ,
              ((collatzStep^[k] n : ℕ) : ℝ) < f n)
            (fun n => 1 / (n : ℝ)) x)
        atTop (𝓝 (((2 : ℝ) ^ (a + 1))⁻¹)))
    (hfinite : ∀ A : ℕ, ∀ᶠ x : ℝ in atTop,
      (∑ a ∈ Finset.range (A + 1),
        weightedLogMassReal
          (fun n => ∃ m : ℕ, n = 2 ^ a * m ∧ 0 < m ∧ Odd m)
          (fun n => ∃ k : ℕ,
            ((collatzStep^[k] n : ℕ) : ℝ) < f n)
          (fun n => 1 / (n : ℝ)) x) ≤
        weightedLogMassReal
          (fun n => 0 < n)
          (fun n => ∃ k : ℕ,
            ((collatzStep^[k] n : ℕ) : ℝ) < f n)
          (fun n => 1 / (n : ℝ)) x) :
    Tendsto
      (fun x : ℝ =>
        weightedLogMassReal
          (fun n => 0 < n)
          (fun n => ∃ k : ℕ,
            ((collatzStep^[k] n : ℕ) : ℝ) < f n)
          (fun n => 1 / (n : ℝ)) x)
      atTop (𝓝 (1 : ℝ)) := by
  let good : ℝ → ℝ := fun x =>
    weightedLogMassReal
      (fun n => 0 < n)
      (fun n => ∃ k : ℕ,
        ((collatzStep^[k] n : ℕ) : ℝ) < f n)
      (fun n => 1 / (n : ℝ)) x
  let total : ℝ → ℝ := fun x =>
    weightedLogMassReal (fun n => 0 < n) (fun _ => True)
      (fun n => 1 / (n : ℝ)) x
  let stratum : ℕ → ℝ → ℝ := fun a x =>
    weightedLogMassReal
      (fun n => ∃ m : ℕ, n = 2 ^ a * m ∧ 0 < m ∧ Odd m)
      (fun n => ∃ k : ℕ,
        ((collatzStep^[k] n : ℕ) : ℝ) < f n)
      (fun n => 1 / (n : ℝ)) x
  have htotal : Tendsto total atTop (𝓝 (1 : ℝ)) := by
    simpa [total] using weightedLogMassReal_positive_true_tendsto_one
  have hupper : ∀ᶠ x : ℝ in atTop, good x ≤ total x := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    dsimp [good, total]
    unfold weightedLogMassReal
    apply div_le_div_of_nonneg_right
    · apply Finset.sum_le_sum
      intro n hn
      by_cases hpos : 0 < n
      · by_cases hsuccess : ∃ k : ℕ,
          ((collatzStep^[k] n : ℕ) : ℝ) < f n
        · simp [hpos, hsuccess]
        · simp [hpos, hsuccess]
      · simp [hpos]
    · exact (Real.log_pos (by linarith)).le
  have hpartial : Tendsto
      (fun A : ℕ =>
        ∑ a ∈ Finset.range (A + 1), ((2 : ℝ) ^ (a + 1))⁻¹)
      atTop (𝓝 (1 : ℝ)) := by
    have hsum_geom : ∀ A : ℕ,
        (∑ a ∈ Finset.range (A + 1), ((2 : ℝ) ^ (a + 1))⁻¹) =
          1 - ((2 : ℝ) ^ (A + 1))⁻¹ := by
      intro A
      induction A with
      | zero => norm_num
      | succ A ih =>
          rw [Finset.sum_range_succ, ih]
          field_simp
          ring
    have hpow : Tendsto
        (fun A : ℕ => ((2 : ℝ) ^ (A + 1))⁻¹)
        atTop (𝓝 0) := by
      have hbase : Tendsto (fun A : ℕ =>
          ((1 / 2 : ℝ) ^ A)) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
      have hsucc : Tendsto (fun A : ℕ => A + 1) atTop atTop := by
        refine tendsto_atTop.2 ?_
        intro n
        filter_upwards [eventually_ge_atTop n] with A hA
        omega
      have hshift := hbase.comp hsucc
      change Tendsto (fun A : ℕ => ((1 / 2 : ℝ) ^ (A + 1))) atTop (𝓝 0) at hshift
      convert hshift using 1
      ext A
      rw [← inv_pow]
      norm_num [one_div]
    have hdiff := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hpow
    simpa [hsum_geom] using hdiff
  apply finite_strata_squeeze_to_one good total stratum hupper htotal
  · simpa [good, stratum] using hfinite
  · simpa [stratum] using hstratum
  · exact hpartial

theorem solution
    (f : ℕ → ℝ)
    (hf : ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < n → M < f n) :
    Tendsto
      (fun x : ℝ =>
        weightedLogMassReal
          (fun n => 0 < n)
          (fun n => ∃ k : ℕ,
            ((collatzStep^[k] n : ℕ) : ℝ) < f n)
          (fun n => 1 / (n : ℝ)) x)
      atTop (𝓝 (1 : ℝ)) := by
  let good : ℝ → ℝ := fun x =>
    weightedLogMassReal
      (fun n => 0 < n)
      (fun n => ∃ k : ℕ,
        ((collatzStep^[k] n : ℕ) : ℝ) < f n)
      (fun n => 1 / (n : ℝ)) x
  have hfinite : ∀ A : ℕ, ∀ᶠ x : ℝ in atTop,
      (∑ a ∈ Finset.range (A + 1),
        weightedLogMassReal
          (fun n => ∃ m : ℕ, n = 2 ^ a * m ∧ 0 < m ∧ Odd m)
          (fun n => ∃ k : ℕ,
            ((collatzStep^[k] n : ℕ) : ℝ) < f n)
          (fun n => 1 / (n : ℝ)) x) ≤ good x := by
    intro A
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    simp only [weightedLogMassReal, good]
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right
    · rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro n hn
      let D : ℕ → Prop := fun a => ∃ m : ℕ,
        n = 2 ^ a * m ∧ 0 < m ∧ Odd m
      let G : Prop := ∃ k : ℕ,
        ((collatzStep^[k] n : ℕ) : ℝ) < f n
      have hD : ∀ a : ℕ, D a ↔ powerTwoOddStratum a n := by
        intro a
        constructor
        · rintro ⟨m, hnm, hmpos, hmodd⟩
          exact ⟨m, hnm, hmodd⟩
        · rintro ⟨m, hnm, hmodd⟩
          refine ⟨m, hnm, ?_, hmodd⟩
          rcases hmodd with ⟨r, hr⟩
          omega
      by_cases hG : G
      · have hsum :
            (∑ a ∈ Finset.range (A + 1),
              if D a ∧ G then (1 / (n : ℝ)) else 0) =
              (1 / (n : ℝ)) *
                (∑ a ∈ Finset.range (A + 1),
                  if powerTwoOddStratum a n then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          by_cases hDa : D a
          · have hPa : powerTwoOddStratum a n := (hD a).mp hDa
            simp [D, G, hG, hDa, hPa]
          · have hPa : ¬ powerTwoOddStratum a n := by
              intro hPa
              exact hDa ((hD a).mpr hPa)
            simp [D, G, hG, hDa, hPa]
        have hsumind := finset_power_two_odd_strata_sum_le_positive
          (Finset.range (A + 1)) n
        have hw : 0 ≤ (1 / (n : ℝ)) := by positivity
        have hmul := mul_le_mul_of_nonneg_left hsumind hw
        by_cases hnpos : 0 < n
        · rw [hsum]
          simpa [D, G, hG, hnpos] using hmul
        · have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnpos
          rw [hsum]
          simpa [D, G, hG, hnpos, hnzero] using hmul
      · simp [D, G, hG]
    · exact (Real.log_pos (by linarith)).le
  apply collatz_almost_bounded_logarithmic_of_stratum_transfer f hf
  · intro a
    exact collatz_fixed_stratum_logarithmic_density a f hf
  · simpa [good] using hfinite
