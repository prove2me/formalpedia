-- Prove2me | solution 1 for OptimalPAC.SampleComplexity.majority_error_le_twelve
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T20:29:57.093043+00:00
-- url     : https://prove2.me/submissions/3e4dc8d7-b9ad-4f41-a074-9f8dee958de8

import Mathlib
import Definitions.Def_OptimalPAC_SampleComplexity_Model

set_option autoImplicit false

open MeasureTheory

namespace OptimalPAC.SampleComplexity

open scoped ENNReal

theorem p6e_measSet_ER {X : Type*} [MeasurableSpace X] {h f : X → Bool} (hh : Measurable h)
    (hf : Measurable f) : MeasurableSet (ER h f) :=
  (measurableSet_eq_fun hh hf).compl

theorem p6e_meas_count {X : Type*} [MeasurableSpace X] (L : List (X → Bool))
    (p : (X → Bool) → X → Bool) (hp : ∀ h ∈ L, MeasurableSet {x | p h x = true}) :
    Measurable (fun x => ((L.countP (fun h => p h x) : ℕ) : ℝ≥0∞)) := by
  induction L with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun h hh => hp h (List.mem_cons_of_mem a hh))
    have ha := hp a List.mem_cons_self
    simp only [List.countP_cons, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact ih'.add (Measurable.ite ha measurable_const measurable_const)

theorem p6e_meas_majority {X : Type*} [MeasurableSpace X] (L : List (X → Bool))
    (hL : ∀ h ∈ L, Measurable h) : Measurable (majority L) := by
  apply measurable_to_bool
  have h1 := p6e_meas_count L (fun h x => decide (h x = false))
    (fun h hh => by
      convert (hL h hh) (measurableSet_singleton false) using 1
      ext x; simp)
  have h2 := p6e_meas_count L (fun h x => decide (h x = true))
    (fun h hh => by
      convert (hL h hh) (measurableSet_singleton true) using 1
      ext x; simp)
  have : majority L ⁻¹' {true} =
      {x | ((L.countP (fun h => decide (h x = false)) : ℕ) : ℝ≥0∞) ≤
        ((L.countP (fun h => decide (h x = true)) : ℕ) : ℝ≥0∞)} := by
    ext x; simp [majority]
  rw [this]
  exact measurableSet_le h1 h2

theorem p6e_lint_eq {X : Type*} [MeasurableSpace X] (P : Measure X) (f : X → Bool)
    (hf : Measurable f) (A : Set X) (hA : MeasurableSet A) (L : List (X → Bool))
    (hL : ∀ h ∈ L, Measurable h) :
    ∫⁻ x, A.indicator (fun x => ((L.countP (fun h => decide (h x ≠ f x)) : ℕ) : ℝ≥0∞)) x ∂P =
      (L.map (fun h => P (A ∩ ER h f))).sum := by
  induction L with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun h hh => hL h (List.mem_cons_of_mem a hh))
    have ha := hL a List.mem_cons_self
    have hE : MeasurableSet (ER a f) := p6e_measSet_ER ha hf
    have hfun : (fun x => A.indicator
        (fun x => ((List.countP (fun h => decide (h x ≠ f x)) (a :: l) : ℕ) : ℝ≥0∞)) x) =
        fun x => (A ∩ ER a f).indicator 1 x +
          A.indicator (fun x => ((l.countP (fun h => decide (h x ≠ f x)) : ℕ) : ℝ≥0∞)) x := by
      funext x
      by_cases hxA : x ∈ A
      · by_cases hxE : x ∈ ER a f
        · have hxE' : a x ≠ f x := hxE
          simp [Set.indicator_of_mem hxA, Set.indicator_of_mem (Set.mem_inter hxA hxE),
            List.countP_cons, hxE', add_comm]
        · have hxE' : a x = f x := by simpa [ER] using hxE
          have : x ∉ A ∩ ER a f := fun h => hxE h.2
          simp [Set.indicator_of_mem hxA, Set.indicator_of_notMem this, List.countP_cons, hxE']
      · have : x ∉ A ∩ ER a f := fun h => hxA h.1
        simp [Set.indicator_of_notMem hxA, Set.indicator_of_notMem this]
    rw [hfun, lintegral_add_left (f := (A ∩ ER a f).indicator 1)
      (measurable_one.indicator (hA.inter hE)),
      lintegral_indicator_one (hA.inter hE), ih']
    simp

theorem p6e_sum_toReal {X : Type*} [MeasurableSpace X] (P : Measure X) [IsFiniteMeasure P]
    (g : (X → Bool) → Set X) (L : List (X → Bool)) :
    (L.map (fun h => P (g h))).sum ≠ ⊤ ∧
      (L.map (fun h => (P (g h)).toReal)).sum = ((L.map (fun h => P (g h))).sum).toReal := by
  induction L with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [List.map_cons, List.sum_cons]
    refine ⟨ENNReal.add_ne_top.2 ⟨measure_ne_top P _, h1⟩, ?_⟩
    rw [ENNReal.toReal_add (measure_ne_top P _) h1, h2]

theorem p6e_countP_tf {X : Type*} (L : List (X → Bool)) (x : X) :
    L.countP (fun h => decide (h x = true)) + L.countP (fun h => decide (h x = false)) =
      L.length := by
  induction L with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons, List.countP_cons, List.length_cons]
    have : (if decide (a x = true) = true then 1 else 0) +
        (if decide (a x = false) = true then 1 else 0) = 1 := by
      cases a x <;> rfl
    omega

theorem p6e_key {X : Type*} (f : X → Bool) (G : Fin 3 → List (X → Bool)) (n : ℕ)
    (hG : ∀ i, (G i).length = n) (x : X)
    (hx : x ∈ ER (majority (G 0 ++ G 1 ++ G 2)) f) :
    ∃ i : Fin 3, x ∈ ER (majority (G i)) f ∧
      n ≤ 2 * ∑ j ∈ Finset.univ.erase i, (G j).countP (fun h => decide (h x ≠ f x)) := by
  have e : ∀ i : Fin 3, ∑ j ∈ Finset.univ.erase i, (G j).countP (fun h => decide (h x ≠ f x))
      + (G i).countP (fun h => decide (h x ≠ f x)) =
      ∑ j, (G j).countP (fun h => decide (h x ≠ f x)) := fun i =>
    Finset.sum_erase_add _ _ (Finset.mem_univ i)
  simp only [Fin.sum_univ_three] at e
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  have t : ∀ j, (G j).countP (fun h => decide (h x = true)) +
      (G j).countP (fun h => decide (h x = false)) = n := fun j =>
    (p6e_countP_tf (G j) x).trans (hG j)
  have t0 := t 0
  have t1 := t 1
  have t2 := t 2
  have hx' : decide ((G 0 ++ G 1 ++ G 2).countP (fun h => decide (h x = false)) ≤
      (G 0 ++ G 1 ++ G 2).countP (fun h => decide (h x = true))) ≠ f x := hx
  rw [List.countP_append, List.countP_append, List.countP_append, List.countP_append] at hx'
  have mem : ∀ i, x ∈ ER (majority (G i)) f ↔
      decide ((G i).countP (fun h => decide (h x = false)) ≤
        (G i).countP (fun h => decide (h x = true))) ≠ f x := fun i => Iff.rfl
  by_cases hfx : f x = true
  · have hw : ∀ j, (G j).countP (fun h => decide (h x ≠ f x)) =
        (G j).countP (fun h => decide (h x = false)) := fun j =>
      List.countP_congr (fun h _ => by rw [hfx]; cases hh : h x <;> simp)
    rw [hfx] at hx'
    have hx2 : (G 0).countP (fun h => decide (h x = true)) +
        (G 1).countP (fun h => decide (h x = true)) +
        (G 2).countP (fun h => decide (h x = true)) <
        (G 0).countP (fun h => decide (h x = false)) +
        (G 1).countP (fun h => decide (h x = false)) +
        (G 2).countP (fun h => decide (h x = false)) := by simpa using hx'
    simp only [hw] at e0 e1 e2 ⊢
    by_cases c0 : (G 0).countP (fun h => decide (h x = true)) <
        (G 0).countP (fun h => decide (h x = false))
    · exact ⟨0, (mem 0).2 (by rw [hfx]; simpa using c0), by omega⟩
    by_cases c1 : (G 1).countP (fun h => decide (h x = true)) <
        (G 1).countP (fun h => decide (h x = false))
    · exact ⟨1, (mem 1).2 (by rw [hfx]; simpa using c1), by omega⟩
    by_cases c2 : (G 2).countP (fun h => decide (h x = true)) <
        (G 2).countP (fun h => decide (h x = false))
    · exact ⟨2, (mem 2).2 (by rw [hfx]; simpa using c2), by omega⟩
    omega
  · have hfx' : f x = false := by simpa using hfx
    have hw : ∀ j, (G j).countP (fun h => decide (h x ≠ f x)) =
        (G j).countP (fun h => decide (h x = true)) := fun j =>
      List.countP_congr (fun h _ => by rw [hfx']; cases hh : h x <;> simp)
    rw [hfx'] at hx'
    have hx2 : (G 0).countP (fun h => decide (h x = false)) +
        (G 1).countP (fun h => decide (h x = false)) +
        (G 2).countP (fun h => decide (h x = false)) ≤
        (G 0).countP (fun h => decide (h x = true)) +
        (G 1).countP (fun h => decide (h x = true)) +
        (G 2).countP (fun h => decide (h x = true)) := by simpa using hx'
    simp only [hw] at e0 e1 e2 ⊢
    by_cases c0 : (G 0).countP (fun h => decide (h x = false)) ≤
        (G 0).countP (fun h => decide (h x = true))
    · exact ⟨0, (mem 0).2 (by rw [hfx']; simpa using c0), by omega⟩
    by_cases c1 : (G 1).countP (fun h => decide (h x = false)) ≤
        (G 1).countP (fun h => decide (h x = true))
    · exact ⟨1, (mem 1).2 (by rw [hfx']; simpa using c1), by omega⟩
    by_cases c2 : (G 2).countP (fun h => decide (h x = false)) ≤
        (G 2).countP (fun h => decide (h x = true))
    · exact ⟨2, (mem 2).2 (by rw [hfx']; simpa using c2), by omega⟩
    omega

end OptimalPAC.SampleComplexity

open MeasureTheory OptimalPAC.SampleComplexity in
theorem solution {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (f : X → Bool) (hf : Measurable f)
    (G : Fin 3 → List (X → Bool)) (n : ℕ) (hn : 1 ≤ n) (hG : ∀ i, (G i).length = n)
    (hGm : ∀ i, ∀ h ∈ G i, Measurable h) :
    er P (majority (G 0 ++ G 1 ++ G 2)) f ≤
        12 * ((1 / 3 : ℝ) * ∑ i : Fin 3, (1 / (2 * (n : ℝ))) *
          ∑ j ∈ Finset.univ.erase i,
            ((G j).map (fun h => (P (ER (majority (G i)) f ∩ ER h f)).toReal)).sum) ∧
      ∀ B : ℝ, (∀ i j : Fin 3, j ≠ i → ∀ h ∈ G j,
          (P (ER (majority (G i)) f ∩ ER h f)).toReal ≤ B) →
        er P (majority (G 0 ++ G 1 ++ G 2)) f ≤ 12 * B := by
  -- measurability
  have hall : ∀ h ∈ G 0 ++ G 1 ++ G 2, Measurable h := by
    intro h hh
    simp only [List.mem_append] at hh
    rcases hh with (h0 | h1) | h2
    · exact hGm 0 h h0
    · exact hGm 1 h h1
    · exact hGm 2 h h2
  have hE : MeasurableSet (ER (majority (G 0 ++ G 1 ++ G 2)) f) :=
    p6e_measSet_ER (p6e_meas_majority _ hall) hf
  have hEi : ∀ i, MeasurableSet (ER (majority (G i)) f) := fun i =>
    p6e_measSet_ER (p6e_meas_majority _ (hGm i)) hf
  set E := ER (majority (G 0 ++ G 1 ++ G 2)) f with hEdef
  set W : Fin 3 → X → ENNReal := fun j x =>
    (((G j).countP (fun h => decide (h x ≠ f x)) : ℕ) : ENNReal) with hW
  have hWm : ∀ j, Measurable (W j) := fun j =>
    p6e_meas_count (G j) (fun h x => decide (h x ≠ f x))
      (fun h hh => by simpa [ER] using p6e_measSet_ER (hGm j h hh) hf)
  -- pointwise
  have hpt : ∀ x, (n : ENNReal) * E.indicator 1 x ≤
      2 * ∑ i : Fin 3, ∑ j ∈ Finset.univ.erase i, (ER (majority (G i)) f).indicator (W j) x := by
    intro x
    by_cases hx : x ∈ E
    · obtain ⟨i, hxi, hle⟩ := p6e_key f G n hG x hx
      rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
      calc (n : ENNReal) ≤ 2 * ∑ j ∈ Finset.univ.erase i, W j x := by
              simp only [hW]
              exact_mod_cast hle
        _ = 2 * ∑ j ∈ Finset.univ.erase i, (ER (majority (G i)) f).indicator (W j) x := by
              simp [Set.indicator_of_mem hxi]
        _ ≤ _ := by
              gcongr
              exact Finset.single_le_sum
                (f := fun i => ∑ j ∈ Finset.univ.erase i, (ER (majority (G i)) f).indicator (W j) x)
                (fun _ _ => zero_le) (Finset.mem_univ i)
    · simp [Set.indicator_of_notMem hx]
  have hint := lintegral_mono (μ := P) hpt
  rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n), lintegral_indicator_one hE] at hint
  rw [lintegral_const_mul' _ _ (by simp)] at hint
  rw [lintegral_finsetSum _ (fun i _ => Finset.measurable_sum _
    fun j _ => (hWm j).indicator (hEi i))] at hint
  simp_rw [lintegral_finsetSum _ (fun j _ => (hWm j).indicator (hEi _))] at hint
  simp_rw [hW, p6e_lint_eq P f hf _ (hEi _) _ (hGm _)] at hint
  -- convert to reals
  set R : Fin 3 → Fin 3 → ℝ := fun i j =>
    ((G j).map (fun h => (P (ER (majority (G i)) f ∩ ER h f)).toReal)).sum with hR
  have hRe : ∀ i j, R i j =
      (((G j).map (fun h => P (ER (majority (G i)) f ∩ ER h f))).sum).toReal := fun i j =>
    (p6e_sum_toReal P (fun h => ER (majority (G i)) f ∩ ER h f) (G j)).2
  have hfin : ∀ i j,
      (((G j).map (fun h => P (ER (majority (G i)) f ∩ ER h f))).sum) ≠ ⊤ := fun i j =>
    (p6e_sum_toReal P (fun h => ER (majority (G i)) f ∩ ER h f) (G j)).1
  have hreal : (n : ℝ) * er P (majority (G 0 ++ G 1 ++ G 2)) f ≤ 2 * ∑ i : Fin 3, ∑ j ∈ Finset.univ.erase i, R i j := by
    have hne : (2 : ENNReal) * ∑ i : Fin 3, ∑ j ∈ Finset.univ.erase i,
        (((G j).map (fun h => P (ER (majority (G i)) f ∩ ER h f))).sum) ≠ ⊤ := by
      apply ENNReal.mul_ne_top (by simp)
      exact (ENNReal.sum_ne_top).2 fun i _ => (ENNReal.sum_ne_top).2 fun j _ => hfin i j
    have := ENNReal.toReal_mono hne hint
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_sum
      (fun i _ => (ENNReal.sum_ne_top).2 fun j _ => hfin i j)] at this
    simp_rw [ENNReal.toReal_sum (fun j _ => hfin _ j), ← hRe] at this
    rw [ENNReal.toReal_natCast, ENNReal.toReal_ofNat] at this
    exact this
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hmain : er P (majority (G 0 ++ G 1 ++ G 2)) f ≤ 2 / n * ∑ i : Fin 3, ∑ j ∈ Finset.univ.erase i, R i j := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hnpos]
    linarith
  have hrhs : 12 * ((1 / 3 : ℝ) * ∑ i : Fin 3, (1 / (2 * (n : ℝ))) *
          ∑ j ∈ Finset.univ.erase i, R i j) =
      2 / n * ∑ i : Fin 3, ∑ j ∈ Finset.univ.erase i, R i j := by
    rw [← Finset.mul_sum]
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · rw [hrhs]; exact hmain
  · intro B hB
    have hRB : ∀ i j, j ≠ i → R i j ≤ n * B := by
      intro i j hji
      have := List.sum_le_card_nsmul
        ((G j).map (fun h => (P (ER (majority (G i)) f ∩ ER h f)).toReal)) B (by
          intro y hy
          obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hy
          exact hB i j hji h hh)
      simpa [hR, hG, nsmul_eq_mul] using this
    have hQ : ∑ i : Fin 3, ∑ j ∈ Finset.univ.erase i, R i j ≤ 6 * (n * B) := by
      calc ∑ i : Fin 3, ∑ j ∈ Finset.univ.erase i, R i j
          ≤ ∑ i : Fin 3, ∑ j ∈ Finset.univ.erase i, (n * B : ℝ) := by
            apply Finset.sum_le_sum; intro i _
            apply Finset.sum_le_sum; intro j hj
            exact hRB i j (Finset.ne_of_mem_erase hj)
        _ = 6 * (n * B) := by
            simp [Finset.sum_const, Finset.card_erase_of_mem]
            ring
    calc er P (majority (G 0 ++ G 1 ++ G 2)) f ≤ 2 / n * ∑ i : Fin 3, ∑ j ∈ Finset.univ.erase i, R i j := hmain
      _ ≤ 2 / n * (6 * (n * B)) := by gcongr
      _ = 12 * B := by field_simp; ring
