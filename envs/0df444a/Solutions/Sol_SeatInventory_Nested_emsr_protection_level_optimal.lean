-- Prove2me | solution 1 for SeatInventory.Nested.emsr_protection_level_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T13:42:12.543992+00:00
-- url     : https://prove2.me/submissions/620ede76-ca6c-4844-b5f8-247323e86ee4

import Mathlib
import Definitions.Def_SeatInventory_Nested_Model

set_option autoImplicit false

namespace PE6005eb5

open SeatInventory.Nested

lemma step_pt (f₁ f₂ : ℝ) (C S a b : ℕ) (hS : S + 1 ≤ C) :
    nestedRevenue f₁ f₂ C (S + 1) a b - nestedRevenue f₁ f₂ C S a b =
      f₁ * (if S + 1 ≤ a ∧ C - S ≤ b then (1 : ℝ) else 0) -
        f₂ * (if C - S ≤ b then (1 : ℝ) else 0) := by
  unfold nestedRevenue
  by_cases hb : C - S ≤ b
  · by_cases ha : S + 1 ≤ a
    · rw [if_pos ⟨ha, hb⟩, if_pos hb]
      have hx : min b (C - (S + 1)) + 1 = min b (C - S) := by omega
      have hy : min a (C - min b (C - (S + 1))) = min a (C - min b (C - S)) + 1 := by omega
      have hx' : ((min b (C - (S + 1)) : ℕ) : ℝ) + 1 = ((min b (C - S) : ℕ) : ℝ) := by
        exact_mod_cast hx
      have hy' : ((min a (C - min b (C - (S + 1))) : ℕ) : ℝ)
          = ((min a (C - min b (C - S)) : ℕ) : ℝ) + 1 := by exact_mod_cast hy
      linear_combination f₂ * hx' + f₁ * hy'
    · rw [if_neg (fun h => ha h.1), if_pos hb]
      have hx : min b (C - (S + 1)) + 1 = min b (C - S) := by omega
      have hy : min a (C - min b (C - (S + 1))) = min a (C - min b (C - S)) := by omega
      have hx' : ((min b (C - (S + 1)) : ℕ) : ℝ) + 1 = ((min b (C - S) : ℕ) : ℝ) := by
        exact_mod_cast hx
      have hy' : ((min a (C - min b (C - (S + 1))) : ℕ) : ℝ)
          = ((min a (C - min b (C - S)) : ℕ) : ℝ) := by exact_mod_cast hy
      linear_combination f₂ * hx' + f₁ * hy'
  · rw [if_neg (fun h => hb h.2), if_neg hb]
    have hx : min b (C - (S + 1)) = min b (C - S) := by omega
    have hy : min a (C - min b (C - (S + 1))) = min a (C - min b (C - S)) := by omega
    have hx' : ((min b (C - (S + 1)) : ℕ) : ℝ) = ((min b (C - S) : ℕ) : ℝ) := by
      exact_mod_cast hx
    have hy' : ((min a (C - min b (C - (S + 1))) : ℕ) : ℝ)
        = ((min a (C - min b (C - S)) : ℕ) : ℝ) := by exact_mod_cast hy
    linear_combination f₂ * hx' + f₁ * hy'

lemma absb (f : ℝ) (n C : ℕ) (h : n ≤ C) : ‖f * (n : ℝ)‖ ≤ |f| * C := by
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
  have : (n : ℝ) ≤ C := by exact_mod_cast h
  exact mul_le_mul_of_nonneg_left this (abs_nonneg f)

lemma bound_nested (f₁ f₂ : ℝ) (C S a b : ℕ) :
    ‖nestedRevenue f₁ f₂ C S a b‖ ≤ |f₂| * C + |f₁| * C := by
  unfold nestedRevenue
  refine (norm_add_le _ _).trans (add_le_add (absb _ _ _ ?_) (absb _ _ _ ?_)) <;> omega

open MeasureTheory ProbabilityTheory in
lemma step_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (r₁ r₂ : Ω → ℕ) (hr₁ : Measurable r₁) (hr₂ : Measurable r₂)
    (hind : IndepFun r₁ r₂ μ) (f₁ f₂ : ℝ) (C S : ℕ) (hS : S + 1 ≤ C) :
    expectedNestedRevenue μ r₁ r₂ f₁ f₂ C (S + 1) - expectedNestedRevenue μ r₁ r₂ f₁ f₂ C S =
      μ.real {ω | C - S ≤ r₂ ω} * (f₁ * tailProb μ r₁ (S + 1) - f₂) := by
  have hm : Measurable (fun ω => (r₁ ω, r₂ ω)) := hr₁.prodMk hr₂
  have intN : ∀ T, Integrable (fun ω => nestedRevenue f₁ f₂ C T (r₁ ω) (r₂ ω)) μ := by
    intro T
    refine Integrable.of_bound ?_ (|f₂| * C + |f₁| * C)
      (ae_of_all _ fun ω => bound_nested f₁ f₂ C T (r₁ ω) (r₂ ω))
    exact ((measurable_of_countable
      (fun p : ℕ × ℕ => nestedRevenue f₁ f₂ C T p.1 p.2)).comp hm).aestronglyMeasurable
  set A : Set Ω := {ω | S + 1 ≤ r₁ ω} with hA
  set B : Set Ω := {ω | C - S ≤ r₂ ω} with hB
  have hAm : MeasurableSet A := hr₁ (MeasurableSet.of_discrete (s := {n : ℕ | S + 1 ≤ n}))
  have hBm : MeasurableSet B := hr₂ (MeasurableSet.of_discrete (s := {n : ℕ | C - S ≤ n}))
  have hfun : (fun ω => nestedRevenue f₁ f₂ C (S + 1) (r₁ ω) (r₂ ω) -
      nestedRevenue f₁ f₂ C S (r₁ ω) (r₂ ω)) =
      fun ω => f₁ * (A ∩ B).indicator (fun _ => (1 : ℝ)) ω -
        f₂ * B.indicator (fun _ => (1 : ℝ)) ω := by
    funext ω
    rw [step_pt f₁ f₂ C S (r₁ ω) (r₂ ω) hS]
    by_cases ha : S + 1 ≤ r₁ ω <;> by_cases hb : C - S ≤ r₂ ω
    · have h1 : ω ∈ A ∩ B := by rw [hA, hB]; exact ⟨ha, hb⟩
      have h2 : ω ∈ B := by rw [hB]; exact hb
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, if_pos ⟨ha, hb⟩, if_pos hb]
    · have h1 : ω ∉ A ∩ B := by rw [hA, hB]; exact fun h => hb h.2
      have h2 : ω ∉ B := by rw [hB]; exact hb
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, if_neg (fun h => hb h.2),
        if_neg hb]
    · have h1 : ω ∉ A ∩ B := by rw [hA, hB]; exact fun h => ha h.1
      have h2 : ω ∈ B := by rw [hB]; exact hb
      rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2, if_neg (fun h => ha h.1),
        if_pos hb]
    · have h1 : ω ∉ A ∩ B := by rw [hA, hB]; exact fun h => hb h.2
      have h2 : ω ∉ B := by rw [hB]; exact hb
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, if_neg (fun h => hb h.2),
        if_neg hb]
  have hdiff : expectedNestedRevenue μ r₁ r₂ f₁ f₂ C (S + 1) -
      expectedNestedRevenue μ r₁ r₂ f₁ f₂ C S = f₁ * μ.real (A ∩ B) - f₂ * μ.real B := by
    unfold expectedNestedRevenue
    rw [← integral_sub (intN _) (intN _), hfun,
      integral_sub (((integrable_const (1 : ℝ)).indicator (hAm.inter hBm)).const_mul f₁)
        (((integrable_const (1 : ℝ)).indicator hBm).const_mul f₂),
      integral_const_mul, integral_const_mul, integral_indicator_const _ (hAm.inter hBm),
      integral_indicator_const _ hBm]
    simp
  have hind' : μ.real (A ∩ B) = μ.real A * μ.real B := by
    have := hind.measure_inter_preimage_eq_mul {n : ℕ | S + 1 ≤ n} {n : ℕ | C - S ≤ n}
      (MeasurableSet.of_discrete) (MeasurableSet.of_discrete)
    simp only [measureReal_def]
    rw [show A ∩ B = r₁ ⁻¹' {n : ℕ | S + 1 ≤ n} ∩ r₂ ⁻¹' {n : ℕ | C - S ≤ n} from rfl, this,
      ENNReal.toReal_mul]
    rfl
  have htail : tailProb μ r₁ (S + 1) = μ.real A := rfl
  rw [hdiff, hind', htail]
  ring

open MeasureTheory ProbabilityTheory in
lemma tail_anti {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → ℕ) {a b : ℕ} (h : a ≤ b) : tailProb μ r b ≤ tailProb μ r a := by
  unfold tailProb
  exact measureReal_mono (fun ω (hω : b ≤ r ω) => show a ≤ r ω by omega)

open MeasureTheory ProbabilityTheory in
lemma tail_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → ℕ) : tailProb μ r 0 = 1 := by
  unfold tailProb
  simp

end PE6005eb5

open MeasureTheory ProbabilityTheory SeatInventory.Nested in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (r₁ r₂ : Ω → ℕ) (hr₁ : Measurable r₁) (hr₂ : Measurable r₂)
    (hind : IndepFun r₁ r₂ μ) (f₁ f₂ : ℝ) (hf₂ : 0 ≤ f₂) (hf : f₂ ≤ f₁) (C : ℕ) :
    emsrProtectionLevel μ r₁ f₁ f₂ C ≤ C ∧
      ∀ S ≤ C, expectedNestedRevenue μ r₁ r₂ f₁ f₂ C S ≤
        expectedNestedRevenue μ r₁ r₂ f₁ f₂ C (emsrProtectionLevel μ r₁ f₁ f₂ C) := by
  set P := emsrProtectionLevel μ r₁ f₁ f₂ C with hP
  set F := (Finset.range (C + 1)).filter (fun S => f₂ ≤ emsr μ r₁ f₁ S) with hF
  have hPF : P = F.sup id := rfl
  have hPC : P ≤ C := by
    rw [hPF]
    apply Finset.sup_le
    intro b hb
    rw [hF, Finset.mem_filter, Finset.mem_range] at hb
    simp only [id]
    omega
  have h0 : (0 : ℕ) ∈ F := by
    rw [hF, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    unfold emsr
    rw [PE6005eb5.tail_zero]
    linarith
  have hPmem : P ∈ F := by
    obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup F ⟨0, h0⟩ id
    rw [hPF, he]
    exact hi
  have hPge : f₂ ≤ f₁ * tailProb μ r₁ P := by
    rw [hF, Finset.mem_filter] at hPmem
    exact hPmem.2
  have hf1 : 0 ≤ f₁ := le_trans hf₂ hf
  have stepsign : ∀ k, k + 1 ≤ C → 0 ≤ μ.real {ω | C - k ≤ r₂ ω} := fun _ _ => measureReal_nonneg
  -- monotone part: k < P
  have up : ∀ d, ∀ n, n + d = P → expectedNestedRevenue μ r₁ r₂ f₁ f₂ C n ≤
      expectedNestedRevenue μ r₁ r₂ f₁ f₂ C P := by
    intro d
    induction d with
    | zero => intro n hn; rw [show n = P by omega]
    | succ d ih =>
      intro n hn
      have hstep := PE6005eb5.step_eq μ r₁ r₂ hr₁ hr₂ hind f₁ f₂ C n (by omega)
      have ht : f₂ ≤ f₁ * tailProb μ r₁ (n + 1) :=
        hPge.trans (mul_le_mul_of_nonneg_left (PE6005eb5.tail_anti μ r₁ (by omega)) hf1)
      have hnn : 0 ≤ μ.real {ω | C - n ≤ r₂ ω} * (f₁ * tailProb μ r₁ (n + 1) - f₂) :=
        mul_nonneg measureReal_nonneg (by linarith)
      have := ih (n + 1) (by omega)
      linarith
  have down : ∀ n, P ≤ n → n ≤ C →
      expectedNestedRevenue μ r₁ r₂ f₁ f₂ C n ≤ expectedNestedRevenue μ r₁ r₂ f₁ f₂ C P := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ k hk ih =>
      intro hk1
      have hlt : f₁ * tailProb μ r₁ (k + 1) < f₂ := by
        by_contra hcon0
        have hcon := not_lt.mp hcon0
        have hle : k + 1 ≤ P := by
          rw [hPF]
          apply Finset.le_sup (f := id)
          rw [hF, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hcon⟩
        omega
      have hstep := PE6005eb5.step_eq μ r₁ r₂ hr₁ hr₂ hind f₁ f₂ C k hk1
      have hnp : μ.real {ω | C - k ≤ r₂ ω} * (f₁ * tailProb μ r₁ (k + 1) - f₂) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos measureReal_nonneg (by linarith)
      have := ih (by omega)
      linarith
  refine ⟨hPC, fun S hS => ?_⟩
  rcases le_total S P with h | h
  · exact up (P - S) S (by omega)
  · exact down S h hS
