-- Prove2me | solution 1 for ScheduledQueue.Stability.sufficiency
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T21:56:43.954486+00:00
-- url     : https://prove2.me/submissions/7fdf1e9b-924d-4480-b621-943e575ff4bf

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed
import Theorems.Thm_ScheduledQueue_Stability_upper_decomposition
import Theorems.Thm_ScheduledQueue_Stability_beta2_bounded
import Theorems.Thm_ScheduledQueue_Stability_beta1_le_gamma1

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

namespace SQSuffAux

theorem bc_eventually_lt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : ℝ} (hh : 0 < h) {W : Ω → ℝ} (hW : Integrable W P)
    (Z : ℕ → Ω → ℝ) (hZ : ∀ n, IdentDistrib (Z n) W P P) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, Z n ω < n * h := by
  set X : Ω → ℝ := fun ω => max (W ω / h + 1) 0
  have hXint : Integrable X P := ((hW.div_const h).add (integrable_const 1)).pos_part
  have hX0 : 0 ≤ X := fun ω => le_max_right _ _
  have hfin : (∑' n : ℕ, P {ω | X ω ∈ Ioi (n : ℝ)}) < ∞ := by
    let _ : MeasureSpace Ω := ⟨P⟩
    exact tsum_prob_mem_Ioi_lt_top hXint hX0
  have hle : ∀ n : ℕ, P {ω | (n : ℝ) * h ≤ Z n ω} ≤ P {ω | X ω ∈ Ioi (n : ℝ)} := by
    intro n
    have e : P {ω | (n : ℝ) * h ≤ Z n ω} = P {ω | (n : ℝ) * h ≤ W ω} :=
      (hZ n).measure_mem_eq (s := {x | (n : ℝ) * h ≤ x}) (measurableSet_le measurable_const measurable_id)
    rw [e]
    apply measure_mono
    intro ω hω
    simp only [mem_setOf_eq, mem_Ioi, X] at hω ⊢
    have : (n : ℝ) ≤ W ω / h := by rw [le_div_iff₀ hh]; linarith
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hsum : (∑' n : ℕ, P {ω | (n : ℝ) * h ≤ Z n ω}) ≠ ∞ :=
    (lt_of_le_of_lt (ENNReal.tsum_le_tsum hle) hfin).ne
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  simpa using hn

theorem encard_lt_top_of_eventually {S : Set ℤ} {p : ℕ → Prop}
    (hS : ∀ j ∈ S, 1 ≤ j ∧ p j.toNat) (hev : ∀ᶠ n : ℕ in atTop, ¬ p n) : S.encard < ⊤ := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hsub : S ⊆ (Finset.Icc (1 : ℤ) N : Set ℤ) := by
    intro j hj
    obtain ⟨h1, h2⟩ := hS j hj
    simp only [Finset.coe_Icc, mem_Icc]
    refine ⟨h1, ?_⟩
    by_contra hc
    exact hN j.toNat (by omega) h2
  exact ((Finset.finite_toSet _).subset hsub).encard_lt_top

end SQSuffAux

open ScheduledQueue.Stability SQSuffAux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledInput P ξ U) :
    (∃ c : ℝ, ∀ᵐ ω ∂P, ξ 0 ω ≤ c) →
      ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ s : ℝ, 0 ≤ s → revCount h ξ U s ω ≠ ⊤ ∧ Lam h ξ U s ω - s ≤ C := by
  rintro ⟨c0, hc0⟩
  set c : ℝ := max c0 0
  have hc : 0 ≤ c := le_max_right _ _
  -- all perturbations are bounded by `c`
  have hall : ∀ᵐ ω ∂P, ∀ j, ξ j ω ≤ c := by
    rw [ae_all_iff]
    intro j
    have h0 : ∀ᵐ ω ∂P, ξ 0 ω ≤ c := by
      filter_upwards [hc0] with ω hω using hω.trans (le_max_left _ _)
    exact (hin.identDistrib j).symm.ae_mem_snd (t := Iic c) measurableSet_Iic h0
  -- `U ∈ [0,1]` almost surely
  have hU : ∀ᵐ ω ∂P, U ω ∈ Icc (0 : ℝ) 1 := by
    rw [hin.uniform.ae_iff (p := fun x => x ∈ Icc (0 : ℝ) 1) measurableSet_Icc.mem]
    exact ae_restrict_mem measurableSet_Icc
  -- `Γ₁ < ∞` almost surely
  have hG : ∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop, -ξ (-(m : ℤ)) ω + h < m * h := by
    apply bc_eventually_lt hh (W := fun ω => -ξ 0 ω + h)
      (hin.integrable.neg.add (integrable_const _))
    intro m
    exact (hin.identDistrib _).comp (u := fun x => -x + h) (by fun_prop)
  filter_upwards [hall, hU, hG] with ω hallω hUω hGω
  have hg1 : gamma1 h ξ ω < ⊤ := by
    apply encard_lt_top_of_eventually (p := fun m : ℕ =>
      (((m : ℤ) : ℝ) - 1) * h < -ξ (-(m : ℤ)) ω) _
    · filter_upwards [hGω] with m hm
      push Not; push_cast; linarith
    · rintro j ⟨hj1, hj2⟩
      refine ⟨hj1, ?_⟩
      show _
      rwa [Int.toNat_of_nonneg (by omega)]
  obtain ⟨g, hg⟩ := ENat.ne_top_iff_exists.1 hg1.ne
  set m : ℕ := ⌊c / h⌋₊
  refine ⟨h * (g + m + 2), fun s hs => ?_⟩
  set k : ℕ := ⌊s / h⌋₊
  have hb1 : beta1 h ξ U s ω ≤ g := hg ▸ (beta1_le_gamma1 P h hh ξ U hin).1 ω hUω s
  have hb2 : beta2 h ξ U s ω ≤ ((m + 1 : ℕ) : ℕ∞) := beta2_bounded h hh ξ U ω c hc hallω hUω s hs
  have hR : revCount h ξ U s ω ≤ ((g + (k + 1) + (m + 1) : ℕ) : ℕ∞) := by
    calc revCount h ξ U s ω ≤ beta1 h ξ U s ω + ((k + 1 : ℕ) : ℕ∞) + beta2 h ξ U s ω :=
          upper_decomposition h hh ξ U ω s hs
      _ ≤ (g : ℕ∞) + ((k + 1 : ℕ) : ℕ∞) + ((m + 1 : ℕ) : ℕ∞) := by gcongr
      _ = _ := by push_cast; ring
  refine ⟨ne_top_of_le_ne_top (ENat.natCast_ne_top _) hR, ?_⟩
  have hnat : (revCount h ξ U s ω).toNat ≤ g + (k + 1) + (m + 1) := ENat.toNat_le_of_le_natCast hR
  have hkle : (k : ℝ) * h ≤ s := by
    have := Nat.floor_le (div_nonneg hs hh.le) (a := s / h)
    rw [le_div_iff₀ hh] at this; exact this
  have hnatR : ((revCount h ξ U s ω).toNat : ℝ) ≤ g + (k + 1) + (m + 1) := by exact_mod_cast hnat
  simp only [Lam]
  nlinarith
