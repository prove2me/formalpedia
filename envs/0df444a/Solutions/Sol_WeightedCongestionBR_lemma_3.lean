-- Prove2me | solution 1 for WeightedCongestionBR.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:52:25.974792+00:00
-- url     : https://prove2.me/submissions/c7dc7cf3-6d3b-4fc9-bf4c-f57550f7d24a

import Mathlib
import Definitions.Def_WeightedCongestionBR_genGolden
import Definitions.Def_DirectTradeCoffee_lambertW
set_option autoImplicit false
open scoped NNReal

open WeightedCongestionBR in
theorem solution (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    genGolden d ρ ≤ (d : ℝ) / DirectTradeCoffee.lambertW ((d : ℝ) / ρ) := by
  have hρ0 : 0 < ρ := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hc : 0 < (d : ℝ) / ρ := div_pos hd0 hρ0
  set c := (d : ℝ) / ρ with hcdef
  have hex : ∃ w : ℝ, 0 ≤ w ∧ w * Real.exp w = c := by
    have hcont : ContinuousOn (fun w : ℝ => w * Real.exp w) (Set.Icc 0 c) :=
      (continuous_id.mul Real.continuous_exp).continuousOn
    have hmem : c ∈ Set.Icc ((fun w : ℝ => w * Real.exp w) 0) ((fun w : ℝ => w * Real.exp w) c) := by
      simp only [zero_mul, Set.mem_Icc]
      refine ⟨hc.le, ?_⟩
      have : 1 ≤ Real.exp c := Real.one_le_exp hc.le
      nlinarith
    obtain ⟨w, hw, hw'⟩ := intermediate_value_Icc hc.le hcont hmem
    exact ⟨w, hw.1, hw'⟩
  unfold DirectTradeCoffee.lambertW
  rw [dif_pos hex]
  obtain ⟨hw0, hwe⟩ := Classical.choose_spec hex
  set w0 := Classical.choose hex with hw0def
  have hw0pos : 0 < w0 := by
    rcases lt_or_eq_of_le hw0 with h | h
    · exact h
    · rw [← h, zero_mul] at hwe; linarith
  unfold genGolden
  apply Real.sSup_le _ (div_pos hd0 hw0pos).le
  rintro x ⟨hx, hxe⟩
  -- x ≤ ρ * exp (d / x)
  have h1 : (1 + 1 / x) ≤ Real.exp (1 / x) := by
    have := Real.add_one_le_exp (1 / x); linarith
  have h2 : (1 + 1 / x) ^ d ≤ Real.exp (d / x) := by
    calc (1 + 1 / x) ^ d ≤ Real.exp (1 / x) ^ d :=
          pow_le_pow_left₀ (by positivity) h1 d
      _ = Real.exp (d / x) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
  have h3 : (x + 1) ^ d = x ^ d * (1 + 1 / x) ^ d := by
    rw [← mul_pow]; congr 1; field_simp
  have hxd : 0 < x ^ d := pow_pos hx d
  have h4 : x ≤ ρ * Real.exp (d / x) := by
    have : x ^ d * x = ρ * (x ^ d * (1 + 1 / x) ^ d) := by
      rw [← h3, hxe]; ring
    have h5 : x ^ d * x ≤ x ^ d * (ρ * Real.exp (d / x)) := by
      rw [this]
      have := mul_le_mul_of_nonneg_left h2 hxd.le
      nlinarith
    exact le_of_mul_le_mul_left h5 hxd
  -- (d/x) exp(d/x) ≥ c
  set u := (d : ℝ) / x with hu
  have hupos : 0 < u := div_pos hd0 hx
  have h6 : c ≤ u * Real.exp u := by
    rw [hcdef, div_le_iff₀ hρ0]
    have : u * x = d := by rw [hu]; field_simp
    calc (d : ℝ) = u * x := this.symm
      _ ≤ u * (ρ * Real.exp u) := mul_le_mul_of_nonneg_left h4 hupos.le
      _ = u * Real.exp u * ρ := by ring
  have h7 : w0 ≤ u := by
    by_contra hlt
    push_neg at hlt
    have : u * Real.exp u < w0 * Real.exp w0 :=
      mul_lt_mul hlt (Real.exp_le_exp.2 hlt.le) (Real.exp_pos _) hw0
    linarith
  rw [le_div_iff₀ hw0pos]
  calc x * w0 ≤ x * u := mul_le_mul_of_nonneg_left h7 hx.le
    _ = d := by rw [hu]; field_simp
