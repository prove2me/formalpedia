-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.charFun_marginal_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:36:00.547194+00:00
-- url     : https://prove2.me/submissions/af3b6b2f-39e1-4158-87a6-6bd65b4e6e36

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_indepFun_increment
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_identDistrib_increment
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_charFun_marginal_zero
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_tendsto_charFun_marginal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

/-- When `X 0 = 0`, the increment from `0` to `t` equals `X t`. -/
private theorem leanlevy_chat20_incr_zero_eq
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {X : ℝ≥0 → Ω → E} (h0 : X 0 = fun _ => 0) (t : ℝ≥0) :
    increment X 0 t = X t := by
  ext ω; show X t ω - X 0 ω = X t ω
  rw [show X 0 ω = 0 from congr_fun h0 ω, sub_zero]

/-- Multiplicativity: `charFun(X(s+k)) = charFun(X(s)) * charFun(X(k))`. -/
private theorem leanlevy_chat20_charFun_mul
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) (s k : ℝ≥0) (ξ : E) :
    charFun (μ.map (X (s + k))) ξ = charFun (μ.map (X s)) ξ * charFun (μ.map (X k)) ξ := by
  have hdecomp : X (s + k) = X s + increment X s (s + k) := by
    ext ω
    change X (s + k) ω = X s ω + (X (s + k) ω - X s ω)
    abel
  have hind : IndepFun (X s) (increment X s (s + k)) μ := by
    have := h.indepFun_increment (s := 0) (t := s) (u := s + k) (zero_le) le_self_add
    rwa [leanlevy_chat20_incr_zero_eq h.start_zero] at this
  have hmeas_inc : Measurable (increment X s (s + k)) := by
    change Measurable (fun ω => X (s + k) ω - X s ω)
    exact (hX (s + k)).sub (hX s)
  have hconv := hind.map_add_eq_map_conv_map₀
    (hX s).aemeasurable hmeas_inc.aemeasurable
  rw [hdecomp, hconv, charFun_conv]
  have hstat := (h.identDistrib_increment s k).map_eq
  rw [leanlevy_chat20_incr_zero_eq h.start_zero] at hstat
  rw [hstat]

/-- Non-vanishing: `charFun(μ.map(X t)) ξ ≠ 0` for all `t` and `ξ`.
Halving argument: if `φ(t) = 0` then `φ(t/2^n) = 0` for all n, but `φ(t/2^n) → φ(0) = 1`. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) (t : ℝ≥0) (ξ : E) :
    charFun (μ.map (X t)) ξ ≠ 0 := by
  intro habs
  have key : ∀ n : ℕ, charFun (μ.map (X (t / (2 ^ n : ℝ≥0)))) ξ = 0 := by
    intro n; induction n with
    | zero =>
      have : t / (2 ^ 0 : ℝ≥0) = t := by exact div_one t
      rw [this]; exact habs
    | succ n ih =>
      have hsplit : t / (2 ^ n : ℝ≥0) =
          t / (2 ^ (n + 1) : ℝ≥0) + t / (2 ^ (n + 1) : ℝ≥0) := by
        have h2n : (2 : ℝ≥0) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by positivity)
        rw [← add_div, ← two_mul, show (2 : ℝ≥0) ^ (n + 1) = 2 * 2 ^ n from by ring]
        exact (mul_div_mul_left _ _ (by positivity : (2 : ℝ≥0) ≠ 0)).symm
      rw [hsplit, leanlevy_chat20_charFun_mul h hX] at ih
      exact mul_self_eq_zero.mp ih
  have htend : Tendsto (fun n : ℕ => t / (2 ^ n : ℝ≥0)) atTop (𝓝 0) := by
    rw [NNReal.tendsto_coe.symm]
    simp only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_zero]
    exact tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hctslim : Tendsto (fun n => charFun (μ.map (X (t / (2 ^ n : ℝ≥0)))) ξ)
      atTop (𝓝 (charFun (μ.map (X 0)) ξ)) := by
    have hrc := h.tendsto_charFun_marginal hX 0 ξ
    apply hrc.comp
    rw [tendsto_nhdsWithin_iff]
    exact ⟨htend, Eventually.of_forall fun _ => Set.mem_Ici.mpr (zero_le)⟩
  rw [h.charFun_marginal_zero ξ] at hctslim
  have : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 1) := by
    convert hctslim using 1; ext n; exact (key n).symm
  have := tendsto_nhds_unique this tendsto_const_nhds
  exact one_ne_zero this
