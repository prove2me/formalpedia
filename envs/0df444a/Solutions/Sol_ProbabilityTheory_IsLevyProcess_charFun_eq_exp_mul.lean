-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.charFun_eq_exp_mul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:22:15.068316+00:00
-- url     : https://prove2.me/submissions/4bd36100-17ee-4b68-be2e-2ca467c61543

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_charFun_marginal_zero
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_tendsto_charFun_marginal
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_charFun_marginal_ne_zero
import Theorems.Thm_ProbabilityTheory_leanlevy_chat22_charFun_marginal_mul
import Theorems.Thm_ProbabilityTheory_leanlevy_chat22_semigroup_log_pow
import Theorems.Thm_ProbabilityTheory_leanlevy_chat22_semigroup_log_constant
import Theorems.Thm_ProbabilityTheory_leanlevy_chat22_semigroup_rat_exp
import Theorems.Thm_ProbabilityTheory_leanlevy_chat22_semigroup_extend_exp
import Theorems.Thm_ProbabilityTheory_leanlevy_chat22_semigroup_log_slope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

/-- The original source's six analytic phases, assembled from their verified
separate source-exact reductions. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t))
    (t : ℝ≥0) (ξ : E) :
    charFun (μ.map (X t)) ξ =
      exp (↑(t : ℝ) * h.charExponent ξ) := by
  set φ : ℝ≥0 → ℂ := fun s => charFun (μ.map (X s)) ξ with hφ_def
  have hφ0 : φ 0 = 1 := h.charFun_marginal_zero ξ
  have hφ_ne : ∀ s, φ s ≠ 0 :=
    fun s => h.charFun_marginal_ne_zero hX s ξ
  have hφ_mul : ∀ s k, φ (s + k) = φ s * φ k :=
    fun s k => leanlevy_chat22_charFun_marginal_mul h hX s k ξ
  have hφ_pow : ∀ (n : ℕ) (s : ℝ≥0),
      φ ((n : ℝ≥0) * s) = (φ s) ^ n := by
    intro n
    induction n with
    | zero => intro s; simp [hφ0]
    | succ n ih =>
      intro s
      rw [show ((n + 1 : ℕ) : ℝ≥0) * s =
        s + (n : ℝ≥0) * s from by push_cast; ring]
      rw [hφ_mul, ih, pow_succ, mul_comm]
  have hφ_rat : ∀ (k n : ℕ),
      φ ((k : ℝ≥0) / (n : ℝ≥0)) =
        (φ (1 / (n : ℝ≥0))) ^ k := by
    intro k n
    simpa [div_eq_mul_inv] using (hφ_pow k (1 / (n : ℝ≥0)))
  have hIci_eq : 𝓝[≥] (0 : ℝ≥0) = 𝓝 0 := by
    rw [show Set.Ici (0 : ℝ≥0) = Set.univ from
      Set.eq_univ_of_forall (fun _ => Set.mem_Ici.mpr zero_le), nhdsWithin_univ]
  have hφ_tendsto0 : Tendsto φ (𝓝 (0 : ℝ≥0)) (𝓝 1) := by
    rw [← hIci_eq, ← hφ0]
    exact h.tendsto_charFun_marginal hX 0 ξ
  obtain ⟨δ, hδ_pos, hlog_pow⟩ :=
    leanlevy_chat22_semigroup_log_pow φ hφ0 hφ_ne hφ_mul hφ_tendsto0
  obtain ⟨c, hconst⟩ :=
    leanlevy_chat22_semigroup_log_constant φ δ hδ_pos hlog_pow
  obtain ⟨N, hN_pos, hN_small⟩ :
      ∃ N : ℕ, 0 < N ∧ (1 : ℝ≥0) / (N : ℝ≥0) < δ := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((δ : ℝ)⁻¹)
    have hn_pos : 0 < n := by
      exact_mod_cast lt_trans (inv_pos.mpr
        (by positivity : (0 : ℝ) < δ)) hn
    refine ⟨n, hn_pos, ?_⟩
    rw [show (1 : ℝ≥0) / (n : ℝ≥0) < δ ↔
      ((1 : ℝ) / (n : ℝ) < (δ : ℝ)) from by
        rw [← NNReal.coe_lt_coe]; simp]
    rw [one_div]
    calc (↑n : ℝ)⁻¹ = 1 / ↑n := (one_div _).symm
      _ < 1 / (δ : ℝ)⁻¹ :=
        one_div_lt_one_div_of_lt
          (inv_pos.mpr (by positivity : (0 : ℝ) < ↑δ)) hn
      _ = ↑δ := by rw [one_div, inv_inv]
  have hrat_exp := leanlevy_chat22_semigroup_rat_exp φ δ c N
    hN_pos hN_small hφ_ne hφ_pow hφ_rat hconst
  have hext : ∀ s : ℝ≥0, φ s = exp (c * ↑(s : ℝ)) :=
    leanlevy_chat22_semigroup_extend_exp φ c
      (fun s => h.tendsto_charFun_marginal hX s ξ) hrat_exp
  have hce : h.charExponent ξ = c := by
    simpa only [IsLevyProcess.charExponent, hφ_def] using
      (leanlevy_chat22_semigroup_log_slope φ c hext)
  change φ t = exp (↑(t : ℝ) * h.charExponent ξ)
  rw [hce, mul_comm, hext t]
