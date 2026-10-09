-- Prove2me | solution 1 for SWPort.Davenport.logDeriv_LFunction_region_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T20:33:44.0185+00:00
-- url     : https://prove2.me/submissions/77f08902-9e91-4862-bf52-1185c34eaae0

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_SWPort_001
import Theorems.Thm_SWPort_Davenport_logDeriv_LFunction_partial_fraction

section
-- module Solutions.Artin.SW.Thm.Davenport_LFunction_zero_one_sub_of_isQuadratic
namespace SWPort
/-! Ported from prove2.me: `Davenport.LFunction_zero_one_sub_of_isQuadratic` (64fb2bde-6d05-40d6-a9f1-4dd950241fc5, statement by alya); proof = accepted direct submission 921768ab-6536-4938-b7d9-e354d98ac4e9 by alya. -/















open Finset DirichletCharacter Vino

namespace SolAux

/-- The Euler-type correction factor relating `L(s, χ)` to `L(s, χ*)` is nonzero when
`0 < re s`, since each factor `1 - ψ p * p ^ (-s)` has `‖ψ p * p ^ (-s)‖ < 1`. -/
private lemma prod_factor_ne_zero {M : ℕ} (N : ℕ) (ψ : DirichletCharacter ℂ M) {s : ℂ}
    (hs : 0 < s.re) :
    ∏ p ∈ N.primeFactors, (1 - ψ p * (p : ℂ) ^ (-s)) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have hp0 : 0 < p := Nat.pos_of_mem_primeFactors hp
  have hnorm : ‖ψ (p : ZMod M) * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp0]
    have hr : (0 : ℝ) ≤ (p : ℝ) ^ (-s).re :=
      (Real.rpow_pos_of_pos (by linarith) _).le
    have h1 : ‖ψ (p : ZMod M)‖ * (p : ℝ) ^ (-s).re ≤ 1 * (p : ℝ) ^ (-s).re :=
      mul_le_mul_of_nonneg_right (ψ.norm_le_one _) hr
    have h2 : (p : ℝ) ^ (-s).re < 1 := by
      refine Real.rpow_lt_one_of_one_lt_of_neg hp1 ?_
      simpa using hs
    calc ‖ψ (p : ZMod M)‖ * (p : ℝ) ^ (-s).re
        ≤ 1 * (p : ℝ) ^ (-s).re := h1
      _ = (p : ℝ) ^ (-s).re := one_mul _
      _ < 1 := h2
  intro hzero
  rw [sub_eq_zero] at hzero
  rw [← hzero, norm_one] at hnorm
  exact lt_irrefl _ hnorm

/-- The archimedean gamma factor is nonzero in the right half plane `0 < re s`. -/
private lemma gammaFactor_ne_zero {N : ℕ} (ψ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    ψ.gammaFactor s ≠ 0 := by
  rcases ψ.even_or_odd with hp | hp
  · rw [hp.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [hp.gammaFactor_def]
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    simp only [Complex.add_re, Complex.one_re]
    linarith

end SolAux

theorem _root_.SWPort.Davenport.LFunction_zero_one_sub_of_isQuadratic (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic) (hχ1 : χ ≠ 1)
    (β : ℝ) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (h : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    DirichletCharacter.LFunction χ ((1 - β : ℝ) : ℂ) = 0 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set χ' : DirichletCharacter ℂ χ.conductor := χ.primitiveCharacter with hχ'def
  have hcl : changeLevel χ.conductor_dvd_level χ' = χ := χ.changeLevel_primitiveCharacter
  -- `χ'` is nontrivial
  have hχ'1 : χ' ≠ 1 := by
    intro hh
    exact hχ1 (by rw [← hcl, hh, map_one])
  -- `χ'` is quadratic
  have hχ'q : χ'.IsQuadratic := by
    rw [MulChar.isQuadratic_iff_sq_eq_one]
    refine (changeLevel_eq_one_iff χ.conductor_dvd_level).mp ?_
    rw [map_pow, hcl]
    exact hχ.sq_eq_one
  have hcond1 : χ.conductor ≠ 1 := fun hh => hχ1 (eq_one_iff_conductor_eq_one.mpr hh)
  have hreβ : (0 : ℝ) < ((β : ℂ)).re := by simpa using hβ₀
  have hre1β : (0 : ℝ) < (1 - (β : ℂ)).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith
  -- Step 2: `L(β, χ') = 0`
  have key1 : LFunction χ' (β : ℂ) = 0 := by
    have hstep := LFunction_changeLevel χ.conductor_dvd_level χ' (s := (β : ℂ)) (Or.inl hχ'1)
    rw [hcl, h] at hstep
    rcases mul_eq_zero.mp hstep.symm with h1 | h1
    · exact h1
    · exact absurd h1 (SolAux.prod_factor_ne_zero q χ' hreβ)
  -- Step 4: the completed L-function vanishes at `β`
  have hcomp : completedLFunction χ' (β : ℂ) = 0 := by
    have hstep := LFunction_eq_completed_div_gammaFactor χ' (β : ℂ) (Or.inr hcond1)
    rw [key1] at hstep
    exact (div_eq_zero_iff.mp hstep.symm).resolve_right (SolAux.gammaFactor_ne_zero χ' hreβ)
  -- Step 5: the functional equation
  have hfe := (χ.primitiveCharacter_isPrimitive).completedLFunction_one_sub (β : ℂ)
  rw [hχ'q.inv, hcomp, mul_zero] at hfe
  -- Step 6: back to the L-function of `χ`
  have key2 : LFunction χ' (1 - (β : ℂ)) = 0 := by
    rw [LFunction_eq_completed_div_gammaFactor χ' _ (Or.inr hcond1), hfe, zero_div]
  have hstep := LFunction_changeLevel χ.conductor_dvd_level χ' (s := 1 - (β : ℂ)) (Or.inl hχ'1)
  rw [hcl, key2, zero_mul] at hstep
  push_cast
  exact hstep

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Zeta23_WeilEF_logDeriv_partial_fraction_disk
alias SWPort.Zeta23.WeilEF.logDeriv_partial_fraction_disk := SWPort.Z.Zeta23.WeilEF.logDeriv_partial_fraction_disk
end

section
-- module Solutions.Artin.SW.Thm.Zeta23_RvM_norm_riemannZeta_le_of_re_pos
alias SWPort.Zeta23.RvM.norm_riemannZeta_le_of_re_pos := SWPort.Z.Zeta23.RvM.norm_riemannZeta_le_of_re_pos
end

section
-- module Solutions.Artin.SW.Thm.Zeta23_RvM_norm_riemannZeta_sub_one_le
alias SWPort.Zeta23.RvM.norm_riemannZeta_sub_one_le := SWPort.Z.Zeta23.RvM.norm_riemannZeta_sub_one_le
end

section
-- module Solutions.Artin.SW.Thm.Davenport_zeta_logDeriv_region_bound
namespace SWPort
/-! Ported from prove2.me: `Davenport.zeta_logDeriv_region_bound` (166af891-8983-454f-a7d7-8e883e5532f0, statement by alya); proof = accepted sketch submission 4c1aadea-2473-4804-83f8-c797c35391ea by alya. -/













open Complex

/-!
# Bound for `ζ'/ζ(s) + 1/(s-1)` in the zero-free region

Assuming `ζ` has no zeros in the region `Re s ≥ 1 - c / log (q (|Im s| + 2))`, we show
`‖ζ'/ζ(s) + 1/(s - 1)‖ ≪ log (q (|Im s| + 2))^2` for `s` in the smaller region with constant
`c / 4` and `Re s ≥ 3/4`.

For `Re s ≥ 2` this follows from the Dirichlet series of `-ζ'/ζ`.  For `3/4 ≤ Re s ≤ 2` we apply
the partial-fraction theorem `Zeta23.WeilEF.logDeriv_partial_fraction_disk` to the entire function
`g(z) = (z - 1) ζ(z)` on the disc `|z - (2 + i t)| ≤ 2`, and use the zero-free hypothesis to keep
every zero `ρ` of `g` in the disc at distance `≥ c / (4 log (q (|t| + 2)))` from `s`.
-/

namespace ZetaRegion

open Filter Topology ArithmeticFunction
open scoped LSeries.notation

/-! ### The entire function `(z - 1) ζ(z)` -/

private lemma g_of_ne {z : ℂ} (hz : z ≠ 1) : g z = (z - 1) * riemannZeta z :=
  Function.update_of_ne hz _ _

private lemma g_one : g 1 = 1 := Function.update_self _ _ _

private lemma g_eventuallyEq {z : ℂ} (hz : z ≠ 1) :
    g =ᶠ[𝓝 z] fun w => (w - 1) * riemannZeta w := by
  filter_upwards [isOpen_ne.mem_nhds hz] with w hw
  exact g_of_ne hw

private lemma hasDerivAt_prod {z : ℂ} (hz : z ≠ 1) :
    HasDerivAt (fun w => (w - 1) * riemannZeta w)
      (riemannZeta z + (z - 1) * deriv riemannZeta z) z := by
  have h1 : HasDerivAt (fun w : ℂ => w - 1) 1 z := (hasDerivAt_id' z).sub_const 1
  have h2 := (differentiableAt_riemannZeta hz).hasDerivAt
  convert h1.mul h2 using 1 <;> try with_reducible_and_instances rfl
  ring

private lemma differentiableAt_g {z : ℂ} (hz : z ≠ 1) : DifferentiableAt ℂ g z :=
  (hasDerivAt_prod hz).differentiableAt.congr_of_eventuallyEq (g_eventuallyEq hz)

private lemma analyticAt_g (z : ℂ) : AnalyticAt ℂ g z := by
  by_cases hz : z = 1
  · subst hz
    refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact differentiableAt_g hw
    · exact continuousAt_update_same.mpr riemannZeta_residue_one
  · refine DifferentiableOn.analyticAt (s := {1}ᶜ) ?_ (isOpen_compl_singleton.mem_nhds hz)
    intro w hw
    exact (differentiableAt_g hw).differentiableWithinAt

private lemma logDeriv_g {s : ℂ} (hs : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    logDeriv g s = deriv riemannZeta s / riemannZeta s + 1 / (s - 1) := by
  have hd : deriv g s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
    rw [(g_eventuallyEq hs).deriv_eq]
    exact (hasDerivAt_prod hs).deriv
  rw [logDeriv_apply, hd, g_of_ne hs]
  have : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp
  ring

/-! ### Bounds on `g` -/

private lemma norm_g_two_ge (t : ℝ) : 1 / 3 ≤ ‖g (2 + t * I)‖ := by
  set s₀ : ℂ := 2 + t * I with hs₀
  have hre : s₀.re = 2 := by simp [hs₀]
  have hs₀1 : s₀ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hre] at this
    norm_num at this
  rw [g_of_ne hs₀1, norm_mul]
  have h1 : 1 ≤ ‖s₀ - 1‖ := by
    have := Complex.abs_re_le_norm (s₀ - 1)
    rw [Complex.sub_re, hre] at this
    norm_num at this
    exact this
  have h2 : 1 / 3 ≤ ‖riemannZeta s₀‖ := by
    have hb := Zeta23.RvM.norm_riemannZeta_sub_one_le (s := s₀) (by rw [hre])
    have := abs_le.mp (abs_norm_sub_norm_le (riemannZeta s₀) 1)
    rw [norm_one] at this
    nlinarith [Real.pi_lt_d2, Real.pi_pos, this.1]
  calc (1 : ℝ) / 3 = 1 * (1 / 3) := by ring
    _ ≤ ‖s₀ - 1‖ * ‖riemannZeta s₀‖ := by gcongr

private lemma norm_g_le (t : ℝ) {w : ℂ} (hw : w ∈ Metric.closedBall (2 + t * I) (24 / 25 * 2)) :
    ‖g w‖ ≤ 100 * (|t| + 2) ^ 2 := by
  set s₀ : ℂ := 2 + t * I with hs₀
  have hre : s₀.re = 2 := by simp [hs₀]
  have hs₀norm : ‖s₀‖ ≤ |t| + 2 := by
    calc ‖s₀‖ = ‖(2 : ℂ) + t * I‖ := rfl
      _ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 2 + |t| := by simp
      _ = |t| + 2 := by ring
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  have hA : 2 ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hwre : 2 / 25 ≤ w.re := by
    have h1 : |(w - s₀).re| ≤ ‖w - s₀‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, hre] at h1
    have := (abs_le.mp h1).1
    linarith
  have hwnorm : ‖w‖ ≤ 2 * (|t| + 2) := by
    calc ‖w‖ = ‖(w - s₀) + s₀‖ := by ring_nf
      _ ≤ ‖w - s₀‖ + ‖s₀‖ := norm_add_le _ _
      _ ≤ 24 / 25 * 2 + (|t| + 2) := by linarith
      _ ≤ 2 * (|t| + 2) := by linarith
  have hw1 : ‖w - 1‖ ≤ 3 * (|t| + 2) := by
    calc ‖w - 1‖ ≤ ‖w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 * (|t| + 2) + 1 := by rw [norm_one]; linarith
      _ ≤ 3 * (|t| + 2) := by linarith
  by_cases h1 : w = 1
  · subst h1
    rw [g_one, norm_one]
    nlinarith
  · rw [g_of_ne h1, norm_mul]
    have hwpos : 0 < w.re := by linarith
    have hζ := Zeta23.RvM.norm_riemannZeta_le_of_re_pos hwpos h1
    have hne : ‖w - 1‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h1)
    have h1w : ‖1 - w‖ = ‖w - 1‖ := norm_sub_rev _ _
    have hprod : ‖w - 1‖ * ‖w‖ / w.re ≤ (3 * (|t| + 2)) * (2 * (|t| + 2)) / (2 / 25) := by
      gcongr
    calc ‖w - 1‖ * ‖riemannZeta w‖
        ≤ ‖w - 1‖ * (1 / 2 + 1 / ‖1 - w‖ + ‖w‖ / w.re) := by gcongr
      _ = ‖w - 1‖ / 2 + 1 + ‖w - 1‖ * ‖w‖ / w.re := by
          rw [h1w]
          field_simp
      _ ≤ 3 * (|t| + 2) / 2 + 1 + (3 * (|t| + 2)) * (2 * (|t| + 2)) / (2 / 25) := by
          gcongr
      _ ≤ 100 * (|t| + 2) ^ 2 := by nlinarith

/-! ### Elementary logarithm estimates -/

private lemma log_two_le_logX (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  refine Real.log_le_log (by norm_num) ?_
  have : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  nlinarith

private lemma inv_log_ratio_le : 1 / Real.log ((24 / 25 : ℝ) / (22 / 25)) ≤ 12 := by
  have h : (1 : ℝ) / 12 ≤ Real.log ((24 / 25 : ℝ) / (22 / 25)) := by
    have := Real.one_sub_inv_le_log_of_pos (x := (24 / 25 : ℝ) / (22 / 25)) (by norm_num)
    norm_num at this ⊢
    linarith
  have hpos : 0 < Real.log ((24 / 25 : ℝ) / (22 / 25)) := by linarith
  rw [div_le_iff₀ hpos]
  linarith

private lemma K_pos : 0 < K := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : 0 ≤ Real.log 300 / Real.log 2 := div_nonneg (Real.log_nonneg (by norm_num)) hlog2.le
  unfold K
  linarith

private lemma log_B_le (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log (300 * (|t| + 2) ^ 2) ≤ K * Real.log ((q : ℝ) * (|t| + 2)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 < |t| + 2 := by linarith [abs_nonneg t]
  have hL : Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) := log_two_le_logX q t
  have hlogA : Real.log (|t| + 2) ≤ Real.log ((q : ℝ) * (|t| + 2)) :=
    Real.log_le_log hA (le_mul_of_one_le_left hA.le hq1)
  have h300 : 0 ≤ Real.log 300 / Real.log 2 := div_nonneg (Real.log_nonneg (by norm_num)) hlog2.le
  have heq : Real.log 300 = Real.log 300 / Real.log 2 * Real.log 2 := by
    field_simp
  have hh := mul_le_mul_of_nonneg_left hL h300
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  unfold K
  push_cast
  nlinarith

/-! ### The core application of the partial-fraction theorem -/

private lemma core (t : ℝ) :
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ Metric.closedBall (2 + t * I) (22 / 25 * 2) | g ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt g ρ : ℝ)) ≤ 12 * Real.log (300 * (|t| + 2) ^ 2)) ∧
      ∀ s ∈ Metric.closedBall (2 + t * I) (83 / 100 * 2), g s ≠ 0 →
        ‖logDeriv g s - ∑ ρ ∈ Z, (analyticOrderNatAt g ρ : ℂ) / (s - ρ)‖
          ≤ 44795000 / 2 * Real.log (300 * (|t| + 2) ^ 2) := by
  set s₀ : ℂ := 2 + t * I with hs₀
  have hfa : AnalyticOnNhd ℂ g (Metric.closedBall s₀ 2) := fun z _ => analyticAt_g z
  have hf0' := norm_g_two_ge t
  have hf0 : g s₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hf0'; norm_num at hf0'
  have hA : 2 ≤ |t| + 2 := by linarith [abs_nonneg t]
  set B : ℝ := 300 * (|t| + 2) ^ 2 with hB
  have hB2 : 2 ≤ B := by rw [hB]; nlinarith
  have hfB : ∀ w ∈ Metric.closedBall s₀ (24 / 25 * 2), ‖g w‖ ≤ B * ‖g s₀‖ := by
    intro w hw
    calc ‖g w‖ ≤ 100 * (|t| + 2) ^ 2 := norm_g_le t hw
      _ = B * (1 / 3) := by rw [hB]; ring
      _ ≤ B * ‖g s₀‖ := by gcongr
  obtain ⟨Z, hZ, hsum, hbound⟩ :=
    Zeta23.WeilEF.logDeriv_partial_fraction_disk (by norm_num : (0 : ℝ) < 2) hfa hf0 hB2 hfB
  refine ⟨Z, hZ, ?_, hbound⟩
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  calc _ ≤ 1 / Real.log ((24 / 25) / (22 / 25)) * Real.log B := hsum
    _ ≤ 12 * Real.log B := by gcongr; exact inv_log_ratio_le

/-! ### Case `3/4 ≤ Re s ≤ 2` -/

private lemma caseB (c : ℝ) (hc : 0 < c) (q : ℕ) [NeZero q]
    (hzero : ∀ s : ℂ, s ≠ 1 → 0 < s.re → Davenport.InRegion c q s → riemannZeta s ≠ 0)
    (s : ℂ) (hs : Davenport.InRegion (c / 4) q s) (hre : 3 / 4 ≤ s.re) (hs2 : s.re ≤ 2)
    (hs1 : s ≠ 1) :
    ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖
      ≤ (22397500 * K / Real.log 2 + 48 * K / c) * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2 := by
  set t := s.im with ht
  set Lq := Real.log ((q : ℝ) * (|t| + 2)) with hLq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL2 : Real.log 2 ≤ Lq := log_two_le_logX q t
  have hLpos : 0 < Lq := lt_of_lt_of_le hlog2 hL2
  have hKpos : 0 < K := K_pos
  unfold Davenport.InRegion Davenport.regionBoundary at hs
  rw [← ht, ← hLq] at hs
  have hζs : riemannZeta s ≠ 0 := by
    apply hzero s hs1 (by linarith)
    unfold Davenport.InRegion Davenport.regionBoundary
    rw [← ht, ← hLq]
    have : c / 4 / Lq ≤ c / Lq := by
      rw [div_div]
      exact div_le_div_of_nonneg_left hc.le hLpos (by linarith)
    linarith
  have hgs : g s ≠ 0 := by
    rw [g_of_ne hs1]; exact mul_ne_zero (sub_ne_zero.mpr hs1) hζs
  obtain ⟨Z, hZ, hsum, hbound⟩ := core t
  set B := 300 * (|t| + 2) ^ 2 with hB
  have hlogB : Real.log B ≤ K * Lq := log_B_le q t
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg (by nlinarith [abs_nonneg t])
  -- `s` lies in the disc of radius `83/50` about `2 + i t`
  have hs_mem : s ∈ Metric.closedBall (2 + t * I) (83 / 100 * 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have : s - (2 + t * I) = ((s.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [ht]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hmain := hbound s hs_mem hgs
  -- zeros of `g` in the disc are zeros of `ζ`, hence outside the region with constant `c`
  have hmem : ∀ ρ ∈ Z, ρ ∈ Metric.closedBall (2 + t * I) (22 / 25 * 2) ∧ g ρ = 0 := by
    intro ρ hρ
    have h := Finset.mem_coe.mpr hρ
    rw [hZ] at h
    exact h
  have hdist : ∀ ρ ∈ Z, c / (4 * Lq) ≤ ‖s - ρ‖ := by
    intro ρ hρ
    obtain ⟨hρball, hρ0⟩ := hmem ρ hρ
    rw [Metric.mem_closedBall, dist_eq_norm] at hρball
    have hρ1 : ρ ≠ 1 := by
      rintro rfl
      rw [g_one] at hρ0
      exact one_ne_zero hρ0
    have hζρ : riemannZeta ρ = 0 := by
      rw [g_of_ne hρ1] at hρ0
      exact (mul_eq_zero.mp hρ0).resolve_left (sub_ne_zero.mpr hρ1)
    have hre2 : (2 + t * I : ℂ).re = 2 := by simp
    have him2 : (2 + t * I : ℂ).im = t := by simp
    have hρre : 6 / 25 ≤ ρ.re := by
      have h1 := Complex.abs_re_le_norm (ρ - (2 + t * I))
      rw [Complex.sub_re, hre2] at h1
      have := (abs_le.mp h1).1
      linarith
    have hρim : |ρ.im| ≤ |t| + 44 / 25 := by
      have h1 := Complex.abs_im_le_norm (ρ - (2 + t * I))
      rw [Complex.sub_im, him2] at h1
      have h2 : |ρ.im| ≤ |ρ.im - t| + |t| := by
        calc |ρ.im| = |(ρ.im - t) + t| := by ring_nf
          _ ≤ |ρ.im - t| + |t| := abs_add_le _ _
      linarith
    have hnot : ¬ Davenport.InRegion c q ρ := fun h => hzero ρ hρ1 (by linarith) h hζρ
    unfold Davenport.InRegion Davenport.regionBoundary at hnot
    rw [not_le] at hnot
    set Lq' := Real.log ((q : ℝ) * (|ρ.im| + 2)) with hLρ
    have hLρ2 : Real.log 2 ≤ Lq' := log_two_le_logX q ρ.im
    have hLρpos : 0 < Lq' := lt_of_lt_of_le hlog2 hLρ2
    have hLρle : Lq' ≤ 2 * Lq := by
      have : (q : ℝ) * (|ρ.im| + 2) ≤ 2 * ((q : ℝ) * (|t| + 2)) := by
        nlinarith [abs_nonneg t]
      calc Lq' ≤ Real.log (2 * ((q : ℝ) * (|t| + 2))) :=
            Real.log_le_log (by positivity) this
        _ = Real.log 2 + Lq := Real.log_mul (by norm_num) (by positivity)
        _ ≤ 2 * Lq := by linarith
    have hcL : c / (2 * Lq) ≤ c / Lq' := div_le_div_of_nonneg_left hc.le hLρpos hLρle
    have hgap : c / (4 * Lq) ≤ s.re - ρ.re := by
      have e1 : c / 4 / Lq = c / (4 * Lq) := by rw [div_div]
      have e2 : c / (2 * Lq) = 2 * (c / (4 * Lq)) := by field_simp; ring
      linarith
    calc c / (4 * Lq) ≤ s.re - ρ.re := hgap
      _ ≤ |(s - ρ).re| := by rw [Complex.sub_re]; exact le_abs_self _
      _ ≤ ‖s - ρ‖ := Complex.abs_re_le_norm _
  have hcL_pos : 0 < c / (4 * Lq) := by positivity
  have hsumnorm : ‖∑ ρ ∈ Z, (analyticOrderNatAt g ρ : ℂ) / (s - ρ)‖
      ≤ (4 * Lq / c) * (12 * Real.log B) := by
    calc ‖∑ ρ ∈ Z, (analyticOrderNatAt g ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ Z, ‖(analyticOrderNatAt g ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (analyticOrderNatAt g ρ : ℝ) * (4 * Lq / c) := by
          apply Finset.sum_le_sum
          intro ρ hρ
          rw [norm_div, Complex.norm_natCast]
          have hd := hdist ρ hρ
          have hpos : 0 < ‖s - ρ‖ := lt_of_lt_of_le hcL_pos hd
          rw [div_le_iff₀ hpos]
          have h1 : 1 ≤ ‖s - ρ‖ * (4 * Lq / c) := by
            calc (1 : ℝ) = c / (4 * Lq) * (4 * Lq / c) := by field_simp
              _ ≤ ‖s - ρ‖ * (4 * Lq / c) := by gcongr
          calc (analyticOrderNatAt g ρ : ℝ) = (analyticOrderNatAt g ρ : ℝ) * 1 := by ring
            _ ≤ (analyticOrderNatAt g ρ : ℝ) * (‖s - ρ‖ * (4 * Lq / c)) := by gcongr
            _ = _ := by ring
      _ = (∑ ρ ∈ Z, (analyticOrderNatAt g ρ : ℝ)) * (4 * Lq / c) := by rw [Finset.sum_mul]
      _ ≤ (12 * Real.log B) * (4 * Lq / c) := by gcongr
      _ = _ := by ring
  have hld : logDeriv g s = deriv riemannZeta s / riemannZeta s + 1 / (s - 1) :=
    logDeriv_g hs1 hζs
  rw [← hld]
  have hfin1 : 44795000 / 2 * (K * Lq) ≤ 22397500 * K / Real.log 2 * Lq ^ 2 := by
    have e : 22397500 * K / Real.log 2 * Lq ^ 2 = 22397500 * K * Lq * (Lq / Real.log 2) := by
      field_simp
    have h1 : 1 ≤ Lq / Real.log 2 := (le_div_iff₀ hlog2).mpr (by linarith)
    rw [e]
    calc 44795000 / 2 * (K * Lq) = 22397500 * K * Lq * 1 := by ring
      _ ≤ 22397500 * K * Lq * (Lq / Real.log 2) := by gcongr
  have hfin2 : 4 * Lq / c * (12 * (K * Lq)) = 48 * K / c * Lq ^ 2 := by
    field_simp
    ring
  calc ‖logDeriv g s‖
      = ‖(logDeriv g s - ∑ ρ ∈ Z, (analyticOrderNatAt g ρ : ℂ) / (s - ρ))
          + ∑ ρ ∈ Z, (analyticOrderNatAt g ρ : ℂ) / (s - ρ)‖ := by rw [sub_add_cancel]
    _ ≤ ‖logDeriv g s - ∑ ρ ∈ Z, (analyticOrderNatAt g ρ : ℂ) / (s - ρ)‖
          + ‖∑ ρ ∈ Z, (analyticOrderNatAt g ρ : ℂ) / (s - ρ)‖ := norm_add_le _ _
    _ ≤ 44795000 / 2 * Real.log B + (4 * Lq / c) * (12 * Real.log B) :=
          add_le_add hmain hsumnorm
    _ ≤ 44795000 / 2 * (K * Lq) + (4 * Lq / c) * (12 * (K * Lq)) := by gcongr
    _ ≤ 22397500 * K / Real.log 2 * Lq ^ 2 + 48 * K / c * Lq ^ 2 := by
          rw [hfin2]; linarith
    _ = (22397500 * K / Real.log 2 + 48 * K / c) * Lq ^ 2 := by ring

/-! ### Case `Re s ≥ 2`: the Dirichlet series -/

private lemma M₀_nonneg : 0 ≤ M₀ := tsum_nonneg fun _ => norm_nonneg _

private lemma norm_logDeriv_zeta_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ M₀ := by
  have hs1 : 1 < s.re := by linarith
  have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1
  have : deriv riemannZeta s / riemannZeta s = -(LSeries ↗Λ s) := by
    rw [h, neg_div, neg_neg]
  rw [this, norm_neg]
  have hsum_s : Summable fun n => ‖LSeries.term ↗Λ s n‖ := by
    have := ArithmeticFunction.LSeriesSummable_vonMangoldt hs1
    rwa [LSeriesSummable, ← summable_norm_iff] at this
  have hsum_2 : Summable fun n => ‖LSeries.term ↗Λ 2 n‖ := by
    have := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := 2) (by norm_num)
    rwa [LSeriesSummable, ← summable_norm_iff] at this
  have h2re : (2 : ℂ).re ≤ s.re := by simpa using hs
  calc ‖LSeries ↗Λ s‖ = ‖∑' n, LSeries.term ↗Λ s n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term ↗Λ s n‖ := norm_tsum_le_tsum_norm hsum_s
    _ ≤ ∑' n, ‖LSeries.term ↗Λ 2 n‖ :=
        hsum_s.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re _ h2re n) hsum_2
    _ = M₀ := rfl

private lemma caseA (q : ℕ) [NeZero q] (s : ℂ) (hs : 2 ≤ s.re) :
    ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖
      ≤ (M₀ + 1) / Real.log 2 ^ 2 * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL2 : Real.log 2 ≤ Real.log ((q : ℝ) * (|s.im| + 2)) := log_two_le_logX q s.im
  have hM := M₀_nonneg
  have h1 : ‖1 / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    have : 1 ≤ ‖s - 1‖ := by
      have := Complex.abs_re_le_norm (s - 1)
      rw [Complex.sub_re, Complex.one_re] at this
      have h : 1 ≤ |s.re - 1| := by rw [abs_of_nonneg (by linarith)]; linarith
      linarith
    exact div_le_one_of_le₀ this (norm_nonneg _)
  calc ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖
      ≤ ‖deriv riemannZeta s / riemannZeta s‖ + ‖1 / (s - 1)‖ := norm_add_le _ _
    _ ≤ M₀ + 1 := add_le_add (norm_logDeriv_zeta_le hs) h1
    _ = (M₀ + 1) / Real.log 2 ^ 2 * Real.log 2 ^ 2 := by field_simp
    _ ≤ (M₀ + 1) / Real.log 2 ^ 2 * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog2.le hL2 2)
        exact div_nonneg (by linarith) (by positivity)

end ZetaRegion

open ZetaRegion in
private theorem zeta_region_bound (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q],
        (∀ s : ℂ, s ≠ 1 → 0 < s.re → Davenport.InRegion c q s → riemannZeta s ≠ 0) →
        ∀ s : ℂ, Davenport.InRegion (c / 4) q s → 3 / 4 ≤ s.re → s ≠ 1 →
          ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖
            ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM := M₀_nonneg
  have hK := K_pos
  have hA : 0 ≤ (M₀ + 1) / Real.log 2 ^ 2 := div_nonneg (by linarith) (by positivity)
  have hB : 0 ≤ 22397500 * K / Real.log 2 + 48 * K / c := by positivity
  refine ⟨(M₀ + 1) / Real.log 2 ^ 2 + (22397500 * K / Real.log 2 + 48 * K / c) + 1, ?_, ?_⟩
  · linarith
  · intro q _ hzero s hs hre hs1
    have hLsq : 0 ≤ Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2 := sq_nonneg _
    by_cases h2 : s.re ≤ 2
    · calc _ ≤ _ := caseB c hc q hzero s hs hre h2 hs1
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hLsq
          linarith
    · rw [not_le] at h2
      calc _ ≤ _ := caseA q s h2.le
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hLsq
          linarith


theorem _root_.SWPort.Davenport.zeta_logDeriv_region_bound (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q],
        (∀ s : ℂ, s ≠ 1 → Davenport.InRegion c q s → riemannZeta s ≠ 0) →
        ∀ s : ℂ, Davenport.InRegion (c / 4) q s → 3 / 4 ≤ s.re → s ≠ 1 →
          ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖
            ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2 := by
  obtain ⟨C, hC, H⟩ := zeta_region_bound c hc
  exact ⟨C, hC, fun q _ hzf => H q (fun s hs1 _ hreg => hzf s hs1 hreg)⟩

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_logDeriv_LFunction_region_bound
namespace SWPort
/-! Ported from prove2.me: `Davenport.logDeriv_LFunction_region_bound` (73d46b4d-209f-401a-8246-602afd9fb331, statement by alya); proof = accepted sketch submission f1fce16d-1a30-461d-a96e-16ad52a62509 by alya. -/

























open Finset DirichletCharacter Vino Davenport

namespace SolRegionBound

set_option maxHeartbeats 1000000

/-! ### Elementary numeric facts -/

private lemma half_le_log_two : (1:ℝ)/2 ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
  norm_num at h
  linarith

private lemma log_region_pos {q : ℕ} (hq : (1:ℝ) ≤ (q:ℝ)) (t : ℝ) :
    0 < Real.log ((q : ℝ) * (|t| + 2)) := by
  apply Real.log_pos
  nlinarith [abs_nonneg t]

private lemma half_le_log_region {q : ℕ} (hq : (1:ℝ) ≤ (q:ℝ)) (t : ℝ) :
    (1:ℝ)/2 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have h : Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
    apply Real.log_le_log (by norm_num)
    nlinarith [abs_nonneg t]
  linarith [half_le_log_two]

private lemma inRegion_mono {q : ℕ} (hq : (1:ℝ) ≤ (q:ℝ)) {c : ℝ} (hc : 0 < c) {s : ℂ}
    (h : InRegion (c/4) q s) : InRegion c q s := by
  have hlog := log_region_pos hq s.im
  unfold InRegion regionBoundary at h ⊢
  have : c / 4 / Real.log ((q:ℝ) * (|s.im| + 2)) ≤ c / Real.log ((q:ℝ) * (|s.im| + 2)) := by
    gcongr
    linarith
  linarith

/-- Every element of an exceptional set has real part at least `1/2`. -/
private lemma half_le_re {q : ℕ} [NeZero q] {c : ℝ} {χ : DirichletCharacter ℂ q} {E : Set ℂ}
    (hE : IsExceptionalSet c χ E) {z : ℂ} (hz : z ∈ E) : 1 / 2 ≤ z.re := by
  obtain ⟨him, hre0, hre1, hreg, hL, hquad, hχ1⟩ := hE.2.1 z hz
  by_contra hlt
  rw [not_le] at hlt
  have hzeq : ((z.re : ℝ) : ℂ) = z := by
    apply Complex.ext <;> simp [him]
  have hL' : DirichletCharacter.LFunction χ ((z.re : ℝ) : ℂ) = 0 := by rw [hzeq]; exact hL
  have hzero := Davenport.LFunction_zero_one_sub_of_isQuadratic q χ hquad hχ1 z.re hre0 hre1 hL'
  set s : ℂ := ((1 - z.re : ℝ) : ℂ) with hsdef
  have hs_re : s.re = 1 - z.re := by simp [hsdef]
  have hs_im : s.im = 0 := by simp [hsdef]
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs_re
    simp only [Complex.one_re] at hs_re
    linarith
  have hreg' : InRegion c q s := by
    unfold InRegion regionBoundary at hreg ⊢
    rw [hs_im, hs_re]
    rw [him] at hreg
    linarith
  have hsE : s ∉ E := by
    intro hmem
    have heq : s = z := hE.1 hmem hz
    have hh : (1 : ℝ) - z.re = z.re := by rw [← hs_re, heq]
    linarith
  exact hE.2.2 s hs1 hreg' hsE hzero

/-- The distance from `s` to the centre `2 + i Im s`. -/
private lemma norm_sub_center (s : ℂ) : ‖s - (2 + (s.im : ℂ) * Complex.I)‖ = |s.re - 2| := by
  have h : s - (2 + (s.im : ℂ) * Complex.I) = ((s.re - 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [h, Complex.norm_real, Real.norm_eq_abs]

/-! ### The bound on `L'/L` far to the right -/

open scoped LSeries.notation

private lemma logDeriv_norm_le_two {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 3 ≤ s.re) :
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤ 2 := by
  have hs1 : 1 < s.re := by linarith
  have e : -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s)
      = LSeries (↗χ * ↗ArithmeticFunction.vonMangoldt) s := by
    rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs1,
      DirichletCharacter.LFunction_eq_LSeries χ hs1,
      DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs1, neg_div]
  have hbd : ∀ n : ℕ, ‖LSeries.term (↗χ * ↗ArithmeticFunction.vonMangoldt) s n‖
      ≤ 1 / (n:ℝ)^2 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · norm_num
    · rw [LSeries.norm_term_eq, if_neg hn]
      have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hn0 : (0:ℝ) < (n:ℝ) := by linarith
      have hcoef : ‖(↗χ * ↗ArithmeticFunction.vonMangoldt) n‖ ≤ (n:ℝ) := by
        simp only [Pi.mul_apply, norm_mul]
        have h1 : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
        have h2 : ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖
            = ArithmeticFunction.vonMangoldt n := by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        have h3 : ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
          ArithmeticFunction.vonMangoldt_le_log
        have h4 : Real.log n ≤ (n:ℝ) - 1 := Real.log_le_sub_one_of_pos hn0
        rw [h2]
        nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := n), norm_nonneg (χ (n : ZMod q))]
      have hrpow : (n:ℝ)^(3:ℝ) ≤ (n:ℝ)^s.re := Real.rpow_le_rpow_of_exponent_le hn1 hs
      have hp3 : (0:ℝ) < (n:ℝ)^(3:ℝ) := Real.rpow_pos_of_pos hn0 _
      have hps : (0:ℝ) < (n:ℝ)^s.re := Real.rpow_pos_of_pos hn0 _
      calc ‖(↗χ * ↗ArithmeticFunction.vonMangoldt) n‖ / (n:ℝ)^s.re
          ≤ (n:ℝ) / (n:ℝ)^s.re := by gcongr
        _ ≤ (n:ℝ) / (n:ℝ)^(3:ℝ) := by gcongr
        _ = 1 / (n:ℝ)^2 := by
            rw [show ((3:ℝ)) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
            have hne : (n:ℝ) ≠ 0 := ne_of_gt hn0
            field_simp
  have hsum2 : Summable (fun n : ℕ => (1:ℝ)/(n:ℝ)^2) := hasSum_zeta_two.summable
  have hsumnorm : Summable (fun n : ℕ => ‖LSeries.term (↗χ * ↗ArithmeticFunction.vonMangoldt) s n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbd hsum2
  have h1 : ‖LSeries (↗χ * ↗ArithmeticFunction.vonMangoldt) s‖
      ≤ ∑' n : ℕ, ‖LSeries.term (↗χ * ↗ArithmeticFunction.vonMangoldt) s n‖ := by
    simp only [LSeries]
    exact norm_tsum_le_tsum_norm hsumnorm
  have h2 : ∑' n : ℕ, ‖LSeries.term (↗χ * ↗ArithmeticFunction.vonMangoldt) s n‖
      ≤ ∑' n : ℕ, (1:ℝ)/(n:ℝ)^2 := hsumnorm.tsum_le_tsum hbd hsum2
  have h3 : ∑' n : ℕ, (1:ℝ)/(n:ℝ)^2 = Real.pi^2/6 := hasSum_zeta_two.tsum_eq
  have h4 : Real.pi^2/6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have : ‖LSeries (↗χ * ↗ArithmeticFunction.vonMangoldt) s‖ ≤ 2 := by
    rw [h3] at h2; linarith
  rw [← norm_neg, e]
  exact this

/-! ### The Euler factors at the primes dividing `q` -/

private lemma norm_factor_bounds {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 3/4 ≤ s.re) :
    ‖(p:ℂ)^(-s)‖ ≤ 3/5 ∧ (2:ℝ)/5 ≤ ‖1 - (p:ℂ)^(-s)‖ := by
  have hkey : (2:ℝ)^(-3/4 : ℝ) ≤ 3/5 := by
    set a : ℝ := (2:ℝ)^(-3/4 : ℝ) with hadef
    have hpos : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
    have ha4 : a^(4:ℕ) = 1/8 := by
      rw [hadef, ← Real.rpow_natCast ((2:ℝ)^(-3/4:ℝ)) 4, ← Real.rpow_mul (by norm_num)]
      norm_num
    by_contra hcon
    push Not at hcon
    have h2 : (9:ℝ)/25 < a^2 := by nlinarith
    have h4 : (81:ℝ)/625 < a^(4:ℕ) := by nlinarith
    rw [ha4] at h4
    norm_num at h4
  have hp0 : 0 < p := by omega
  have hnorm : ‖(p:ℂ)^(-s)‖ = (p:ℝ)^(-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hp0]
    simp
  have h1 : (p:ℝ)^(-s.re) ≤ (2:ℝ)^(-s.re) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp) (by linarith)
  have h2 : (2:ℝ)^(-s.re) ≤ (2:ℝ)^(-3/4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hle : ‖(p:ℂ)^(-s)‖ ≤ 3/5 := by rw [hnorm]; linarith
  refine ⟨hle, ?_⟩
  have h := norm_sub_norm_le (1 : ℂ) ((p:ℂ)^(-s))
  rw [norm_one] at h
  linarith

private lemma differentiableAt_factor {p : ℕ} (hp : p ≠ 0) (z : ℂ) :
    DifferentiableAt ℂ (fun w : ℂ => 1 - (p:ℂ)^(-w)) z := by
  have hp0 : (p:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have h1 : DifferentiableAt ℂ (fun w : ℂ => -w) z := (differentiableAt_id (𝕜 := ℂ) (x := z)).neg
  exact (h1.const_cpow (Or.inl hp0)).const_sub 1

private lemma logDeriv_factor_bound {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 3/4 ≤ s.re) :
    ‖logDeriv (fun w : ℂ => 1 - (p:ℂ)^(-w)) s‖ ≤ 2 * Real.log p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : (p:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  obtain ⟨hb1, hb2⟩ := norm_factor_bounds hp2 hs
  have hlogp : (0:ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hd : DifferentiableAt ℂ (fun w : ℂ => -w) s := (differentiableAt_id (𝕜 := ℂ) (x := s)).neg
  have hderiv : deriv (fun w : ℂ => 1 - (p:ℂ)^(-w)) s = (Complex.log p) * (p:ℂ)^(-s) := by
    rw [deriv_const_sub, Complex.deriv_const_cpow hd]
    simp
  have hlogn : ‖Complex.log (p:ℂ)‖ = Real.log p := by
    rw [← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogp]
  rw [logDeriv_apply, hderiv, norm_div, norm_mul, hlogn]
  have hden : (0:ℝ) < ‖1 - (p:ℂ)^(-s)‖ := by linarith
  rw [div_le_iff₀ hden]
  nlinarith [hlogp, hb1, hb2, norm_nonneg ((p:ℂ)^(-s))]

private lemma sum_logDeriv_factors_bound (q : ℕ) [NeZero q] {s : ℂ} (hs : 3/4 ≤ s.re) :
    ‖∑ p ∈ q.primeFactors, logDeriv (fun w : ℂ => 1 - (p:ℂ)^(-w)) s‖ ≤ 2 * Real.log q := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hprodpos : (0:ℝ) < ∏ p ∈ q.primeFactors, (p:ℝ) := by
    apply Finset.prod_pos
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).pos
    exact_mod_cast this
  have hdvd : (∏ p ∈ q.primeFactors, p) ≤ q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) (Nat.prod_primeFactors_dvd q)
  calc ‖∑ p ∈ q.primeFactors, logDeriv (fun w : ℂ => 1 - (p:ℂ)^(-w)) s‖
      ≤ ∑ p ∈ q.primeFactors, ‖logDeriv (fun w : ℂ => 1 - (p:ℂ)^(-w)) s‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ q.primeFactors, 2 * Real.log p :=
        Finset.sum_le_sum fun p hp =>
          logDeriv_factor_bound (Nat.prime_of_mem_primeFactors hp) hs
    _ = 2 * ∑ p ∈ q.primeFactors, Real.log p := by rw [Finset.mul_sum]
    _ = 2 * Real.log (∏ p ∈ q.primeFactors, (p:ℝ)) := by
        rw [Real.log_prod]
        intro p hp
        have := (Nat.prime_of_mem_primeFactors hp).pos
        positivity
    _ ≤ 2 * Real.log q := by
        have hcast : (∏ p ∈ q.primeFactors, (p:ℝ)) = ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
          push_cast
          rfl
        rw [hcast]
        have : Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ Real.log q := by
          apply Real.log_le_log
          · rw [← hcast]; exact hprodpos
          · exact_mod_cast hdvd
        linarith

end SolRegionBound

open SolRegionBound

set_option maxHeartbeats 2000000 in
open Classical in
theorem _root_.SWPort.Davenport.logDeriv_LFunction_region_bound_oai (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (E : Set ℂ),
        IsExceptionalSet c χ E →
          (∀ z ∈ E, (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ)
              ≤ C * Real.log (2 * q)) ∧
          ∀ s : ℂ, InRegion (c / 4) q s → 3 / 4 ≤ s.re → s ≠ 1 → s ∉ E →
            ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s
                + (if χ = 1 then 1 / (s - 1) else 0)
                - ∑ᶠ z ∈ E, (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) / (s - z)‖
              ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2 := by
  obtain ⟨C₁, hC₁pos, hPF⟩ := Davenport.logDeriv_LFunction_partial_fraction
  obtain ⟨Cz, hCzpos, hZeta⟩ := Davenport.zeta_logDeriv_region_bound c hc
  set K : ℝ := C₁ / c with hKdef
  have hKpos : 0 < K := by rw [hKdef]; exact div_pos hC₁pos hc
  set C : ℝ := 20 * (C₁ + 1) + Cz + 10 * (K + 1) + 10 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; linarith
  have hCd : C₁ ≤ C := by rw [hCdef]; linarith
  have hCa : 8 + 2 * C₁ ≤ C := by rw [hCdef]; linarith
  have hCb : 10 * C₁ + 4 * K ≤ C := by rw [hCdef]; linarith
  have hCc : Cz + 4 ≤ C := by rw [hCdef]; linarith
  refine ⟨C, hCpos, ?_⟩
  intro q _ χ E hE
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq0
  have hqpos : (0:ℝ) < (q:ℝ) := by linarith
  have hlog2q : (1:ℝ)/2 ≤ Real.log (2 * q) := by
    have : Real.log 2 ≤ Real.log (2 * q) := Real.log_le_log (by norm_num) (by linarith)
    linarith [half_le_log_two]
  by_cases hχ : χ = 1
  · -- ### Case B : principal character
    subst hχ
    have hEempty : E = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      exact (hE.2.1 z hz).2.2.2.2.2.2 rfl
    subst hEempty
    refine ⟨fun z hz => absurd hz (Set.notMem_empty z), ?_⟩
    intro s hreg hre hs1 _
    have hTC : ∀ w : ℂ, w ≠ 1 →
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) w
          = (∏ p ∈ q.primeFactors, (1 - (p:ℂ)^(-w))) * riemannZeta w := fun w hw =>
      DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hw
    have hζ0 : ∀ w : ℂ, w ≠ 1 → InRegion c q w → riemannZeta w ≠ 0 := by
      intro w hw hregw hzero
      have hL := hE.2.2 w hw hregw (Set.notMem_empty w)
      rw [hTC w hw, hzero, mul_zero] at hL
      exact hL rfl
    have hζne : riemannZeta s ≠ 0 := hζ0 s hs1 (inRegion_mono hq1 hc hreg)
    have hζd : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
    have hfne : ∀ p ∈ q.primeFactors, (1 - (p:ℂ)^(-s)) ≠ 0 := by
      intro p hp hzero
      have h2 := (norm_factor_bounds (Nat.prime_of_mem_primeFactors hp).two_le hre).2
      rw [hzero, norm_zero] at h2
      linarith
    have hfd : ∀ p ∈ q.primeFactors, DifferentiableAt ℂ (fun w : ℂ => 1 - (p:ℂ)^(-w)) s :=
      fun p hp => differentiableAt_factor (Nat.prime_of_mem_primeFactors hp).ne_zero s
    have hPs : (∏ p ∈ q.primeFactors, (1 - (p:ℂ)^(-s))) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr hfne
    have hdP : DifferentiableAt ℂ
        (fun w : ℂ => ∏ p ∈ q.primeFactors, (1 - (p:ℂ)^(-w))) s :=
      DifferentiableAt.fun_finsetProd hfd
    have hev : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)
        =ᶠ[nhds s] (fun w : ℂ => (∏ p ∈ q.primeFactors, (1 - (p:ℂ)^(-w))) * riemannZeta w) := by
      filter_upwards [isOpen_ne.mem_nhds hs1] with w hw using hTC w hw
    have hderiv : deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s
        = deriv (fun w : ℂ => (∏ p ∈ q.primeFactors, (1 - (p:ℂ)^(-w))) * riemannZeta w) s :=
      hev.deriv_eq
    have hlogeq : logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s
        = logDeriv (fun w : ℂ => (∏ p ∈ q.primeFactors, (1 - (p:ℂ)^(-w))) * riemannZeta w) s := by
      rw [logDeriv_apply, logDeriv_apply, hderiv, hTC s hs1]
    have hmul := logDeriv_mul (f := fun w : ℂ => ∏ p ∈ q.primeFactors, (1 - (p:ℂ)^(-w)))
      (g := riemannZeta) s hPs hζne hdP hζd
    have hprod := logDeriv_prod (𝕜 := ℂ) (𝕜' := ℂ)
      (f := fun (p : ℕ) (w : ℂ) => 1 - (p:ℂ)^(-w)) (s := q.primeFactors) (x := s) hfne hfd
    have key : deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s
          / DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s
        = (∑ p ∈ q.primeFactors, logDeriv (fun w : ℂ => 1 - (p:ℂ)^(-w)) s)
          + deriv riemannZeta s / riemannZeta s := by
      have := hlogeq.trans hmul
      rw [hprod] at this
      simpa only [logDeriv_apply] using this
    have h0 : (∑ᶠ z ∈ (∅ : Set ℂ),
        (analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) z : ℂ)
          / (s - z)) = 0 := finsum_mem_empty
    rw [if_pos rfl, h0, sub_zero, key]
    have heq : (∑ p ∈ q.primeFactors, logDeriv (fun w : ℂ => 1 - (p:ℂ)^(-w)) s)
          + deriv riemannZeta s / riemannZeta s + 1 / (s - 1)
        = (deriv riemannZeta s / riemannZeta s + 1 / (s - 1))
          + ∑ p ∈ q.primeFactors, logDeriv (fun w : ℂ => 1 - (p:ℂ)^(-w)) s := by ring
    rw [heq]
    have hb1 : ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖
        ≤ Cz * Real.log ((q:ℝ) * (|s.im| + 2)) ^ 2 := hZeta q hζ0 s hreg hre hs1
    have hb2 : ‖∑ p ∈ q.primeFactors, logDeriv (fun w : ℂ => 1 - (p:ℂ)^(-w)) s‖
        ≤ 2 * Real.log q := sum_logDeriv_factors_bound q hre
    have hlogq : Real.log q ≤ Real.log ((q:ℝ) * (|s.im| + 2)) := by
      apply Real.log_le_log hqpos
      nlinarith [abs_nonneg s.im]
    have hLthalf : (1:ℝ)/2 ≤ Real.log ((q:ℝ) * (|s.im| + 2)) := half_le_log_region hq1 s.im
    have htri := norm_add_le
      (deriv riemannZeta s / riemannZeta s + 1 / (s - 1))
      (∑ p ∈ q.primeFactors, logDeriv (fun w : ℂ => 1 - (p:ℂ)^(-w)) s)
    nlinarith [hb1, hb2, htri, hlogq, hLthalf, hCc,
      sq_nonneg (Real.log ((q:ℝ) * (|s.im| + 2)))]
  · -- ### Case A : non-principal character
    have hEfin : E.Finite := hE.1.finite
    set Efin : Finset ℂ := hEfin.toFinset with hEfindef
    have hmemE : ∀ z : ℂ, z ∈ Efin ↔ z ∈ E := fun z => hEfin.mem_toFinset
    have hcard : Efin.card ≤ 1 :=
      Finset.card_le_one.mpr fun a ha b hb => hE.1 ((hmemE a).mp ha) ((hmemE b).mp hb)
    -- the multiplicity bound
    have hmult : ∀ z ∈ E, (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ)
        ≤ C₁ * Real.log (2 * q) := by
      intro z hz
      obtain ⟨Z, hZ, hZsum, _⟩ := hPF q χ hχ 0
      have hzhalf := half_le_re hE hz
      obtain ⟨him, hre0, hre1, _, hLz, _, _⟩ := hE.2.1 z hz
      have hzZ : z ∈ Z := by
        have hmem : z ∈ ({ρ ∈ Metric.closedBall (2 + ((0:ℝ):ℂ) * Complex.I) (3/2) |
            DirichletCharacter.LFunction χ ρ = 0} : Set ℂ) := by
          refine ⟨?_, hLz⟩
          rw [Metric.mem_closedBall, dist_eq_norm]
          have hc0 : z - (2 + ((0:ℝ):ℂ) * Complex.I) = ((z.re - 2 : ℝ) : ℂ) := by
            apply Complex.ext <;> simp [him]
          rw [hc0, Complex.norm_real, Real.norm_eq_abs, abs_le]
          constructor <;> linarith
        rw [← hZ] at hmem
        exact hmem
      have h1 : (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ)
          ≤ ∑ ρ ∈ Z, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) :=
        Finset.single_le_sum
          (f := fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ))
          (fun i _ => by positivity) hzZ
      have h2 : (q:ℝ) * (|(0:ℝ)| + 2) = 2 * q := by rw [abs_zero]; ring
      rw [h2] at hZsum
      linarith
    refine ⟨fun z hz => le_trans (hmult z hz)
      (by nlinarith [hmult z hz, hCd, hlog2q, hC₁pos]), ?_⟩
    intro s hreg hre hs1 hsE
    have hfs : (∑ᶠ z ∈ E, (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) / (s - z))
        = ∑ z ∈ Efin, (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) / (s - z) := by
      rw [hEfindef]
      exact finsum_mem_eq_finite_toFinset_sum _ hEfin
    rw [if_neg hχ, add_zero, hfs]
    have hLthalf : (1:ℝ)/2 ≤ Real.log ((q:ℝ) * (|s.im| + 2)) := half_le_log_region hq1 s.im
    have hLtpos : 0 < Real.log ((q:ℝ) * (|s.im| + 2)) := log_region_pos hq1 s.im
    have hlog2qle : Real.log (2 * q) ≤ Real.log ((q:ℝ) * (|s.im| + 2)) := by
      apply Real.log_le_log (by linarith)
      nlinarith [abs_nonneg s.im]
    rcases le_or_gt 3 s.re with hbig | hsmall
    · -- far to the right
      have h1 : ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤ 2 :=
        logDeriv_norm_le_two χ hbig
      have h2 : ‖∑ z ∈ Efin,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) / (s - z)‖
            ≤ C₁ * Real.log (2 * q) := by
        calc ‖∑ z ∈ Efin, (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) / (s - z)‖
            ≤ ∑ z ∈ Efin, ‖(analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) / (s - z)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ _z ∈ Efin, C₁ * Real.log (2 * q) := by
              refine Finset.sum_le_sum ?_
              intro z hz
              have hzE : z ∈ E := (hmemE z).mp hz
              obtain ⟨_, _, hre1, _, _, _, _⟩ := hE.2.1 z hzE
              have hge : (1:ℝ) ≤ ‖s - z‖ := by
                calc (1:ℝ) ≤ s.re - z.re := by linarith
                  _ ≤ |s.re - z.re| := le_abs_self _
                  _ ≤ ‖s - z‖ := by
                      have := Complex.abs_re_le_norm (s - z)
                      simpa using this
              rw [norm_div]
              have hnc : ‖((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℕ) : ℂ)‖
                  = (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ) := by simp
              rw [hnc]
              calc (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ) / ‖s - z‖
                  ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ) :=
                    div_le_self (by positivity) hge
                _ ≤ C₁ * Real.log (2 * q) := hmult z hzE
          _ = (Efin.card : ℝ) * (C₁ * Real.log (2 * q)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ 1 * (C₁ * Real.log (2 * q)) := by
              apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
              positivity
          _ = C₁ * Real.log (2 * q) := one_mul _
      have htri := norm_sub_le
        (deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s)
        (∑ z ∈ Efin, (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) / (s - z))
      have hLtsq : Real.log ((q:ℝ) * (|s.im| + 2))
          ≤ 2 * Real.log ((q:ℝ) * (|s.im| + 2)) ^ 2 := by nlinarith [hLthalf]
      have hone : (1:ℝ) ≤ 4 * Real.log ((q:ℝ) * (|s.im| + 2)) ^ 2 := by nlinarith [hLthalf]
      have hstep1 : C₁ * Real.log (2 * q) ≤ C₁ * Real.log ((q:ℝ) * (|s.im| + 2)) :=
        mul_le_mul_of_nonneg_left hlog2qle hC₁pos.le
      have hstep2 : C₁ * Real.log ((q:ℝ) * (|s.im| + 2))
          ≤ C₁ * (2 * Real.log ((q:ℝ) * (|s.im| + 2)) ^ 2) :=
        mul_le_mul_of_nonneg_left hLtsq hC₁pos.le
      have hstep3 : (8 + 2 * C₁) * Real.log ((q:ℝ) * (|s.im| + 2)) ^ 2
          ≤ C * Real.log ((q:ℝ) * (|s.im| + 2)) ^ 2 :=
        mul_le_mul_of_nonneg_right hCa (sq_nonneg _)
      nlinarith [h1, h2, htri, hone, hstep1, hstep2, hstep3]
    · -- the substantive range `3/4 ≤ σ < 3`
      obtain ⟨Z, hZ, hZsum, hZbd⟩ := hPF q χ hχ s.im
      have hsball : s ∈ Metric.closedBall (2 + ((s.im : ℝ) : ℂ) * Complex.I) (7/5) := by
        rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_center, abs_le]
        constructor <;> linarith
      have hLs : DirichletCharacter.LFunction χ s ≠ 0 :=
        hE.2.2 s hs1 (inRegion_mono hq1 hc hreg) hsE
      have hA := hZbd s hsball hLs
      rw [logDeriv_apply] at hA
      -- decomposition of the two sums
      have hdecomp :
          (∑ ρ ∈ Z, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ))
            - ∑ z ∈ Efin, (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) / (s - z)
          = (∑ ρ ∈ Z \ Efin,
                (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ))
            - ∑ z ∈ Efin \ Z,
                (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) / (s - z) := by
        rw [← Finset.sum_inter_add_sum_sdiff Z Efin
              (fun w => (analyticOrderNatAt (DirichletCharacter.LFunction χ) w : ℂ) / (s - w)),
            ← Finset.sum_inter_add_sum_sdiff Efin Z
              (fun w => (analyticOrderNatAt (DirichletCharacter.LFunction χ) w : ℂ) / (s - w)),
            Finset.inter_comm Efin Z]
        ring
      have hsplit :
          deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s
            - ∑ z ∈ Efin, (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) / (s - z)
          = (deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s
              - ∑ ρ ∈ Z, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ))
            + ((∑ ρ ∈ Z \ Efin,
                  (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ))
              - ∑ z ∈ Efin \ Z,
                  (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) / (s - z)) := by
        rw [← hdecomp]; ring
      -- bound on the far zeros
      have hZfar : ‖∑ ρ ∈ Z \ Efin,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖
            ≤ 4 * K * Real.log ((q:ℝ) * (|s.im| + 2)) ^ 2 := by
        have hfac0 : (0:ℝ) ≤ 4 * Real.log ((q:ℝ) * (|s.im| + 2)) / c := by
          apply div_nonneg <;> linarith
        have hterm : ∀ ρ ∈ Z \ Efin,
            ‖(analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖
              ≤ (4 * Real.log ((q:ℝ) * (|s.im| + 2)) / c)
                  * (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
          intro ρ hρ
          rw [Finset.mem_sdiff] at hρ
          obtain ⟨hρZ, hρE⟩ := hρ
          have hmem : ρ ∈ ({w ∈ Metric.closedBall (2 + ((s.im : ℝ) : ℂ) * Complex.I) (3/2) |
              DirichletCharacter.LFunction χ w = 0} : Set ℂ) := by
            rw [← hZ]; exact hρZ
          obtain ⟨hball, hLρ⟩ := hmem
          have hρ1 : ρ ≠ 1 := by
            intro h
            rw [h] at hLρ
            exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
              (by simp) hLρ
          have hnotreg : ¬ InRegion c q ρ := fun hregρ =>
            hE.2.2 ρ hρ1 hregρ (fun h => hρE ((hmemE ρ).mpr h)) hLρ
          unfold InRegion regionBoundary at hnotreg
          rw [not_le] at hnotreg
          -- the imaginary parts are close
          have hdist : ‖ρ - (2 + ((s.im : ℝ) : ℂ) * Complex.I)‖ ≤ 3/2 := by
            have h := Metric.mem_closedBall.mp hball
            rwa [dist_eq_norm] at h
          have himdist : |ρ.im - s.im| ≤ 3/2 := by
            have h2 := Complex.abs_im_le_norm (ρ - (2 + ((s.im : ℝ) : ℂ) * Complex.I))
            have h3 : (ρ - (2 + ((s.im : ℝ) : ℂ) * Complex.I)).im = ρ.im - s.im := by simp
            rw [h3] at h2
            linarith
          have hab : |ρ.im| ≤ |s.im| + 3/2 := by
            have := abs_sub_abs_le_abs_sub ρ.im s.im
            linarith
          have hlogρpos : 0 < Real.log ((q:ℝ) * (|ρ.im| + 2)) := log_region_pos hq1 ρ.im
          have hstep1 : (q:ℝ) * (|ρ.im| + 2) ≤ ((q:ℝ) * (|s.im| + 2))^2 := by
            have hbig2 : (2:ℝ) ≤ (q:ℝ) * (|s.im| + 2) := by nlinarith [abs_nonneg s.im]
            have h1 : |ρ.im| + 2 ≤ 2 * (|s.im| + 2) := by linarith [abs_nonneg s.im]
            nlinarith [hq1, abs_nonneg s.im, abs_nonneg ρ.im]
          have hlogρ : Real.log ((q:ℝ) * (|ρ.im| + 2))
              ≤ 2 * Real.log ((q:ℝ) * (|s.im| + 2)) := by
            calc Real.log ((q:ℝ) * (|ρ.im| + 2))
                ≤ Real.log (((q:ℝ) * (|s.im| + 2))^2) := by
                  apply Real.log_le_log _ hstep1
                  nlinarith [abs_nonneg ρ.im, hq1]
              _ = 2 * Real.log ((q:ℝ) * (|s.im| + 2)) := by
                  rw [Real.log_pow]; norm_num
          have hcdiv : c / (2 * Real.log ((q:ℝ) * (|s.im| + 2)))
              ≤ c / Real.log ((q:ℝ) * (|ρ.im| + 2)) := by
            rw [div_le_div_iff₀ (by linarith) hlogρpos]
            nlinarith [hc, hlogρ]
          have hregs : 1 - c / 4 / Real.log ((q:ℝ) * (|s.im| + 2)) ≤ s.re := by
            unfold InRegion regionBoundary at hreg
            exact hreg
          have e1 : c / 4 / Real.log ((q:ℝ) * (|s.im| + 2))
              = c / (4 * Real.log ((q:ℝ) * (|s.im| + 2))) := by rw [div_div]
          have e2 : c / (2 * Real.log ((q:ℝ) * (|s.im| + 2)))
              - c / (4 * Real.log ((q:ℝ) * (|s.im| + 2)))
              = c / (4 * Real.log ((q:ℝ) * (|s.im| + 2))) := by
            field_simp
            ring
          have hgap : c / (4 * Real.log ((q:ℝ) * (|s.im| + 2))) ≤ s.re - ρ.re := by
            rw [e1] at hregs
            linarith
          have hgappos : 0 < c / (4 * Real.log ((q:ℝ) * (|s.im| + 2))) := by
            apply div_pos hc
            linarith
          have hnormge : c / (4 * Real.log ((q:ℝ) * (|s.im| + 2))) ≤ ‖s - ρ‖ := by
            calc c / (4 * Real.log ((q:ℝ) * (|s.im| + 2))) ≤ s.re - ρ.re := hgap
              _ ≤ |s.re - ρ.re| := le_abs_self _
              _ ≤ ‖s - ρ‖ := by
                  have := Complex.abs_re_le_norm (s - ρ)
                  simpa using this
          have hnormpos : (0:ℝ) < ‖s - ρ‖ := lt_of_lt_of_le hgappos hnormge
          have hfac : (1:ℝ) ≤ (4 * Real.log ((q:ℝ) * (|s.im| + 2)) / c) * ‖s - ρ‖ := by
            have h1 : (4 * Real.log ((q:ℝ) * (|s.im| + 2)) / c)
                * (c / (4 * Real.log ((q:ℝ) * (|s.im| + 2)))) = 1 := by
              field_simp
            calc (1:ℝ) = (4 * Real.log ((q:ℝ) * (|s.im| + 2)) / c)
                  * (c / (4 * Real.log ((q:ℝ) * (|s.im| + 2)))) := h1.symm
              _ ≤ (4 * Real.log ((q:ℝ) * (|s.im| + 2)) / c) * ‖s - ρ‖ :=
                  mul_le_mul_of_nonneg_left hnormge hfac0
          rw [norm_div]
          have hnc : ‖((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℂ)‖
              = (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by simp
          rw [hnc, div_le_iff₀ hnormpos]
          nlinarith [hfac, Nat.cast_nonneg (α := ℝ)
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ)]
        calc ‖∑ ρ ∈ Z \ Efin,
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖
            ≤ ∑ ρ ∈ Z \ Efin,
                ‖(analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ ρ ∈ Z \ Efin, (4 * Real.log ((q:ℝ) * (|s.im| + 2)) / c)
                * (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) :=
              Finset.sum_le_sum hterm
          _ = (4 * Real.log ((q:ℝ) * (|s.im| + 2)) / c)
                * ∑ ρ ∈ Z \ Efin, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
              rw [Finset.mul_sum]
          _ ≤ (4 * Real.log ((q:ℝ) * (|s.im| + 2)) / c)
                * ∑ ρ ∈ Z, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
              apply mul_le_mul_of_nonneg_left _ hfac0
              apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
              intro i _ _
              positivity
          _ ≤ (4 * Real.log ((q:ℝ) * (|s.im| + 2)) / c)
                * (C₁ * Real.log ((q:ℝ) * (|s.im| + 2))) :=
              mul_le_mul_of_nonneg_left hZsum hfac0
          _ = 4 * K * Real.log ((q:ℝ) * (|s.im| + 2)) ^ 2 := by
              rw [hKdef]; field_simp
      -- bound on the exceptional zero if it is outside the disc
      have hEfar : ‖∑ z ∈ Efin \ Z,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) / (s - z)‖
            ≤ 4 * (C₁ * Real.log (2 * q)) := by
        have hsc : ‖s - (2 + ((s.im : ℝ) : ℂ) * Complex.I)‖ ≤ 5/4 := by
          rw [norm_sub_center, abs_le]
          constructor <;> linarith
        have hterm : ∀ z ∈ Efin \ Z,
            ‖(analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) / (s - z)‖
              ≤ 4 * (C₁ * Real.log (2 * q)) := by
          intro z hz
          rw [Finset.mem_sdiff] at hz
          obtain ⟨hzE, hzZ⟩ := hz
          have hzE' : z ∈ E := (hmemE z).mp hzE
          obtain ⟨_, _, _, _, hLz, _, _⟩ := hE.2.1 z hzE'
          have hzball : ¬ (z ∈ Metric.closedBall (2 + ((s.im : ℝ) : ℂ) * Complex.I) (3/2)) := by
            intro hb
            apply hzZ
            have hmem : z ∈ ({w ∈ Metric.closedBall (2 + ((s.im : ℝ) : ℂ) * Complex.I) (3/2) |
                DirichletCharacter.LFunction χ w = 0} : Set ℂ) := ⟨hb, hLz⟩
            rw [← hZ] at hmem
            exact hmem
          rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hzball
          have hge : (1:ℝ)/4 ≤ ‖s - z‖ := by
            have h := norm_sub_norm_le (z - (2 + ((s.im : ℝ) : ℂ) * Complex.I))
              (s - (2 + ((s.im : ℝ) : ℂ) * Complex.I))
            have he : (z - (2 + ((s.im : ℝ) : ℂ) * Complex.I))
                - (s - (2 + ((s.im : ℝ) : ℂ) * Complex.I)) = z - s := by ring
            rw [he] at h
            have hzs : ‖z - s‖ = ‖s - z‖ := norm_sub_rev _ _
            rw [hzs] at h
            linarith
          have hnormpos : (0:ℝ) < ‖s - z‖ := by linarith
          rw [norm_div]
          have hnc : ‖((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℕ) : ℂ)‖
              = (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ) := by simp
          rw [hnc, div_le_iff₀ hnormpos]
          nlinarith [hmult z hzE', hge,
            Nat.cast_nonneg (α := ℝ) (analyticOrderNatAt (DirichletCharacter.LFunction χ) z),
            hC₁pos, hlog2q]
        calc ‖∑ z ∈ Efin \ Z,
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) / (s - z)‖
            ≤ ∑ z ∈ Efin \ Z,
                ‖(analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) / (s - z)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ _z ∈ Efin \ Z, 4 * (C₁ * Real.log (2 * q)) := Finset.sum_le_sum hterm
          _ = ((Efin \ Z).card : ℝ) * (4 * (C₁ * Real.log (2 * q))) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ 1 * (4 * (C₁ * Real.log (2 * q))) := by
              apply mul_le_mul_of_nonneg_right
              · have : (Efin \ Z).card ≤ 1 :=
                  le_trans (Finset.card_le_card Finset.sdiff_subset) hcard
                exact_mod_cast this
              · positivity
          _ = 4 * (C₁ * Real.log (2 * q)) := one_mul _
      rw [hsplit]
      have htri1 := norm_add_le
        (deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s
          - ∑ ρ ∈ Z, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ))
        ((∑ ρ ∈ Z \ Efin,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ))
          - ∑ z ∈ Efin \ Z,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) / (s - z))
      have htri2 := norm_sub_le
        (∑ ρ ∈ Z \ Efin,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ))
        (∑ z ∈ Efin \ Z,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) / (s - z))
      have hLtsq : Real.log ((q:ℝ) * (|s.im| + 2))
          ≤ 2 * Real.log ((q:ℝ) * (|s.im| + 2)) ^ 2 := by nlinarith [hLthalf]
      nlinarith [hA, hZfar, hEfar, htri1, htri2, hlog2qle, hLthalf, hLtsq, hCb, hC₁pos, hKpos,
        mul_le_mul_of_nonneg_left hLtsq hC₁pos.le,
        mul_le_mul_of_nonneg_right hCb (sq_nonneg (Real.log ((q:ℝ) * (|s.im| + 2))))]

end SWPort
end

theorem solution : type_of% @SWPort.Davenport.logDeriv_LFunction_region_bound_oai := @SWPort.Davenport.logDeriv_LFunction_region_bound_oai
