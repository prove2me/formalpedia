-- Prove2me | solution 1 for RH.Transport.actual_uniform_common_probe
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Himan
-- created : 2026-11-15T03:28:29.971455+00:00
-- url     : https://prove2.me/submissions/9911dfb6-1d5d-43db-b562-03472e521a6a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Transport_PhysicalAnalytic_HeckeBridge
import Definitions.Def_Transport_DataProbe
import Definitions.Def_Transport_PhysicalHigh_MomentBound
import Theorems.Thm_RH_Transport_TunedCandidate_boundary_value
import Theorems.Thm_RH_Transport_TunedCandidate_signal_intercept_value
import Theorems.Thm_RH_Transport_TunedCandidate_boundary_eq_geometry
import Theorems.Thm_RH_Transport_TunedCandidate_p_lt_one_thousandth
import Theorems.Thm_RH_Transport_PhysicalHigh_exists_tuned_data
import Theorems.Thm_RH_Transport_PhysicalHigh_exists_tuned_source_data
import Theorems.Thm_RH_Transport_PhysicalHigh_exists_tuned_count_parameters
import Theorems.Thm_RH_Transport_PhysicalHigh_data_chosen_moments
import Theorems.Thm_RH_Transport_PhysicalHigh_fixed_high_bound
import Theorems.Thm_RH_Transport_PhysicalAnalytic_actual_source_analytic_transported
import Theorems.Thm_RH_Transport_dataProbe_low
open OAI.SevenEighths

set_option autoImplicit false

/-! Assembly of the actual common probe (LW56e2, `Transport/CommonProbe.lean`).
Every arithmetic and analytic input is an imported lemma; only the original
7/8 family ceiling is a hypothesis here. -/

namespace RH.Transport.CommonProbeAssembly
noncomputable section
open scoped Classical
open Filter Asymptotics
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeFinalAssembly PrincipalSignalComparison

/-- The tuned signal exponent is affine of slope one. -/
lemma tuned_signal_add_shift (s : ℝ) :
    TunedCandidate.signal s = s + TunedCandidate.signal 0 := by
  rw [TunedCandidate.signal_intercept_value s, TunedCandidate.signal_intercept_value 0]
  ring

/-- An eventual norm bound by a constant multiple of a real power is a Big-O bound. -/
lemma isBigO_rpow_of_eventual_norm_bound (f : ℝ → ℂ) (r : ℝ)
    (h : ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ‖f Z‖ ≤ C * Z ^ r) :
    f =O[atTop] (fun Z : ℝ => Z ^ r) := by
  obtain ⟨C, _, hb⟩ := h
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hb, eventually_ge_atTop (0 : ℝ)] with Z hb hZ
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hZ r)] using hb

/-- The source form of the statement, in terms of the tuned constants. -/
theorem actual_uniform_common_probe
    (hceiling : HeckeZeroSupremum.beta ≤ 7 / 8) :
    PhysicalAnalytic.UniformCommonProbe TunedCandidate.B (TunedCandidate.signal 0) := by
  intro hβ
  obtain ⟨D⟩ := PhysicalHigh.exists_tuned_data 0 1 (by norm_num)
  obtain ⟨seed, F, _, hfirst⟩ :=
    PhysicalHigh.exists_tuned_source_data D.P.e D.P.e_pos ∅ (by simp)
  have hloss : 0 < PhysicalHigh.reservedLoss := by norm_num
  obtain ⟨counts⟩ :=
    PhysicalHigh.exists_tuned_count_parameters F PhysicalHigh.reservedLoss hloss
  have hβ51 : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta := by
    have hB := TunedCandidate.boundary_value
    linarith
  obtain ⟨τ, hτ, hτd, hτcost, hτt, hτ2, hτeps, hsource⟩ :=
    PhysicalHigh.data_chosen_moments F D counts hβ51 hceiling
  obtain ⟨C, hC, hhigh⟩ := PhysicalHigh.fixed_high_bound hβ hceiling D F hfirst counts τ
    hτ hτd hτcost hτt hτ2 hτeps
  let ω := (HeckeZeroSupremum.beta - TunedCandidate.B) / 2
  have hω : 0 < ω := by dsimp [ω]; linarith
  have hωgap : ω < HeckeZeroSupremum.beta - TunedCandidate.B := by dsimp [ω]; linarith
  refine ⟨ω, D.P.sigma, hω, hωgap, D.P.sigma_pos, ?_⟩
  intro η _hprimitive
  obtain ⟨hmask, hH, hHbound⟩ := PhysicalAnalytic.actual_source_analytic_transported
    TunedCandidate.p TunedCandidate.p_lt_one_thousandth F.S F.exclusions η
  rw [← TunedCandidate.boundary_eq_geometry] at hH hHbound
  refine ⟨η.excludePrimes F.S F.exclusions.prime, sourceCorrection η F.S,
    dataProbe F D η, hmask, hH, hHbound, ?_, ?_⟩
  · simpa only [tuned_signal_add_shift TunedCandidate.B] using dataProbe_low F D ω hω η
  · obtain ⟨Ct, hCt, hbound⟩ := hhigh η
    obtain ⟨Cm, hCm, hmoment⟩ := hsource η
    apply isBigO_rpow_of_eventual_norm_bound
    refine ⟨Ct + C * Cm * (η.modulus.absNorm : ℝ) ^ (2 * D.P.eps), by positivity, ?_⟩
    filter_upwards [hbound, hmoment] with Z hb hm
    simpa only [tuned_signal_add_shift HeckeZeroSupremum.beta] using hb Cm hCm.le hm.2

end
end RH.Transport.CommonProbeAssembly

theorem solution
    (hceiling : OAI.SevenEighths.HeckeZeroSupremum.beta ≤ 7 / 8) :
    RH.Transport.PhysicalAnalytic.UniformCommonProbe
      (4374785349 / 5000000000) (-2147607 / 3125000) := by
  have h := RH.Transport.CommonProbeAssembly.actual_uniform_common_probe hceiling
  have hB : RH.Transport.TunedCandidate.B = 4374785349 / 5000000000 :=
    RH.Transport.TunedCandidate.boundary_value
  have hc : RH.Transport.TunedCandidate.signal 0 = -2147607 / 3125000 := by
    rw [RH.Transport.TunedCandidate.signal_intercept_value 0]
    norm_num
  rwa [hB, hc] at h
