-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_maDensity_bsmul_f913413ea179
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:41:05.257883+00:00
-- url     : https://prove2.me/submissions/25fcc179-c99a-4548-bfa8-1c7760cc0eb5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsPosPartLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsDegZeroSmooth_mul_ac2f2d59f4e1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_cxHessian_add_re
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_cxHessian_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isOpen_blockNonzero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_pot_contDiffAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.PtsPosPartLocal
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
variable {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
namespace GroundTheory.Heights₂.Heights.PtsPosPartLocal
theorem _root_.solution {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {γ γ' : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {c : K → (Fin e → ℂ) → ℂ} {y : Fin e → ℂ}
    (hγ : AnalyticAt ℂ γ y) (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0) (hcan : ∀ k, AnalyticAt ℂ (c k) y)
    (hc0 : ∀ k, c k y ≠ 0) (hrel : ∀ᶠ y' in 𝓝 y, γ' y' = bsmul (fun k => c k y') (γ y')) :
    maDensity (fun j y' => pot L j (γ' y')) y = maDensity (fun j y' => pot L j (γ y')) y := by
  have hcont : ∀ᶠ y' in 𝓝 y, ∀ k, ∃ i, γ y' ⟨k, i⟩ ≠ 0 :=
    hγ.continuousAt.eventually (isOpen_blockNonzero.mem_nhds hy)
  have hcne : ∀ᶠ y' in 𝓝 y, ∀ k, c k y' ≠ 0 :=
    eventually_all.mpr fun k => (hcan k).continuousAt.eventually_ne (hc0 k)
  have hH : ∀ j, cxHessian (fun y' => pot L j (γ' y')) y = cxHessian (fun y' => pot L j (γ y')) y := by
    intro j
    set G : (Fin e → ℂ) → ℂ := fun y' => ∑ k, (((L j).a k : ℝ) : ℂ) * Complex.log (c k y' / c k y)
    set C : ℝ := ∑ k, ((L j).a k : ℝ) * Real.log ‖c k y‖
    have hGan : AnalyticAt ℂ G y := by
      refine Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul ?_
      refine ((hcan k).div analyticAt_const (hc0 k)).clog ?_
      show c k y / c k y ∈ Complex.slitPlane
      rw [div_self (hc0 k)]
      exact Complex.one_mem_slitPlane
    have heq : (fun y' => pot L j (γ' y')) =ᶠ[𝓝 y] fun y' => pot L j (γ y') + (G y').re + C := by
      filter_upwards [hrel, hcont, hcne] with y' hr hγ0 hc
      have hpos : 0 < (L j).h (γ y') := (L j).pos _ hγ0
      have hsm : (L j).h (bsmul (fun k => c k y') (γ y')) =
          (∏ k, ‖c k y'‖ ^ (L j).a k) * (L j).h (γ y') := (L j).smul _ _ hc
      have hne : ∀ k, ‖c k y'‖ ^ (L j).a k ≠ 0 := fun k =>
        zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
      have hterm : ∀ k, ((((L j).a k : ℝ) : ℂ) * Complex.log (c k y' / c k y)).re =
          ((L j).a k : ℝ) * Real.log ‖c k y'‖ - ((L j).a k : ℝ) * Real.log ‖c k y‖ := by
        intro k
        rw [Complex.re_ofReal_mul, Complex.log_re, norm_div,
          Real.log_div (norm_ne_zero_iff.mpr (hc k)) (norm_ne_zero_iff.mpr (hc0 k)), mul_sub]
      simp only [pot, G, C]
      rw [hr, hsm, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => hne k) hpos.ne',
        Real.log_prod (fun k _ => hne k), Complex.re_sum]
      simp only [Real.log_zpow, hterm, Finset.sum_sub_distrib]
      ring
    rw [cxHessian_congr heq, cxHessian_add_re (φ := fun y' => pot L j (γ y')) C
      (pot_contDiffAt (hL j) hγ hy) hGan]
  simp only [maDensity, hH]
end GroundTheory.Heights₂.Heights.PtsPosPartLocal
