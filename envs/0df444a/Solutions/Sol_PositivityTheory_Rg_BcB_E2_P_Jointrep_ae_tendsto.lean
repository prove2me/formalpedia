-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.Jointrep.ae_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:42:01.716706+00:00
-- url     : https://prove2.me/submissions/1a85b994-436b-4615-82c1-5e296dea10ed

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Jointrep
import Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Jointrep_geom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P
open PositivityTheory.Rg.BcB.E2.P.Jointrep
namespace PositivityTheory.Rg.BcB.E2.P.Jointrep
theorem _root_.solution {S : Type} [MeasurableSpace S] {ν : Measure S} (h : Lp ℂ 2 ν) (v : ℕ → Lp ℂ 2 ν)
    (hv : ∀ j, edist h (v j) < (2⁻¹ : ℝ≥0∞) ^ j) :
    ∀ᵐ s ∂ν, Tendsto (fun j => (v j : S → ℂ) s) atTop (𝓝 (h s)) := by
  let g : ℕ → S → ℝ≥0∞ := fun j s => ‖(v j : S → ℂ) s - h s‖ₑ ^ (2:ℝ)
  have gm : ∀ j, Measurable (g j) := fun j =>
    (((Lp.stronglyMeasurable (v j)).measurable.sub (Lp.stronglyMeasurable h).measurable).enorm).pow_const _
  have hint : ∀ j, ∫⁻ s, g j s ∂ν ≤ ((2⁻¹ : ℝ≥0∞) ^ j) ^ 2 := by
    intro j
    have e1 : ∫⁻ s, g j s ∂ν = eLpNorm' (fun s => (v j : S → ℂ) s - h s) 2 ν ^ (2:ℝ) :=
      lintegral_rpow_enorm_eq_rpow_eLpNorm' two_pos
    have e2 : eLpNorm' (fun s => (v j : S → ℂ) s - h s) 2 ν = edist (v j) h := by
      rw [Lp.edist_def, eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top]
      simp only [ENNReal.toReal_ofNat]
      rfl
    rw [e1, e2, ENNReal.rpow_two]
    gcongr
    rw [edist_comm]; exact (hv j).le
  have hsum : ∫⁻ s, ∑' j, g j s ∂ν ≠ ⊤ := by
    rw [lintegral_tsum fun j => (gm j).aemeasurable]
    exact ne_top_of_le_ne_top geom (ENNReal.tsum_le_tsum hint)
  filter_upwards [ae_lt_top (Measurable.ennreal_tsum gm) hsum] with s hs
  have h0 : Tendsto (fun j => g j s) atTop (𝓝 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hs.ne
  have h1 : Tendsto (fun j => (g j s) ^ (2⁻¹ : ℝ)) atTop (𝓝 0) := by
    have := ((ENNReal.continuous_rpow_const (y := (2⁻¹:ℝ))).tendsto 0).comp h0
    simpa [Function.comp_def] using this
  rw [tendsto_iff_edist_tendsto_0]
  refine h1.congr fun j => ?_
  simp only [g, edist_eq_enorm_sub]
  rw [← ENNReal.rpow_mul]
  norm_num
end PositivityTheory.Rg.BcB.E2.P.Jointrep
