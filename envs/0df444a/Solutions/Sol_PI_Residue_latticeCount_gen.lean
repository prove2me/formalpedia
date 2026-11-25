-- Prove2me | solution 1 for PI.Residue.latticeCount_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:13:42.952665+00:00
-- url     : https://prove2.me/submissions/65233f42-95fc-4755-a5ee-37bafa649854

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_LatticeCountGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding MeasureTheory
open scoped ENNReal Pointwise Classical
noncomputable section
open PI PI.Residue
namespace PI.Residue
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (B : Set E) (hB : MeasurableSet B) :
    μ B ≤ (∑' x : L, (B - B).indicator (fun _ => (1 : ℝ≥0∞)) (x : E)) *
      ENNReal.ofReal (ZLattice.covolume L μ) := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  have hF := ZLattice.isAddFundamentalDomain b μ
  set F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ) with hFdef
  have hfin : μ F ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hcov : ENNReal.ofReal (ZLattice.covolume L μ) = μ F := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L μ hF, measureReal_def,
      ENNReal.ofReal_toReal hfin]
  haveI : VAddInvariantMeasure L E μ :=
    ⟨fun c s _ => measure_preimage_add μ (c : E) s⟩
  have hm : ∀ g : L, MeasurableSet (g +ᵥ B) := fun g => hB.const_vadd g
  have h2 : ∀ g : L, μ ((g +ᵥ B) ∩ F) =
      ∫⁻ t in F, (g +ᵥ B).indicator (fun _ => (1 : ℝ≥0∞)) t ∂μ := by
    intro g
    rw [lintegral_indicator_const (hm g), one_mul, Measure.restrict_apply (hm g)]
  have hpt : ∀ t : E, ∑' g : L, (g +ᵥ B).indicator (fun _ => (1 : ℝ≥0∞)) t ≤
      ∑' x : L, (B - B).indicator (fun _ => (1 : ℝ≥0∞)) (x : E) := by
    intro t
    by_cases h : ∃ g0 : L, t ∈ g0 +ᵥ B
    · obtain ⟨g0, hg0⟩ := h
      rw [← (Equiv.addRight g0).tsum_eq]
      refine ENNReal.tsum_le_tsum fun g => ?_
      by_cases hg : t ∈ ((Equiv.addRight g0) g) +ᵥ B
      · have : (g : E) ∈ B - B := by
          obtain ⟨b0, hb0, e0⟩ := hg0
          obtain ⟨b1, hb1, e1⟩ := hg
          refine ⟨b0, hb0, b1, hb1, ?_⟩
          have e0' : (g0 : E) + b0 = t := e0
          have e1' : ((g : E) + (g0 : E)) + b1 = t := e1
          have : (g0 : E) + b0 = ((g : E) + (g0 : E)) + b1 := e0'.trans e1'.symm
          rw [sub_eq_iff_eq_add]
          apply add_left_cancel (a := (g0 : E))
          rw [this]; abel
        rw [Set.indicator_of_mem hg, Set.indicator_of_mem this]
      · rw [Set.indicator_of_notMem hg]; exact zero_le
    · push Not at h
      have : ∀ g : L, (g +ᵥ B).indicator (fun _ => (1 : ℝ≥0∞)) t = 0 :=
        fun g => Set.indicator_of_notMem (h g) _
      simp [this]
  calc μ B = ∑' g : L, μ ((g +ᵥ B) ∩ F) := hF.measure_eq_tsum B
    _ = ∫⁻ t in F, ∑' g : L, (g +ᵥ B).indicator (fun _ => (1 : ℝ≥0∞)) t ∂μ := by
        rw [lintegral_tsum fun g => (measurable_const.indicator (hm g)).aemeasurable]
        exact tsum_congr h2
    _ ≤ ∫⁻ _ in F, ∑' x : L, (B - B).indicator (fun _ => (1 : ℝ≥0∞)) (x : E) ∂μ :=
        lintegral_mono hpt
    _ = _ := by rw [setLIntegral_const, hcov]
end PI.Residue
