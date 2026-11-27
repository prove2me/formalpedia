-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.measure_div_le_ncard_inter_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:28:49.669199+00:00
-- url     : https://prove2.me/submissions/1fbe7375-2665-4a91-b5e3-6874013f3499

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_CountZSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_fiber_count_le_ncard_inter_lattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Module
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (S : Set E)
    (hconv : Convex ℝ S) (hsymm : ∀ x ∈ S, -x ∈ S) (hb : Bornology.IsBounded S)
    (hm : MeasurableSet S) :
    (μ S).toReal / (2 ^ finrank ℝ E * ZLattice.covolume L μ) ≤ ((S ∩ (L : Set E)).ncard : ℝ) := by
  classical
  haveI : MeasureTheory.VAddInvariantMeasure L E μ :=
    ⟨fun g s _ => by simp only [Submodule.vadd_def, vadd_eq_add]; exact measure_preimage_add μ (g : E) s⟩
  have hF : MeasureTheory.IsAddFundamentalDomain L
      (ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)) μ :=
    ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) μ
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain L μ hF
  have hpos : 0 < ZLattice.covolume L μ := ZLattice.covolume_pos L μ
  have hTm : MeasurableSet ((2⁻¹ : ℝ) • S) := hm.const_smul₀ _
  have hle : μ ((2⁻¹ : ℝ) • S) ≤ ((S ∩ (L : Set E)).ncard : ENNReal)
      * μ (ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)) := by
    rw [hF.measure_eq_tsum ((2⁻¹ : ℝ) • S)]
    calc ∑' g : L, μ ((g +ᵥ (2⁻¹ : ℝ) • S)
          ∩ ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L))
        = ∑' g : L, ∫⁻ y in ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L),
            ((g +ᵥ (2⁻¹ : ℝ) • S).indicator 1 y : ENNReal) ∂μ := by
          congr 1; funext g
          rw [lintegral_indicator_one (hTm.const_vadd g), Measure.restrict_apply (hTm.const_vadd g)]
      _ = ∫⁻ y in ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L),
            ∑' g : L, ((g +ᵥ (2⁻¹ : ℝ) • S).indicator 1 y : ENNReal) ∂μ :=
          (lintegral_tsum fun g => (measurable_one.indicator (hTm.const_vadd g)).aemeasurable).symm
      _ ≤ ∫⁻ _ in ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L),
            ((S ∩ (L : Set E)).ncard : ENNReal) ∂μ :=
          lintegral_mono fun y => fiber_count_le_ncard_inter_lattice L S hconv hsymm hb y
      _ = _ := setLIntegral_const _ _
  have hFfin : μ (ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)) ≠ ⊤ := by
    intro h
    rw [hcov, Measure.real, h] at hpos
    simp at hpos
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hFfin) hle
  rw [Measure.addHaar_smul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_nonneg (by positivity), inv_pow, ENNReal.toReal_natCast] at hreal
  have h2 : (0 : ℝ) < 2 ^ finrank ℝ E := by positivity
  rw [inv_mul_le_iff₀ h2] at hreal
  rw [div_le_iff₀ (mul_pos h2 hpos), hcov, Measure.real]
  calc (μ S).toReal ≤ _ := hreal
    _ = _ := by ring
end ReciprocityTheory.GeometryOfNumbersTheory
