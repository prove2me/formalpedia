-- Prove2me | solution 1 for PI.QuotMeasUniqW.qLift_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:36:44.020641+00:00
-- url     : https://prove2.me/submissions/1420293b-be82-4643-bd94-2dc0ce4f7d5b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QmuWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientMeasureUniqueness_QLiftIsMulLeftInvariant
import Theorems.Thm_PI_QuotMeasUniqW_hAvg_indicator_le
import Theorems.Thm_PI_QuotMeasUniqW_lintegral_qLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Pointwise
open scoped ENNReal
open PI PI.QuotMeasUniqW
namespace PI.QuotMeasUniqW
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (hH : IsClosed (H : Set G)) (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts ν] (ρ : Measure (G ⧸ H))
    (hρK : ∀ K : Set (G ⧸ H), IsCompact K → ρ K < ⊤) : IsFiniteMeasureOnCompacts (qLift ν ρ) := by
  refine ⟨?_⟩
  intro K hK
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hi : Measurable (K.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hKm
  have hKK : IsCompact (K⁻¹ * K) := hK.inv.mul hK
  have hc : IsCompact {h : H | (h : G) ∈ K⁻¹ * K} := by
    exact hH.isClosedEmbedding_subtypeVal.isCompact_preimage hKK
  have hM : ν {h : H | (h : G) ∈ K⁻¹ * K} < ⊤ := hc.measure_lt_top
  have hP : ρ (QuotientGroup.mk '' K : Set (G ⧸ H)) < ⊤ := by
    exact hρK _ (hK.image QuotientGroup.continuous_mk)
  have hpt : ∀ y : G ⧸ H, hAvg ν (K.indicator 1) y.out
      ≤ (QuotientGroup.mk '' K : Set (G ⧸ H)).indicator
          (fun _ => ν {h : H | (h : G) ∈ K⁻¹ * K}) y := by
    intro y
    have hmk : ∀ h : H, ((y.out * (h : G) : G) : G ⧸ H) = y := by
      intro h
      exact (QuotientGroup.mk_mul_of_mem _ h.2).trans (QuotientGroup.out_eq' y)
    by_cases hy : y ∈ (QuotientGroup.mk '' K : Set (G ⧸ H))
    · rw [Set.indicator_of_mem hy]
      exact hAvg_indicator_le ν K K 1 y.out (fun x hx => by simpa using hx)
    · have hz : ∀ h : H, K.indicator (1 : G → ℝ≥0∞) (y.out * (h : G)) = 0 := by
        intro h
        rw [Set.indicator_apply_eq_zero]
        intro hmem
        exact (hy ⟨_, hmem, hmk h⟩).elim
      have hfz : hAvg ν (K.indicator 1) y.out = 0 := by
        simp only [hAvg, hz, lintegral_zero]
      rw [hfz]
      exact zero_le
  calc qLift ν ρ K = ∫⁻ x, K.indicator 1 x ∂qLift ν ρ :=
        (lintegral_indicator_one hKm).symm
    _ = ∫⁻ y, hAvg ν (K.indicator 1) y.out ∂ρ := lintegral_qLift ν ρ hi
    _ ≤ ∫⁻ y, (QuotientGroup.mk '' K : Set (G ⧸ H)).indicator
          (fun _ => ν {h : H | (h : G) ∈ K⁻¹ * K}) y ∂ρ := lintegral_mono hpt
    _ ≤ ν {h : H | (h : G) ∈ K⁻¹ * K} * ρ (QuotientGroup.mk '' K : Set (G ⧸ H)) :=
        lintegral_indicator_const_le _ _
    _ < ⊤ := by
        exact ENNReal.mul_lt_top hM hP
end PI.QuotMeasUniqW
