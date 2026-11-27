-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SheetImageArea_proof_5087d368712c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:07:53.994886+00:00
-- url     : https://prove2.me/submissions/3b48b27e-7724-49a2-b9b7-7ed3911b7bbb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetImageArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetImageAreaSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjectionFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetImageArea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_measurable_sheetJac_05453086f16d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Matrix
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace SheetImageArea
theorem _root_.solution (h : SheetImageAreaSet.Statement) : SheetImageArea.Statement := by
  classical
  intro n d A U s hU hs hA B hB hBU g hg
  let U' : Set (EuclideanSpace ℂ (Fin d)) := WithLp.ofLp ⁻¹' U
  let T : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin n) := fun y => WithLp.toLp 2 (s (WithLp.ofLp y))
  let T' := U'.piecewise T (fun _ => 0)
  have hU' : IsOpen U' := hU.preimage (PiLp.continuous_ofLp 2 _)
  have hT : ContinuousOn T U' :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn
      (hs.continuousOn.comp (PiLp.continuous_ofLp 2 _).continuousOn fun _ hy => hy)
  have hT'm : Measurable T' := hT.measurable_piecewise continuousOn_const hU'.measurableSet
  have hEq : ∀ y ∈ B, T' y = T y := fun y hy => Set.piecewise_eq_of_mem _ _ _ (hBU y hy)
  have hJ : Measurable fun y : EuclideanSpace ℂ (Fin d) => ENNReal.ofReal (sheetJac s (WithLp.ofLp y)) :=
    ENNReal.measurable_ofReal.comp ((measurable_sheetJac s).comp (PiLp.continuous_ofLp 2 _).measurable)
  let ρ := (μH[((2 * d : ℕ) : ℝ)].restrict B).withDensity
    fun y : EuclideanSpace ℂ (Fin d) => ENNReal.ofReal (sheetJac s (WithLp.ofLp y))
  have hmap : ρ.map T' = (μH[((2 * d : ℕ) : ℝ)]).restrict (T '' B) := by
    ext S hS
    have hpre : MeasurableSet (T' ⁻¹' S) := hT'm hS
    rw [Measure.map_apply hT'm hS, withDensity_apply _ hpre, Measure.restrict_restrict hpre,
      Measure.restrict_apply hS,
      ← h n d A U s hU hs hA _ (hpre.inter hB) fun y hy => hBU y hy.2]
    congr 1
    ext z
    constructor
    · rintro ⟨y, ⟨hyS, hyB⟩, rfl⟩
      exact ⟨by simpa [Set.mem_preimage, hEq y hyB] using hyS, y, hyB, rfl⟩
    · rintro ⟨hzS, y, hyB, rfl⟩
      exact ⟨y, ⟨by simpa [Set.mem_preimage, hEq y hyB] using hzS, hyB⟩, rfl⟩
  calc ∫⁻ y in B, g (WithLp.toLp 2 (s (WithLp.ofLp y))) * ENNReal.ofReal (sheetJac s (WithLp.ofLp y))
          ∂(μH[((2 * d : ℕ) : ℝ)])
      = ∫⁻ y in B, ENNReal.ofReal (sheetJac s (WithLp.ofLp y)) * g (T' y) ∂(μH[((2 * d : ℕ) : ℝ)]) :=
        setLIntegral_congr_fun hB fun y hy => by rw [hEq y hy, mul_comm]
    _ = ∫⁻ y, g (T' y) ∂ρ := (lintegral_withDensity_eq_lintegral_mul _ hJ (hg.comp hT'm)).symm
    _ = ∫⁻ z, g z ∂(ρ.map T') := (lintegral_map hg hT'm).symm
    _ = _ := by rw [hmap]
end SheetImageArea
end GroundTheory.Heights₂.Heights
