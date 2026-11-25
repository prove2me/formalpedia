-- Prove2me | solution 1 for PI.ProdFormulaE.HaarAlgP.haarAlg_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:10.992805+00:00
-- url     : https://prove2.me/submissions/5bf04602-cf9a-4e9d-a218-fac418323795

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarMain
import Theorems.Thm_PI_ProdFormulaE_HaarBox_image_toLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure ValuativeRel Topology Module
open scoped NNReal ENNReal Pointwise
open PI PI.ProdFormulaE PI.ProdFormulaE.HaarAlgP
open HaarBox
namespace PI.ProdFormulaE.HaarAlgP
theorem _root_.solution
    (hscale : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K] (E : Type) [AddCommGroup E] [Module K E] [TopologicalSpace E]
      [IsModuleTopology K E] [MeasurableSpace E] [BorelSpace E] (n : ℕ) (b : Basis (Fin n) K E)
      (μ : Measure E) [μ.IsAddHaarMeasure], ScaleBox b μ)
    (htrans : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K] (E : Type) [AddCommGroup E] [Module K E] [TopologicalSpace E]
      [IsModuleTopology K E] (n : ℕ) (b : Basis (Fin n) K E), TransvBox b) :
    St.HaarAlg := by
  intro K _ _ _ _ A _ _ _ _ _ _ _ _ μ _ y hy S
  classical
  let b := Module.finBasis K A
  set M := LinearMap.toMatrix b b (LinearMap.mulLeft K y) with hM
  have hdet : M.det = Algebra.norm K y := by
    rw [hM, LinearMap.det_toMatrix, Algebra.norm_apply]
    rfl
  have hdet0 : M.det ≠ 0 := by
    rw [hdet]
    exact (hy.map (Algebra.norm K)).ne_zero
  have h := image_toLin b μ (hscale K A _ b μ) (htrans K A _ b) M hdet0 S
  rw [hdet, hM, Matrix.toLin_toMatrix] at h
  exact h
end PI.ProdFormulaE.HaarAlgP
