-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KMain.coordX_temperate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:57:28.038074+00:00
-- url     : https://prove2.me/submissions/24fc54cb-39f7-422c-a18e-bca13282f9b4

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSchwartzSums_SchwartzPolyGauss
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply



set_option autoImplicit false
noncomputable section
open scoped SchwartzMap
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KMain
open PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KMain
theorem _root_.solution {m n : ℕ} (k : Fin m × Fin n × Bool) : Function.HasTemperateGrowth (coordX k) := by
  rcases k with ⟨a, i, β⟩
  cases β
  · have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a)).hasTemperateGrowth
    convert h using 1
    funext x
    simp [coordX]
  · have h := ((Complex.conjCLE.toContinuousLinearMap).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a))).hasTemperateGrowth
    convert h using 1
    funext x
    simp [coordX]
end PositivityTheory.SiegelWeilFormula.KMain
