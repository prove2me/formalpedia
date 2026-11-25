-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KMain.evX_temperate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:39.393262+00:00
-- url     : https://prove2.me/submissions/9181a685-6aa9-4400-ac76-37dfa91a2a94

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSchwartzSums_SchwartzPolyGauss
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KMain_coordX_temperate
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
theorem _root_.solution {m n : ℕ} (P : PX m n) : Function.HasTemperateGrowth (fun x => evX P x) := by
  have hev : (fun x => evX P x) = fun x => MvPolynomial.eval (fun k => coordX k x) P := by
    funext x
    rfl
  rw [hev]
  induction P using MvPolynomial.induction_on with
  | C c0 =>
    simp only [MvPolynomial.eval_C]
    exact Function.HasTemperateGrowth.const c0
  | add p q hp hq =>
    simp only [map_add]
    exact Function.HasTemperateGrowth.add (hp rfl) (hq rfl)
  | mul_X p k hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact Function.HasTemperateGrowth.mul (hp rfl) (coordX_temperate k)
end PositivityTheory.SiegelWeilFormula.KMain
