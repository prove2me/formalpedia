-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_det_restrictScalars_toLin__6aa316170093
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:30:19.659156+00:00
-- url     : https://prove2.me/submissions/ba93241c-5514-4948-9c7a-5323021ac4ec

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralLinearChangeVariablesComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
theorem _root_.solution {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det ((Matrix.toLin' D).restrictScalars ℝ) = Complex.normSq (Matrix.det D) := by
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
