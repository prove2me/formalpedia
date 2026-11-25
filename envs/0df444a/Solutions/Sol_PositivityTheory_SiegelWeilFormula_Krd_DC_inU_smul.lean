-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Krd.DC.inU_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:57:10.506348+00:00
-- url     : https://prove2.me/submissions/b57013f6-3392-4298-889d-760d98be51cc

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseCP
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Krd PositivityTheory.SiegelWeilFormula.Krd.DC
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PositivityTheory.SiegelWeilFormula.Krd.DC
theorem _root_.solution {J h : Matrix ι ι ℂ} (hh : InU J h) {μ : ℂ} (hμ : star μ * μ = 1) : InU J (μ • h) := by
  unfold InU at *
  simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hh]
  rw [mul_comm μ, hμ, one_smul]
end PositivityTheory.SiegelWeilFormula.Krd.DC
