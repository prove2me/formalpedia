-- Prove2me | solution 1 for P2M_GlobalTheory_RealWeil_UnitaryOsc_detPlus_conj__6463fe3cfaa2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:02.641818+00:00
-- url     : https://prove2.me/submissions/f25bb848-0a2c-462d-843b-3b64a0b224c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairingsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CartanInvolutionConjOfPosDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThreeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianCongrInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProjEqSelfOfAnnihilated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.UnitaryOsc
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.RealWeil.UnitaryOsc
theorem _root_.solution {a s s' g g' : Matrix ι ι ℂ} (ha : a.det ≠ 0) (hs : a * s = s' * a) (hg : a * g = g' * a) :
    dP s g = dP s' g' := by
  have e : a * ((1 / 2 : ℂ) • ((1 + s) * g) + (1 / 2 : ℂ) • (1 - s)) =
      ((1 / 2 : ℂ) • ((1 + s') * g') + (1 / 2 : ℂ) • (1 - s')) * a := by
    have e1 : a * (s * g) = s' * g' * a := by rw [← mul_assoc, hs, mul_assoc, hg, mul_assoc]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, one_mul, mul_one, hs, hg, e1]
  have := congrArg Matrix.det e
  rw [det_mul, det_mul, mul_comm] at this
  exact mul_right_cancel₀ ha this
end GlobalTheory.RealWeil.UnitaryOsc
