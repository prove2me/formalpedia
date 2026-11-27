-- Prove2me | solution 1 for P2M_GlobalTheory_FockRep_detPlus_eq_det_toBlocks___f9bcbd0bab63
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:58:50.85312+00:00
-- url     : https://prove2.me/submissions/cea8ea29-2e47-40a1-87d8-75d214f5f4a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfOrthogonalTranslatesProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryOsc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix MeasureTheory Complex GlobalTheory.RealWeil GlobalTheory.RealWeil.UnitaryOsc
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.FockRep
namespace GlobalTheory.FockRep
theorem _root_.solution {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (g : Matrix (m ⊕ n) (m ⊕ n) ℂ) :
    dP (fromBlocks 1 0 0 (-1)) g = g.toBlocks₁₁.det := by
  have : (1 / 2 : ℂ) • ((1 + (fromBlocks 1 0 0 (-1) : Matrix (m ⊕ n) (m ⊕ n) ℂ)) * g) +
      (1 / 2 : ℂ) • (1 - (fromBlocks 1 0 0 (-1) : Matrix (m ⊕ n) (m ⊕ n) ℂ)) =
      fromBlocks g.toBlocks₁₁ g.toBlocks₁₂ 0 1 := by
    conv_lhs => rw [← fromBlocks_toBlocks g, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add,
      fromBlocks_add, fromBlocks_multiply, fromBlocks_smul, fromBlocks_smul, fromBlocks_add]
    congr 1
    · rw [add_zero, Matrix.zero_mul, add_zero, add_mul, one_mul]; module
    · rw [add_zero, Matrix.zero_mul, add_zero, Matrix.add_mul, Matrix.one_mul]; module
    · simp
    · simp only [add_zero, Matrix.zero_mul, add_neg_cancel, neg_neg, smul_zero, zero_add]; module
  rw [dP, this, det_fromBlocks_zero₂₁, det_one, mul_one]
end GlobalTheory.FockRep
