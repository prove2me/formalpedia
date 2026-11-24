-- Prove2me | solution 1 for P2M_GlobalTheory_SW_Parab_qm_mul__cae64bfa856c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:45.796806+00:00
-- url     : https://prove2.me/submissions/a64583cb-de43-4d88-8283-58472da33135

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Parab
open Matrix Complex
open scoped ComplexConjugate Real
namespace GlobalTheory.SW.Parab
namespace _root_.GlobalTheory.SW.Parab
theorem _root_.solution {α β γ : Type} [Fintype β] (A : Matrix α β ℚ) (B : Matrix β γ ℚ) :
    _root_.GlobalTheory.SW.qm (A * B) = _root_.GlobalTheory.SW.qm A * _root_.GlobalTheory.SW.qm B := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm, mul_apply]
end _root_.GlobalTheory.SW.Parab
end GlobalTheory.SW.Parab
