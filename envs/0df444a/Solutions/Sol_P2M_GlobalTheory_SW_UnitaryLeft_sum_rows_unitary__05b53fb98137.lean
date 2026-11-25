-- Prove2me | solution 1 for P2M_GlobalTheory_SW_UnitaryLeft_sum_rows_unitary__05b53fb98137
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:31:07.484007+00:00
-- url     : https://prove2.me/submissions/b99ccdf0-76a3-47ee-9b2e-5039a0cbe25b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroup
import Theorems.Thm_GlobalTheory_SW_UnitaryLeft_sum_rows_unitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.UnitaryLeft
noncomputable section
namespace GlobalTheory.SW.UnitaryLeft
theorem _root_.solution {n N : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (hPQ : Qᵀ * P = 1)
    (U V : Matrix (Fin n) (Fin N) ℂ) :
    ∑ k, (P * U) k ⬝ᵥ (Q * V) k = ∑ k, U k ⬝ᵥ V k := by
  simpa using sum_rows_unitary P Q hPQ U V 1
end GlobalTheory.SW.UnitaryLeft
