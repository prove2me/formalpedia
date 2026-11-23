-- Prove2me | solution 1 for PI.Dv.Tr.chi_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:06.475133+00:00
-- url     : https://prove2.me/submissions/a6a7136d-e5b5-415b-a1af-02bba237f3ac

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module NumberField
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
open Classical
namespace PI.Dv.Tr
theorem _root_.solution (P : Pair K G) (h : P.H) : ((((P.chi h)⁻¹ : Kˣ) : K)) ^ Fintype.card P.H = 1 := by
  rw [← Units.val_pow_eq_pow_val, ← map_inv, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
end PI.Dv.Tr
