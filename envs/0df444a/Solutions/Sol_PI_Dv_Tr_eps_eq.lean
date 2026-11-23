-- Prove2me | solution 1 for PI.Dv.Tr.eps_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:52.038961+00:00
-- url     : https://prove2.me/submissions/caac5d9b-41f5-4df2-9b78-8aaf2fb58ed0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_KudlaSiegelWeil
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility

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
open PI.Dv Module
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
open Classical
namespace PI.Dv.Tr
theorem _root_.solution (P : Pair K G) : eps P = ((Fintype.card P.H : ℕ) : K)⁻¹ • epsSum P := by
  rw [eps, epsSum, Nat.card_eq_fintype_card]
  congr 1
  symm
  refine Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _ ?_ ?_
  · intro x hx
    rw [dif_neg]
    intro hm
    exact hx ⟨⟨x, hm⟩, rfl⟩
  · intro h
    rw [dif_pos h.2]
end PI.Dv.Tr
