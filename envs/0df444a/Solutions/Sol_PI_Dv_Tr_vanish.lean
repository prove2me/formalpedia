-- Prove2me | solution 1 for PI.Dv.Tr.vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:36:07.670934+00:00
-- url     : https://prove2.me/submissions/b9d2610b-268a-4d71-9159-873c4b56c6c6

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
namespace PI.Dv.Tr
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V) (P0 : Pair K G) (x : V)
    (h : ∀ g, ρ.asAlgebraHom (eps P0) (ρ g x) = 0) (c : MonoidAlgebra K G) :
    ρ.asAlgebraHom (eps P0 * c) x = 0 := by
  induction c using MonoidAlgebra.induction_on with
  | of g => rw [map_mul, Module.End.mul_apply, Representation.asAlgebraHom_of, h g]
  | add a b ha hb => rw [mul_add, map_add, LinearMap.add_apply, ha, hb, add_zero]
  | smul r a ha => rw [mul_smul_comm, map_smul, LinearMap.smul_apply, ha, smul_zero]
end PI.Dv.Tr
