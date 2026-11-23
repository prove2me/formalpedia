-- Prove2me | solution 1 for PI.Dv.Tr.phi_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:12.461034+00:00
-- url     : https://prove2.me/submissions/8e890a4f-c73e-4cd8-8290-921c112d5277

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module NumberField
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
open Classical
namespace PI.Dv.Tr
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V) (P0 : Pair K G) (g : G)
    (y : V) :
    ρ.asAlgebraHom (epsSum P0 * MonoidAlgebra.of K G g) y =
      ∑ h : P0.H, (((P0.chi h)⁻¹ : Kˣ) : K) • ρ (h : G) (ρ g y) := by
  rw [map_mul, Representation.asAlgebraHom_of, Module.End.mul_apply, epsSum, map_sum, LinearMap.sum_apply]
  simp only [map_smul, Representation.asAlgebraHom_of, LinearMap.smul_apply]
end PI.Dv.Tr
