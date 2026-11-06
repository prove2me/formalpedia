-- Prove2me | solution 1 for QEC.Semantics.exists_finiteKrausFamily_of_choiMatrix_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:41:54.170831+00:00
-- url     : https://prove2.me/submissions/da36cce8-6d46-4c1b-a70c-c1e697e07ed3

import Definitions.Def_QEC_Semantics_Channels_Choi
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Theorems.Thm_QEC_Semantics_choiMatrix_finiteKrausFamilyOfChoiVectors_inducedMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_choiMatrix_ext
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics
theorem _root_.solution {n : Nat} {betaK : Type*}
    [Fintype betaK]
    (Φ : Operator H →ₗ[Complex] Operator K)
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (hchoi : (choiMatrix Φ bH bK).PosSemidef) :
    ∃ (m : Nat), ∃ R : FiniteKrausFamily (Fin m) H K,
      R.inducedMap = Φ := by
  classical
  rcases (Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hchoi) with ⟨m, v, hv⟩
  let R : FiniteKrausFamily (Fin m) H K := finiteKrausFamilyOfChoiVectors bH bK v
  refine ⟨m, R, ?_⟩
  exact choiMatrix_ext R.inducedMap Φ bH bK (by
    calc
      choiMatrix R.inducedMap bH bK
          = ∑ a : Fin m, Matrix.vecMulVec (v a) (star (v a)) := by
            simpa [R] using choiMatrix_finiteKrausFamilyOfChoiVectors_inducedMap bH bK v
      _ = choiMatrix Φ bH bK := hv.symm)
end QEC.Semantics
