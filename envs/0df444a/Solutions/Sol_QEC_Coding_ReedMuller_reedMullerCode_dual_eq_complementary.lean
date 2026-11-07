-- Prove2me | solution 1 for QEC.Coding.ReedMuller.reedMullerCode_dual_eq_complementary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:59:45.504867+00:00
-- url     : https://prove2.me/submissions/a85bcfe2-97c7-4845-9359-f0a7e7e895e6

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_ReedMuller_Base
import Theorems.Thm_QEC_Coding_ReedMuller_reedMullerCode_dimension_eq_card_squarefree
import Theorems.Thm_QEC_Coding_ReedMuller_reedMullerCode_le_dual_of_add_lt
import Theorems.Thm_QEC_Coding_ReedMuller_card_booleanPoint
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LinearCode_dual_dimension_eq_length_sub_dimension
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


section
noncomputable section
namespace QEC
namespace Coding
namespace ReedMuller
open scoped BigOperators
private theorem squarefree_card_add_complementary {m r : Nat}
    (hrm : r < m) :
    Fintype.card (SquarefreeMonomial m r) +
      Fintype.card (SquarefreeMonomial m (m - r - 1)) =
        Fintype.card (BooleanPoint m) := by
  classical
  have hhigh :
      Fintype.card {support : Finset (Fin m) // ¬ support.card ≤ r} =
        Fintype.card (SquarefreeMonomial m (m - r - 1)) :=
    Fintype.card_congr (highSquarefreeComplementEquiv hrm)
  calc
    Fintype.card (SquarefreeMonomial m r) +
        Fintype.card (SquarefreeMonomial m (m - r - 1)) =
        Fintype.card {support : Finset (Fin m) // support.card ≤ r} +
          Fintype.card {support : Finset (Fin m) // ¬ support.card ≤ r} := by
            rw [hhigh]
    _ = Fintype.card {support : Finset (Fin m) // support.card ≤ r} +
          (Fintype.card (Finset (Fin m)) -
            Fintype.card {support : Finset (Fin m) // support.card ≤ r}) := by
          rw [Fintype.card_subtype_compl]
    _ = Fintype.card (Finset (Fin m)) := by
          exact Nat.add_sub_of_le (Fintype.card_subtype_le _)
    _ = Fintype.card (BooleanPoint m) := by
          rw [Fintype.card_finset, Fintype.card_fin, card_booleanPoint]
end ReedMuller
end Coding
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.ReedMuller
open scoped BigOperators
namespace QEC.Coding.ReedMuller
theorem _root_.solution {r m : Nat}
    (hrm : r < m) :
    (reedMullerCode (m - r - 1) m).dual.carrier =
      (reedMullerCode r m).carrier := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact reedMullerCode_le_dual_of_add_lt (r := m - r - 1) (s := r) (by omega)
  · change Dimension (reedMullerCode r m) =
      Dimension (reedMullerCode (m - r - 1) m).dual
    rw [LinearCode.dual_dimension_eq_length_sub_dimension]
    have hdimension :
        Dimension (reedMullerCode r m) +
          Dimension (reedMullerCode (m - r - 1) m) =
            Length (ZMod 2) (BooleanPoint m) := by
      rw [reedMullerCode_dimension_eq_card_squarefree,
        reedMullerCode_dimension_eq_card_squarefree]
      simpa [Length] using squarefree_card_add_complementary hrm
    omega
end QEC.Coding.ReedMuller
