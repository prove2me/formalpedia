-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.diagonalRecoveryProjectionSum_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:38:02.445298+00:00
-- url     : https://prove2.me/submissions/687e25e2-2b63-4d84-a4b1-e55d526b372f

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryProjectionTerm_adjoint

set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
variable [DecidableEq ι]
omit [DecidableEq ι]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    (F : FiniteKrausFamily ι H H) (C : QuantumCode H) (lambda : ι → ℝ) :
    LinearMap.adjoint
        (∑ a : ι,
          (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
            (diagonalRecoveryOperator C F lambda a)) =
      ∑ a : ι,
        (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
          (diagonalRecoveryOperator C F lambda a) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  exact diagonalRecoveryProjectionTerm_adjoint F C lambda a
end QEC.Semantics.FiniteKrausFamily
