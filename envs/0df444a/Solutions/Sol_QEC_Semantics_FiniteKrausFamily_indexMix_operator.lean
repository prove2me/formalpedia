-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.indexMix_operator
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:57:58.670995+00:00
-- url     : https://prove2.me/submissions/ea4740dc-4990-4549-8a9d-28a4867c00f4

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
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

theorem solution (E : FiniteKrausFamily ι H H)
    (U : Matrix ι ι Complex) (a : ι) :
    (E.indexMix U).operator a = ∑ i : ι, U i a • E.operator i := by
  solve | rfl | simp [indexMix] | simp_all [indexMix] | omega | norm_num
