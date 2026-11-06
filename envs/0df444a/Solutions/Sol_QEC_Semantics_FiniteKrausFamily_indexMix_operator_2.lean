-- Prove2me | solution 2 for QEC.Semantics.FiniteKrausFamily.indexMix_operator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:44:28.490147+00:00
-- url     : https://prove2.me/submissions/c403581e-177b-4dbf-8865-c272c0eb1dce

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
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution (E : FiniteKrausFamily ι H H)
    (U : Matrix ι ι Complex) (a : ι) :
    (E.indexMix U).operator a = ∑ i : ι, U i a • E.operator i :=
  rfl
end QEC.Semantics.FiniteKrausFamily
