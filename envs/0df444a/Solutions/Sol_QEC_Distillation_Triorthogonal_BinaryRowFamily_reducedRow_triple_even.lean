-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.reducedRow_triple_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:20:29.027848+00:00
-- url     : https://prove2.me/submissions/25a154cf-67d7-41de-b008-f3608cc0cd62

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_reducedRow_triplePairing_eq_zero
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_tripleOverlap_cast


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]
universe uO uE uC
open QEC.Distillation.Triorthogonal.BinaryRowFamily
variable {OddRow : Type uO} {EvenRow : Type uE} {Col : Type uC}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
namespace QEC.Distillation.Triorthogonal.BinaryRowFamily
theorem _root_.solution
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {r s t : Sum OddRow R.EvenBasisIndex}
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    Even (tripleOverlap (R.reducedRow r) (R.reducedRow s) (R.reducedRow t)) := by
  rw [← ZMod.natCast_eq_zero_iff_even, tripleOverlap_cast]
  exact reducedRow_triplePairing_eq_zero R hR hrs hrt hst
end QEC.Distillation.Triorthogonal.BinaryRowFamily
