-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BinaryRowFamily.reducedRow_pair_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:16:16.052328+00:00
-- url     : https://prove2.me/submissions/2bf56c7e-d430-4e03-987a-fdb86ff3df4c

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_reducedRow_pairing_eq_zero_of_ne

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
    {r s : R.ReducedRowIndex} (hrs : r ≠ s) :
    Even (pairOverlap (R.reducedRow r) (R.reducedRow s)) := by
  rw [← ZMod.natCast_eq_zero_iff_even, pairOverlap_cast]
  exact R.reducedRow_pairing_eq_zero_of_ne hR hrs
end QEC.Distillation.Triorthogonal.BinaryRowFamily
