-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.fintype_sum_triple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:39:28.017209+00:00
-- url     : https://prove2.me/submissions/47979eef-7600-421e-9df0-409f74938dfd

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ListStructure

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution
    {A B C Value : Type*} [Fintype A] [Fintype B] [Fintype C]
    [AddCommMonoid Value] (value : A → B → C → Value) :
    (∑ entry : A × B × C, value entry.1 entry.2.1 entry.2.2) =
      ∑ first : A, ∑ second : B, ∑ third : C, value first second third := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro first _
  rw [Fintype.sum_prod_type]
end QEC.Coding.Why24AppendixANF
