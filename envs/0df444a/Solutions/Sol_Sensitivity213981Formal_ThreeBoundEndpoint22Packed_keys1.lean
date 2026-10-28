-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys1
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:35:29.308374+00:00
-- url     : https://prove2.me/submissions/bf980f30-6237-409d-a313-4d68941fa4b4

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree001
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData001
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedPackedTreeMatch
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith


namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
namespace ThreeBoundEndpoint22Packed
open ThreeBoundRelaxedPacked
theorem keys1_0 : subtree1_0.checkKeys=true := by decide +kernel
theorem keys1_1 : subtree1_1.checkKeys=true := by decide +kernel
theorem keys1_2 : subtree1_2.checkKeys=true := by decide +kernel
theorem keys1_3 : subtree1_3.checkKeys=true := by decide +kernel
theorem keys1_4 : subtree1_4.checkKeys=true := by decide +kernel
theorem keys1_5 : subtree1_5.checkKeys=true := by decide +kernel
theorem keys1_6 : subtree1_6.checkKeys=true := by decide +kernel
theorem keys1_7 : subtree1_7.checkKeys=true := by decide +kernel
theorem keys1 : subtree1.checkKeys=true := by
  simp only [subtree1,Tree.checkKeys,keys1_0,keys1_1,keys1_2,keys1_3,keys1_4,keys1_5,keys1_6,keys1_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree1)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys1
