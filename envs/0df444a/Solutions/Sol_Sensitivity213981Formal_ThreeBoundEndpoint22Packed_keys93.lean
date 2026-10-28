-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys93
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:31:27.488156+00:00
-- url     : https://prove2.me/submissions/7efd4cf6-cdfd-4494-9fb2-cbd99653bf07

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree093
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData093
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
theorem keys93_0 : subtree93_0.checkKeys=true := by decide +kernel
theorem keys93_1 : subtree93_1.checkKeys=true := by decide +kernel
theorem keys93_2 : subtree93_2.checkKeys=true := by decide +kernel
theorem keys93_3 : subtree93_3.checkKeys=true := by decide +kernel
theorem keys93_4 : subtree93_4.checkKeys=true := by decide +kernel
theorem keys93_5 : subtree93_5.checkKeys=true := by decide +kernel
theorem keys93_6 : subtree93_6.checkKeys=true := by decide +kernel
theorem keys93_7 : subtree93_7.checkKeys=true := by decide +kernel
theorem keys93 : subtree93.checkKeys=true := by
  simp only [subtree93,Tree.checkKeys,keys93_0,keys93_1,keys93_2,keys93_3,keys93_4,keys93_5,keys93_6,keys93_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree93)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys93
