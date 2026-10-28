-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys75
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:54:08.964152+00:00
-- url     : https://prove2.me/submissions/c5b43a21-858a-4e67-8f15-d221608829f1

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree075
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData075
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
theorem keys75_0 : subtree75_0.checkKeys=true := by decide +kernel
theorem keys75_1 : subtree75_1.checkKeys=true := by decide +kernel
theorem keys75_2 : subtree75_2.checkKeys=true := by decide +kernel
theorem keys75_3 : subtree75_3.checkKeys=true := by decide +kernel
theorem keys75_4 : subtree75_4.checkKeys=true := by decide +kernel
theorem keys75_5 : subtree75_5.checkKeys=true := by decide +kernel
theorem keys75_6 : subtree75_6.checkKeys=true := by decide +kernel
theorem keys75_7 : subtree75_7.checkKeys=true := by decide +kernel
theorem keys75 : subtree75.checkKeys=true := by
  simp only [subtree75,Tree.checkKeys,keys75_0,keys75_1,keys75_2,keys75_3,keys75_4,keys75_5,keys75_6,keys75_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree75)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys75
