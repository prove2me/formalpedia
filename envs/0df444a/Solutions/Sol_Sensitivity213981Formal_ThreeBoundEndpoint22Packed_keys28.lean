-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys28
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:37:30.592095+00:00
-- url     : https://prove2.me/submissions/c547c87a-09c6-4a94-b35c-059afad4c9b9

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree028
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData028
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
theorem keys28_0 : subtree28_0.checkKeys=true := by decide +kernel
theorem keys28_1 : subtree28_1.checkKeys=true := by decide +kernel
theorem keys28_2 : subtree28_2.checkKeys=true := by decide +kernel
theorem keys28_3 : subtree28_3.checkKeys=true := by decide +kernel
theorem keys28_4 : subtree28_4.checkKeys=true := by decide +kernel
theorem keys28_5 : subtree28_5.checkKeys=true := by decide +kernel
theorem keys28_6 : subtree28_6.checkKeys=true := by decide +kernel
theorem keys28_7 : subtree28_7.checkKeys=true := by decide +kernel
theorem keys28 : subtree28.checkKeys=true := by
  simp only [subtree28,Tree.checkKeys,keys28_0,keys28_1,keys28_2,keys28_3,keys28_4,keys28_5,keys28_6,keys28_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree28)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys28
