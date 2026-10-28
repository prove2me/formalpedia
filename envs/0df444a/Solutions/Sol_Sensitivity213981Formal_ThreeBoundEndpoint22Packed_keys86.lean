-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys86
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:31:22.773034+00:00
-- url     : https://prove2.me/submissions/163f65ec-61f4-4bcf-8a41-68f1f7163dba

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree086
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData086
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
theorem keys86_0 : subtree86_0.checkKeys=true := by decide +kernel
theorem keys86_1 : subtree86_1.checkKeys=true := by decide +kernel
theorem keys86_2 : subtree86_2.checkKeys=true := by decide +kernel
theorem keys86_3 : subtree86_3.checkKeys=true := by decide +kernel
theorem keys86_4 : subtree86_4.checkKeys=true := by decide +kernel
theorem keys86_5 : subtree86_5.checkKeys=true := by decide +kernel
theorem keys86_6 : subtree86_6.checkKeys=true := by decide +kernel
theorem keys86_7 : subtree86_7.checkKeys=true := by decide +kernel
theorem keys86 : subtree86.checkKeys=true := by
  simp only [subtree86,Tree.checkKeys,keys86_0,keys86_1,keys86_2,keys86_3,keys86_4,keys86_5,keys86_6,keys86_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree86)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys86
