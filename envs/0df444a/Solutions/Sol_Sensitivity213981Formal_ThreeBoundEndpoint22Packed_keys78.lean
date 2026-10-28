-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys78
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:54:10.653998+00:00
-- url     : https://prove2.me/submissions/790501df-bbcf-4051-a755-46ca88905d8e

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree078
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData078
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
theorem keys78_0 : subtree78_0.checkKeys=true := by decide +kernel
theorem keys78_1 : subtree78_1.checkKeys=true := by decide +kernel
theorem keys78_2 : subtree78_2.checkKeys=true := by decide +kernel
theorem keys78_3 : subtree78_3.checkKeys=true := by decide +kernel
theorem keys78_4 : subtree78_4.checkKeys=true := by decide +kernel
theorem keys78_5 : subtree78_5.checkKeys=true := by decide +kernel
theorem keys78_6 : subtree78_6.checkKeys=true := by decide +kernel
theorem keys78_7 : subtree78_7.checkKeys=true := by decide +kernel
theorem keys78 : subtree78.checkKeys=true := by
  simp only [subtree78,Tree.checkKeys,keys78_0,keys78_1,keys78_2,keys78_3,keys78_4,keys78_5,keys78_6,keys78_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree78)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys78
