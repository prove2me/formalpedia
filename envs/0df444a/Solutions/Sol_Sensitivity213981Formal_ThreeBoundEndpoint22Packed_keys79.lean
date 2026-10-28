-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys79
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:54:11.183472+00:00
-- url     : https://prove2.me/submissions/341bd0ce-16dc-47ed-ac9d-982c74e2b266

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree079
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData079
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
theorem keys79_0 : subtree79_0.checkKeys=true := by decide +kernel
theorem keys79_1 : subtree79_1.checkKeys=true := by decide +kernel
theorem keys79_2 : subtree79_2.checkKeys=true := by decide +kernel
theorem keys79_3 : subtree79_3.checkKeys=true := by decide +kernel
theorem keys79_4 : subtree79_4.checkKeys=true := by decide +kernel
theorem keys79_5 : subtree79_5.checkKeys=true := by decide +kernel
theorem keys79_6 : subtree79_6.checkKeys=true := by decide +kernel
theorem keys79_7 : subtree79_7.checkKeys=true := by decide +kernel
theorem keys79 : subtree79.checkKeys=true := by
  simp only [subtree79,Tree.checkKeys,keys79_0,keys79_1,keys79_2,keys79_3,keys79_4,keys79_5,keys79_6,keys79_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree79)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys79
