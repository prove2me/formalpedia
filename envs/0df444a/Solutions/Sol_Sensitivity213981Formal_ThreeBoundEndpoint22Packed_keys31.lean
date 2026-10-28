-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys31
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:37:22.7026+00:00
-- url     : https://prove2.me/submissions/132ff5b3-5ece-41b3-b7bb-4d3d371e6618

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree031
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData031
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
theorem keys31_0 : subtree31_0.checkKeys=true := by decide +kernel
theorem keys31_1 : subtree31_1.checkKeys=true := by decide +kernel
theorem keys31_2 : subtree31_2.checkKeys=true := by decide +kernel
theorem keys31_3 : subtree31_3.checkKeys=true := by decide +kernel
theorem keys31_4 : subtree31_4.checkKeys=true := by decide +kernel
theorem keys31_5 : subtree31_5.checkKeys=true := by decide +kernel
theorem keys31_6 : subtree31_6.checkKeys=true := by decide +kernel
theorem keys31_7 : subtree31_7.checkKeys=true := by decide +kernel
theorem keys31 : subtree31.checkKeys=true := by
  simp only [subtree31,Tree.checkKeys,keys31_0,keys31_1,keys31_2,keys31_3,keys31_4,keys31_5,keys31_6,keys31_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree31)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys31
