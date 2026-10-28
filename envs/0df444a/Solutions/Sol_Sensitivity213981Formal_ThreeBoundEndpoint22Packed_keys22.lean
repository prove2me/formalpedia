-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys22
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:36:58.646745+00:00
-- url     : https://prove2.me/submissions/c50ec284-3d7a-4d9e-a8ba-c117977ed1ce

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree022
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData022
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
theorem keys22_0 : subtree22_0.checkKeys=true := by decide +kernel
theorem keys22_1 : subtree22_1.checkKeys=true := by decide +kernel
theorem keys22_2 : subtree22_2.checkKeys=true := by decide +kernel
theorem keys22_3 : subtree22_3.checkKeys=true := by decide +kernel
theorem keys22_4 : subtree22_4.checkKeys=true := by decide +kernel
theorem keys22_5 : subtree22_5.checkKeys=true := by decide +kernel
theorem keys22_6 : subtree22_6.checkKeys=true := by decide +kernel
theorem keys22_7 : subtree22_7.checkKeys=true := by decide +kernel
theorem keys22 : subtree22.checkKeys=true := by
  simp only [subtree22,Tree.checkKeys,keys22_0,keys22_1,keys22_2,keys22_3,keys22_4,keys22_5,keys22_6,keys22_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree22)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys22
