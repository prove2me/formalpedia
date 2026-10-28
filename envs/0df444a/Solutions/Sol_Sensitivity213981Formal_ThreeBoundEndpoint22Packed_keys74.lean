-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys74
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:54:08.405469+00:00
-- url     : https://prove2.me/submissions/34b1ca28-6b98-45f2-bcee-efa19159e17f

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree074
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData074
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
theorem keys74_0 : subtree74_0.checkKeys=true := by decide +kernel
theorem keys74_1 : subtree74_1.checkKeys=true := by decide +kernel
theorem keys74_2 : subtree74_2.checkKeys=true := by decide +kernel
theorem keys74_3 : subtree74_3.checkKeys=true := by decide +kernel
theorem keys74_4 : subtree74_4.checkKeys=true := by decide +kernel
theorem keys74_5 : subtree74_5.checkKeys=true := by decide +kernel
theorem keys74_6 : subtree74_6.checkKeys=true := by decide +kernel
theorem keys74_7 : subtree74_7.checkKeys=true := by decide +kernel
theorem keys74 : subtree74.checkKeys=true := by
  simp only [subtree74,Tree.checkKeys,keys74_0,keys74_1,keys74_2,keys74_3,keys74_4,keys74_5,keys74_6,keys74_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree74)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys74
