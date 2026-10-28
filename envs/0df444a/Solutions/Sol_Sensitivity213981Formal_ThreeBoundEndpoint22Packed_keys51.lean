-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys51
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:43:23.841228+00:00
-- url     : https://prove2.me/submissions/40726c4d-b481-48c7-8367-b380dfdba342

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree051
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData051
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
theorem keys51_0 : subtree51_0.checkKeys=true := by decide +kernel
theorem keys51_1 : subtree51_1.checkKeys=true := by decide +kernel
theorem keys51_2 : subtree51_2.checkKeys=true := by decide +kernel
theorem keys51_3 : subtree51_3.checkKeys=true := by decide +kernel
theorem keys51_4 : subtree51_4.checkKeys=true := by decide +kernel
theorem keys51_5 : subtree51_5.checkKeys=true := by decide +kernel
theorem keys51_6 : subtree51_6.checkKeys=true := by decide +kernel
theorem keys51_7 : subtree51_7.checkKeys=true := by decide +kernel
theorem keys51 : subtree51.checkKeys=true := by
  simp only [subtree51,Tree.checkKeys,keys51_0,keys51_1,keys51_2,keys51_3,keys51_4,keys51_5,keys51_6,keys51_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree51)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys51
