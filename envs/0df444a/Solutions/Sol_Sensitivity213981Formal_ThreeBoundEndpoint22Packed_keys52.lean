-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys52
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:43:37.283194+00:00
-- url     : https://prove2.me/submissions/3c5b9cdb-77e5-48be-804d-33ad483aaa72

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree052
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData052
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
theorem keys52_0 : subtree52_0.checkKeys=true := by decide +kernel
theorem keys52_1 : subtree52_1.checkKeys=true := by decide +kernel
theorem keys52_2 : subtree52_2.checkKeys=true := by decide +kernel
theorem keys52_3 : subtree52_3.checkKeys=true := by decide +kernel
theorem keys52_4 : subtree52_4.checkKeys=true := by decide +kernel
theorem keys52_5 : subtree52_5.checkKeys=true := by decide +kernel
theorem keys52_6 : subtree52_6.checkKeys=true := by decide +kernel
theorem keys52_7 : subtree52_7.checkKeys=true := by decide +kernel
theorem keys52 : subtree52.checkKeys=true := by
  simp only [subtree52,Tree.checkKeys,keys52_0,keys52_1,keys52_2,keys52_3,keys52_4,keys52_5,keys52_6,keys52_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree52)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys52
