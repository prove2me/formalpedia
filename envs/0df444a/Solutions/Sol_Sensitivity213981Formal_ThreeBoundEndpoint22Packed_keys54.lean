-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys54
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:44:02.620646+00:00
-- url     : https://prove2.me/submissions/e38580a5-f156-43ed-827f-fd955f568679

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree054
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData054
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
theorem keys54_0 : subtree54_0.checkKeys=true := by decide +kernel
theorem keys54_1 : subtree54_1.checkKeys=true := by decide +kernel
theorem keys54_2 : subtree54_2.checkKeys=true := by decide +kernel
theorem keys54_3 : subtree54_3.checkKeys=true := by decide +kernel
theorem keys54_4 : subtree54_4.checkKeys=true := by decide +kernel
theorem keys54_5 : subtree54_5.checkKeys=true := by decide +kernel
theorem keys54_6 : subtree54_6.checkKeys=true := by decide +kernel
theorem keys54_7 : subtree54_7.checkKeys=true := by decide +kernel
theorem keys54 : subtree54.checkKeys=true := by
  simp only [subtree54,Tree.checkKeys,keys54_0,keys54_1,keys54_2,keys54_3,keys54_4,keys54_5,keys54_6,keys54_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree54)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys54
