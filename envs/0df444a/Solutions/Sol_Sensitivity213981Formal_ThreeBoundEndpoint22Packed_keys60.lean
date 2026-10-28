-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys60
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:44:20.25682+00:00
-- url     : https://prove2.me/submissions/0d22806b-7807-44c0-b8f4-902bddabec68

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree060
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData060
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
theorem keys60_0 : subtree60_0.checkKeys=true := by decide +kernel
theorem keys60_1 : subtree60_1.checkKeys=true := by decide +kernel
theorem keys60_2 : subtree60_2.checkKeys=true := by decide +kernel
theorem keys60_3 : subtree60_3.checkKeys=true := by decide +kernel
theorem keys60_4 : subtree60_4.checkKeys=true := by decide +kernel
theorem keys60_5 : subtree60_5.checkKeys=true := by decide +kernel
theorem keys60_6 : subtree60_6.checkKeys=true := by decide +kernel
theorem keys60_7 : subtree60_7.checkKeys=true := by decide +kernel
theorem keys60 : subtree60.checkKeys=true := by
  simp only [subtree60,Tree.checkKeys,keys60_0,keys60_1,keys60_2,keys60_3,keys60_4,keys60_5,keys60_6,keys60_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree60)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys60
