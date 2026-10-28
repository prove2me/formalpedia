-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys48
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:43:15.788058+00:00
-- url     : https://prove2.me/submissions/ebfd0792-c1d8-4f21-99b5-824af76f49af

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree048
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData048
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
theorem keys48_0 : subtree48_0.checkKeys=true := by decide +kernel
theorem keys48_1 : subtree48_1.checkKeys=true := by decide +kernel
theorem keys48_2 : subtree48_2.checkKeys=true := by decide +kernel
theorem keys48_3 : subtree48_3.checkKeys=true := by decide +kernel
theorem keys48_4 : subtree48_4.checkKeys=true := by decide +kernel
theorem keys48_5 : subtree48_5.checkKeys=true := by decide +kernel
theorem keys48_6 : subtree48_6.checkKeys=true := by decide +kernel
theorem keys48_7 : subtree48_7.checkKeys=true := by decide +kernel
theorem keys48 : subtree48.checkKeys=true := by
  simp only [subtree48,Tree.checkKeys,keys48_0,keys48_1,keys48_2,keys48_3,keys48_4,keys48_5,keys48_6,keys48_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree48)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys48
