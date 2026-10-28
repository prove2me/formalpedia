-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys12
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:36:41.644676+00:00
-- url     : https://prove2.me/submissions/f3f3180f-1f4c-46e6-818e-d35b8bc0b671

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree012
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData012
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
theorem keys12_0 : subtree12_0.checkKeys=true := by decide +kernel
theorem keys12_1 : subtree12_1.checkKeys=true := by decide +kernel
theorem keys12_2 : subtree12_2.checkKeys=true := by decide +kernel
theorem keys12_3 : subtree12_3.checkKeys=true := by decide +kernel
theorem keys12_4 : subtree12_4.checkKeys=true := by decide +kernel
theorem keys12_5 : subtree12_5.checkKeys=true := by decide +kernel
theorem keys12_6 : subtree12_6.checkKeys=true := by decide +kernel
theorem keys12_7 : subtree12_7.checkKeys=true := by decide +kernel
theorem keys12 : subtree12.checkKeys=true := by
  simp only [subtree12,Tree.checkKeys,keys12_0,keys12_1,keys12_2,keys12_3,keys12_4,keys12_5,keys12_6,keys12_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree12)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys12
