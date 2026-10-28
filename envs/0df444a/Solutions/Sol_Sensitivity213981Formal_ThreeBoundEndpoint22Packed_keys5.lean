-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys5
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:35:47.544914+00:00
-- url     : https://prove2.me/submissions/7c53f32e-0195-455a-bdb1-36915aebd34a

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree005
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData005
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
theorem keys5_0 : subtree5_0.checkKeys=true := by decide +kernel
theorem keys5_1 : subtree5_1.checkKeys=true := by decide +kernel
theorem keys5_2 : subtree5_2.checkKeys=true := by decide +kernel
theorem keys5_3 : subtree5_3.checkKeys=true := by decide +kernel
theorem keys5_4 : subtree5_4.checkKeys=true := by decide +kernel
theorem keys5_5 : subtree5_5.checkKeys=true := by decide +kernel
theorem keys5_6 : subtree5_6.checkKeys=true := by decide +kernel
theorem keys5_7 : subtree5_7.checkKeys=true := by decide +kernel
theorem keys5 : subtree5.checkKeys=true := by
  simp only [subtree5,Tree.checkKeys,keys5_0,keys5_1,keys5_2,keys5_3,keys5_4,keys5_5,keys5_6,keys5_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree5)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys5
