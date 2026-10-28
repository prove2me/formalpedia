-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys33
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:38:11.326365+00:00
-- url     : https://prove2.me/submissions/90a6008d-64c7-4c9d-af3b-221e59ad49b5

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree033
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData033
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
theorem keys33_0 : subtree33_0.checkKeys=true := by decide +kernel
theorem keys33_1 : subtree33_1.checkKeys=true := by decide +kernel
theorem keys33_2 : subtree33_2.checkKeys=true := by decide +kernel
theorem keys33_3 : subtree33_3.checkKeys=true := by decide +kernel
theorem keys33_4 : subtree33_4.checkKeys=true := by decide +kernel
theorem keys33_5 : subtree33_5.checkKeys=true := by decide +kernel
theorem keys33_6 : subtree33_6.checkKeys=true := by decide +kernel
theorem keys33_7 : subtree33_7.checkKeys=true := by decide +kernel
theorem keys33 : subtree33.checkKeys=true := by
  simp only [subtree33,Tree.checkKeys,keys33_0,keys33_1,keys33_2,keys33_3,keys33_4,keys33_5,keys33_6,keys33_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree33)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys33
