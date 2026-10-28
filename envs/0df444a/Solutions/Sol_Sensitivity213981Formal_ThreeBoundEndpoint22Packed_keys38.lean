-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys38
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:39:59.914278+00:00
-- url     : https://prove2.me/submissions/1bf07363-858d-4015-b605-36bda5d8e456

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree038
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData038
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
theorem keys38_0 : subtree38_0.checkKeys=true := by decide +kernel
theorem keys38_1 : subtree38_1.checkKeys=true := by decide +kernel
theorem keys38_2 : subtree38_2.checkKeys=true := by decide +kernel
theorem keys38_3 : subtree38_3.checkKeys=true := by decide +kernel
theorem keys38_4 : subtree38_4.checkKeys=true := by decide +kernel
theorem keys38_5 : subtree38_5.checkKeys=true := by decide +kernel
theorem keys38_6 : subtree38_6.checkKeys=true := by decide +kernel
theorem keys38_7 : subtree38_7.checkKeys=true := by decide +kernel
theorem keys38 : subtree38.checkKeys=true := by
  simp only [subtree38,Tree.checkKeys,keys38_0,keys38_1,keys38_2,keys38_3,keys38_4,keys38_5,keys38_6,keys38_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree38)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys38
