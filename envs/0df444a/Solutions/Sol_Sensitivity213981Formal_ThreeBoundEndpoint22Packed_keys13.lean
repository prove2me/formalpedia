-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys13
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:36:15.103427+00:00
-- url     : https://prove2.me/submissions/384dc22f-bad3-40bf-a67f-b6f9bcc58f70

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree013
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData013
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
theorem keys13_0 : subtree13_0.checkKeys=true := by decide +kernel
theorem keys13_1 : subtree13_1.checkKeys=true := by decide +kernel
theorem keys13_2 : subtree13_2.checkKeys=true := by decide +kernel
theorem keys13_3 : subtree13_3.checkKeys=true := by decide +kernel
theorem keys13_4 : subtree13_4.checkKeys=true := by decide +kernel
theorem keys13_5 : subtree13_5.checkKeys=true := by decide +kernel
theorem keys13_6 : subtree13_6.checkKeys=true := by decide +kernel
theorem keys13_7 : subtree13_7.checkKeys=true := by decide +kernel
theorem keys13 : subtree13.checkKeys=true := by
  simp only [subtree13,Tree.checkKeys,keys13_0,keys13_1,keys13_2,keys13_3,keys13_4,keys13_5,keys13_6,keys13_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree13)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys13
