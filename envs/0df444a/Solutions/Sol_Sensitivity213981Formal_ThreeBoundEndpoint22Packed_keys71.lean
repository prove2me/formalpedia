-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys71
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:54:06.72342+00:00
-- url     : https://prove2.me/submissions/47c54d77-0e2e-4fb5-88c6-9cbb08059f38

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree071
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData071
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
theorem keys71_0 : subtree71_0.checkKeys=true := by decide +kernel
theorem keys71_1 : subtree71_1.checkKeys=true := by decide +kernel
theorem keys71_2 : subtree71_2.checkKeys=true := by decide +kernel
theorem keys71_3 : subtree71_3.checkKeys=true := by decide +kernel
theorem keys71_4 : subtree71_4.checkKeys=true := by decide +kernel
theorem keys71_5 : subtree71_5.checkKeys=true := by decide +kernel
theorem keys71_6 : subtree71_6.checkKeys=true := by decide +kernel
theorem keys71_7 : subtree71_7.checkKeys=true := by decide +kernel
theorem keys71 : subtree71.checkKeys=true := by
  simp only [subtree71,Tree.checkKeys,keys71_0,keys71_1,keys71_2,keys71_3,keys71_4,keys71_5,keys71_6,keys71_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree71)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys71
