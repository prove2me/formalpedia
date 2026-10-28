-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys76
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:54:09.491006+00:00
-- url     : https://prove2.me/submissions/dfcf4032-9a44-477c-9b9b-fd51f9a5931f

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree076
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData076
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
theorem keys76_0 : subtree76_0.checkKeys=true := by decide +kernel
theorem keys76_1 : subtree76_1.checkKeys=true := by decide +kernel
theorem keys76_2 : subtree76_2.checkKeys=true := by decide +kernel
theorem keys76_3 : subtree76_3.checkKeys=true := by decide +kernel
theorem keys76_4 : subtree76_4.checkKeys=true := by decide +kernel
theorem keys76_5 : subtree76_5.checkKeys=true := by decide +kernel
theorem keys76_6 : subtree76_6.checkKeys=true := by decide +kernel
theorem keys76_7 : subtree76_7.checkKeys=true := by decide +kernel
theorem keys76 : subtree76.checkKeys=true := by
  simp only [subtree76,Tree.checkKeys,keys76_0,keys76_1,keys76_2,keys76_3,keys76_4,keys76_5,keys76_6,keys76_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree76)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys76
