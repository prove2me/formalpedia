-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys92
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:31:26.902234+00:00
-- url     : https://prove2.me/submissions/6c89cd17-9b61-4e9e-8bef-5dc6047e8cc4

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree092
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData092
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
theorem keys92_0 : subtree92_0.checkKeys=true := by decide +kernel
theorem keys92_1 : subtree92_1.checkKeys=true := by decide +kernel
theorem keys92_2 : subtree92_2.checkKeys=true := by decide +kernel
theorem keys92_3 : subtree92_3.checkKeys=true := by decide +kernel
theorem keys92_4 : subtree92_4.checkKeys=true := by decide +kernel
theorem keys92_5 : subtree92_5.checkKeys=true := by decide +kernel
theorem keys92_6 : subtree92_6.checkKeys=true := by decide +kernel
theorem keys92_7 : subtree92_7.checkKeys=true := by decide +kernel
theorem keys92 : subtree92.checkKeys=true := by
  simp only [subtree92,Tree.checkKeys,keys92_0,keys92_1,keys92_2,keys92_3,keys92_4,keys92_5,keys92_6,keys92_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree92)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys92
