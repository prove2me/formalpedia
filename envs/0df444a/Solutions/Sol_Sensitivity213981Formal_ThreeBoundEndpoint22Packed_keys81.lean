-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys81
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:31:19.742697+00:00
-- url     : https://prove2.me/submissions/319d4bd7-d594-4d6e-bec3-840c4134e80b

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree081
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData081
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
theorem keys81_0 : subtree81_0.checkKeys=true := by decide +kernel
theorem keys81_1 : subtree81_1.checkKeys=true := by decide +kernel
theorem keys81_2 : subtree81_2.checkKeys=true := by decide +kernel
theorem keys81_3 : subtree81_3.checkKeys=true := by decide +kernel
theorem keys81_4 : subtree81_4.checkKeys=true := by decide +kernel
theorem keys81_5 : subtree81_5.checkKeys=true := by decide +kernel
theorem keys81_6 : subtree81_6.checkKeys=true := by decide +kernel
theorem keys81_7 : subtree81_7.checkKeys=true := by decide +kernel
theorem keys81 : subtree81.checkKeys=true := by
  simp only [subtree81,Tree.checkKeys,keys81_0,keys81_1,keys81_2,keys81_3,keys81_4,keys81_5,keys81_6,keys81_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree81)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys81
