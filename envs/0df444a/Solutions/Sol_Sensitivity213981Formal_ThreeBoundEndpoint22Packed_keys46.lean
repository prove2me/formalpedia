-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys46
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:42:46.436414+00:00
-- url     : https://prove2.me/submissions/89ad64ac-7bec-46d9-a599-c3e6e0d3d392

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree046
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData046
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
theorem keys46_0 : subtree46_0.checkKeys=true := by decide +kernel
theorem keys46_1 : subtree46_1.checkKeys=true := by decide +kernel
theorem keys46_2 : subtree46_2.checkKeys=true := by decide +kernel
theorem keys46_3 : subtree46_3.checkKeys=true := by decide +kernel
theorem keys46_4 : subtree46_4.checkKeys=true := by decide +kernel
theorem keys46_5 : subtree46_5.checkKeys=true := by decide +kernel
theorem keys46_6 : subtree46_6.checkKeys=true := by decide +kernel
theorem keys46_7 : subtree46_7.checkKeys=true := by decide +kernel
theorem keys46 : subtree46.checkKeys=true := by
  simp only [subtree46,Tree.checkKeys,keys46_0,keys46_1,keys46_2,keys46_3,keys46_4,keys46_5,keys46_6,keys46_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree46)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys46
