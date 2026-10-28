-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys9
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:36:14.092206+00:00
-- url     : https://prove2.me/submissions/e20dd415-dc30-4938-8160-db051bf8f540

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree009
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData009
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
theorem keys9_0 : subtree9_0.checkKeys=true := by decide +kernel
theorem keys9_1 : subtree9_1.checkKeys=true := by decide +kernel
theorem keys9_2 : subtree9_2.checkKeys=true := by decide +kernel
theorem keys9_3 : subtree9_3.checkKeys=true := by decide +kernel
theorem keys9_4 : subtree9_4.checkKeys=true := by decide +kernel
theorem keys9_5 : subtree9_5.checkKeys=true := by decide +kernel
theorem keys9_6 : subtree9_6.checkKeys=true := by decide +kernel
theorem keys9_7 : subtree9_7.checkKeys=true := by decide +kernel
theorem keys9 : subtree9.checkKeys=true := by
  simp only [subtree9,Tree.checkKeys,keys9_0,keys9_1,keys9_2,keys9_3,keys9_4,keys9_5,keys9_6,keys9_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree9)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys9
