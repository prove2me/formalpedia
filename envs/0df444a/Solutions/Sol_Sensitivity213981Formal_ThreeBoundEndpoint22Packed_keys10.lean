-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys10
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:36:41.14503+00:00
-- url     : https://prove2.me/submissions/682522d3-6c91-4769-8608-f897c66ef6a8

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree010
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData010
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
theorem keys10_0 : subtree10_0.checkKeys=true := by decide +kernel
theorem keys10_1 : subtree10_1.checkKeys=true := by decide +kernel
theorem keys10_2 : subtree10_2.checkKeys=true := by decide +kernel
theorem keys10_3 : subtree10_3.checkKeys=true := by decide +kernel
theorem keys10_4 : subtree10_4.checkKeys=true := by decide +kernel
theorem keys10_5 : subtree10_5.checkKeys=true := by decide +kernel
theorem keys10_6 : subtree10_6.checkKeys=true := by decide +kernel
theorem keys10_7 : subtree10_7.checkKeys=true := by decide +kernel
theorem keys10 : subtree10.checkKeys=true := by
  simp only [subtree10,Tree.checkKeys,keys10_0,keys10_1,keys10_2,keys10_3,keys10_4,keys10_5,keys10_6,keys10_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree10)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys10
