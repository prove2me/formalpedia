-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys85
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:31:21.854214+00:00
-- url     : https://prove2.me/submissions/c2afcaae-8568-4887-9e15-35eeb6491e63

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree085
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData085
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
theorem keys85_0 : subtree85_0.checkKeys=true := by decide +kernel
theorem keys85_1 : subtree85_1.checkKeys=true := by decide +kernel
theorem keys85_2 : subtree85_2.checkKeys=true := by decide +kernel
theorem keys85_3 : subtree85_3.checkKeys=true := by decide +kernel
theorem keys85_4 : subtree85_4.checkKeys=true := by decide +kernel
theorem keys85_5 : subtree85_5.checkKeys=true := by decide +kernel
theorem keys85_6 : subtree85_6.checkKeys=true := by decide +kernel
theorem keys85_7 : subtree85_7.checkKeys=true := by decide +kernel
theorem keys85 : subtree85.checkKeys=true := by
  simp only [subtree85,Tree.checkKeys,keys85_0,keys85_1,keys85_2,keys85_3,keys85_4,keys85_5,keys85_6,keys85_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree85)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys85
