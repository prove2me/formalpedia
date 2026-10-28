-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys94
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:31:28.026539+00:00
-- url     : https://prove2.me/submissions/cf4a905c-8acd-4af1-9055-4ef808501373

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree094
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData094
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
theorem keys94_0 : subtree94_0.checkKeys=true := by decide +kernel
theorem keys94_1 : subtree94_1.checkKeys=true := by decide +kernel
theorem keys94_2 : subtree94_2.checkKeys=true := by decide +kernel
theorem keys94_3 : subtree94_3.checkKeys=true := by decide +kernel
theorem keys94_4 : subtree94_4.checkKeys=true := by decide +kernel
theorem keys94_5 : subtree94_5.checkKeys=true := by decide +kernel
theorem keys94_6 : subtree94_6.checkKeys=true := by decide +kernel
theorem keys94_7 : subtree94_7.checkKeys=true := by decide +kernel
theorem keys94 : subtree94.checkKeys=true := by
  simp only [subtree94,Tree.checkKeys,keys94_0,keys94_1,keys94_2,keys94_3,keys94_4,keys94_5,keys94_6,keys94_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree94)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys94
