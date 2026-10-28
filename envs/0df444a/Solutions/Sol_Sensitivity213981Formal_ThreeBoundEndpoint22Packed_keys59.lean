-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys59
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:44:19.487666+00:00
-- url     : https://prove2.me/submissions/92be7349-e8b9-4b86-a4fe-59d9ba8c9b4f

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree059
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData059
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
theorem keys59_0 : subtree59_0.checkKeys=true := by decide +kernel
theorem keys59_1 : subtree59_1.checkKeys=true := by decide +kernel
theorem keys59_2 : subtree59_2.checkKeys=true := by decide +kernel
theorem keys59_3 : subtree59_3.checkKeys=true := by decide +kernel
theorem keys59_4 : subtree59_4.checkKeys=true := by decide +kernel
theorem keys59_5 : subtree59_5.checkKeys=true := by decide +kernel
theorem keys59_6 : subtree59_6.checkKeys=true := by decide +kernel
theorem keys59_7 : subtree59_7.checkKeys=true := by decide +kernel
theorem keys59 : subtree59.checkKeys=true := by
  simp only [subtree59,Tree.checkKeys,keys59_0,keys59_1,keys59_2,keys59_3,keys59_4,keys59_5,keys59_6,keys59_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree59)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys59
