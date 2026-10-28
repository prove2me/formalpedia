-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys36
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:38:43.654977+00:00
-- url     : https://prove2.me/submissions/03a7aebd-4049-480b-af48-cd01bd933c39

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree036
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData036
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
theorem keys36_0 : subtree36_0.checkKeys=true := by decide +kernel
theorem keys36_1 : subtree36_1.checkKeys=true := by decide +kernel
theorem keys36_2 : subtree36_2.checkKeys=true := by decide +kernel
theorem keys36_3 : subtree36_3.checkKeys=true := by decide +kernel
theorem keys36_4 : subtree36_4.checkKeys=true := by decide +kernel
theorem keys36_5 : subtree36_5.checkKeys=true := by decide +kernel
theorem keys36_6 : subtree36_6.checkKeys=true := by decide +kernel
theorem keys36_7 : subtree36_7.checkKeys=true := by decide +kernel
theorem keys36 : subtree36.checkKeys=true := by
  simp only [subtree36,Tree.checkKeys,keys36_0,keys36_1,keys36_2,keys36_3,keys36_4,keys36_5,keys36_6,keys36_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree36)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys36
