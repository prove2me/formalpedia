-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys25
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:36:59.133364+00:00
-- url     : https://prove2.me/submissions/73359858-7c4f-42d5-8f66-ff6c263210e4

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree025
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData025
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
theorem keys25_0 : subtree25_0.checkKeys=true := by decide +kernel
theorem keys25_1 : subtree25_1.checkKeys=true := by decide +kernel
theorem keys25_2 : subtree25_2.checkKeys=true := by decide +kernel
theorem keys25_3 : subtree25_3.checkKeys=true := by decide +kernel
theorem keys25_4 : subtree25_4.checkKeys=true := by decide +kernel
theorem keys25_5 : subtree25_5.checkKeys=true := by decide +kernel
theorem keys25_6 : subtree25_6.checkKeys=true := by decide +kernel
theorem keys25_7 : subtree25_7.checkKeys=true := by decide +kernel
theorem keys25 : subtree25.checkKeys=true := by
  simp only [subtree25,Tree.checkKeys,keys25_0,keys25_1,keys25_2,keys25_3,keys25_4,keys25_5,keys25_6,keys25_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree25)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys25
