-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys17
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:37:07.550835+00:00
-- url     : https://prove2.me/submissions/8eed4be1-8517-496d-9c47-fbcb234fbe1f

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree017
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData017
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
theorem keys17_0 : subtree17_0.checkKeys=true := by decide +kernel
theorem keys17_1 : subtree17_1.checkKeys=true := by decide +kernel
theorem keys17_2 : subtree17_2.checkKeys=true := by decide +kernel
theorem keys17_3 : subtree17_3.checkKeys=true := by decide +kernel
theorem keys17_4 : subtree17_4.checkKeys=true := by decide +kernel
theorem keys17_5 : subtree17_5.checkKeys=true := by decide +kernel
theorem keys17_6 : subtree17_6.checkKeys=true := by decide +kernel
theorem keys17_7 : subtree17_7.checkKeys=true := by decide +kernel
theorem keys17 : subtree17.checkKeys=true := by
  simp only [subtree17,Tree.checkKeys,keys17_0,keys17_1,keys17_2,keys17_3,keys17_4,keys17_5,keys17_6,keys17_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree17)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys17
