-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys30
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:37:31.205823+00:00
-- url     : https://prove2.me/submissions/e5d9133f-ce1d-4e4c-ab5c-46d67e607cf0

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree030
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData030
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
theorem keys30_0 : subtree30_0.checkKeys=true := by decide +kernel
theorem keys30_1 : subtree30_1.checkKeys=true := by decide +kernel
theorem keys30_2 : subtree30_2.checkKeys=true := by decide +kernel
theorem keys30_3 : subtree30_3.checkKeys=true := by decide +kernel
theorem keys30_4 : subtree30_4.checkKeys=true := by decide +kernel
theorem keys30_5 : subtree30_5.checkKeys=true := by decide +kernel
theorem keys30_6 : subtree30_6.checkKeys=true := by decide +kernel
theorem keys30_7 : subtree30_7.checkKeys=true := by decide +kernel
theorem keys30 : subtree30.checkKeys=true := by
  simp only [subtree30,Tree.checkKeys,keys30_0,keys30_1,keys30_2,keys30_3,keys30_4,keys30_5,keys30_6,keys30_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree30)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys30
