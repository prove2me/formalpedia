-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys27
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:37:48.24978+00:00
-- url     : https://prove2.me/submissions/4707430f-f2e0-43b2-ad2d-d4e938b9e790

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree027
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData027
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
theorem keys27_0 : subtree27_0.checkKeys=true := by decide +kernel
theorem keys27_1 : subtree27_1.checkKeys=true := by decide +kernel
theorem keys27_2 : subtree27_2.checkKeys=true := by decide +kernel
theorem keys27_3 : subtree27_3.checkKeys=true := by decide +kernel
theorem keys27_4 : subtree27_4.checkKeys=true := by decide +kernel
theorem keys27_5 : subtree27_5.checkKeys=true := by decide +kernel
theorem keys27_6 : subtree27_6.checkKeys=true := by decide +kernel
theorem keys27_7 : subtree27_7.checkKeys=true := by decide +kernel
theorem keys27 : subtree27.checkKeys=true := by
  simp only [subtree27,Tree.checkKeys,keys27_0,keys27_1,keys27_2,keys27_3,keys27_4,keys27_5,keys27_6,keys27_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree27)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys27
