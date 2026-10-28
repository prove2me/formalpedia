-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys14
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:36:04.011039+00:00
-- url     : https://prove2.me/submissions/f988328b-af7f-4e9d-8100-21b7c85e3994

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree014
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData014
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
theorem keys14_0 : subtree14_0.checkKeys=true := by decide +kernel
theorem keys14_1 : subtree14_1.checkKeys=true := by decide +kernel
theorem keys14_2 : subtree14_2.checkKeys=true := by decide +kernel
theorem keys14_3 : subtree14_3.checkKeys=true := by decide +kernel
theorem keys14_4 : subtree14_4.checkKeys=true := by decide +kernel
theorem keys14_5 : subtree14_5.checkKeys=true := by decide +kernel
theorem keys14_6 : subtree14_6.checkKeys=true := by decide +kernel
theorem keys14_7 : subtree14_7.checkKeys=true := by decide +kernel
theorem keys14 : subtree14.checkKeys=true := by
  simp only [subtree14,Tree.checkKeys,keys14_0,keys14_1,keys14_2,keys14_3,keys14_4,keys14_5,keys14_6,keys14_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree14)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys14
