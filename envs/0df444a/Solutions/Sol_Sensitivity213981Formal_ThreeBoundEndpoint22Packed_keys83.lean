-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys83
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:31:21.095391+00:00
-- url     : https://prove2.me/submissions/6e6bbdf5-aa5c-47bf-936b-59ffc1137a12

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree083
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData083
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
theorem keys83_0 : subtree83_0.checkKeys=true := by decide +kernel
theorem keys83_1 : subtree83_1.checkKeys=true := by decide +kernel
theorem keys83_2 : subtree83_2.checkKeys=true := by decide +kernel
theorem keys83_3 : subtree83_3.checkKeys=true := by decide +kernel
theorem keys83_4 : subtree83_4.checkKeys=true := by decide +kernel
theorem keys83_5 : subtree83_5.checkKeys=true := by decide +kernel
theorem keys83_6 : subtree83_6.checkKeys=true := by decide +kernel
theorem keys83_7 : subtree83_7.checkKeys=true := by decide +kernel
theorem keys83 : subtree83.checkKeys=true := by
  simp only [subtree83,Tree.checkKeys,keys83_0,keys83_1,keys83_2,keys83_3,keys83_4,keys83_5,keys83_6,keys83_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree83)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys83
