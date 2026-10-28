-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys84
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:14:08.343106+00:00
-- url     : https://prove2.me/submissions/8f63fe7c-1900-49e9-99a6-1bd2454696b2

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree084
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData084
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
theorem keys84_0 : subtree84_0.checkKeys=true := by decide +kernel
theorem keys84_1 : subtree84_1.checkKeys=true := by decide +kernel
theorem keys84_2 : subtree84_2.checkKeys=true := by decide +kernel
theorem keys84_3 : subtree84_3.checkKeys=true := by decide +kernel
theorem keys84_4 : subtree84_4.checkKeys=true := by decide +kernel
theorem keys84_5 : subtree84_5.checkKeys=true := by decide +kernel
theorem keys84_6 : subtree84_6.checkKeys=true := by decide +kernel
theorem keys84_7 : subtree84_7.checkKeys=true := by decide +kernel
theorem keys84 : subtree84.checkKeys=true := by
  simp only [subtree84,Tree.checkKeys,keys84_0,keys84_1,keys84_2,keys84_3,keys84_4,keys84_5,keys84_6,keys84_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree84)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys84
