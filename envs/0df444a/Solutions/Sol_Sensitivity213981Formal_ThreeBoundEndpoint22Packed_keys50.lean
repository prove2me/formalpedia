-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys50
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:43:45.321522+00:00
-- url     : https://prove2.me/submissions/b21b136b-c3bb-40c0-80f2-2db43b8450a0

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree050
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData050
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
theorem keys50_0 : subtree50_0.checkKeys=true := by decide +kernel
theorem keys50_1 : subtree50_1.checkKeys=true := by decide +kernel
theorem keys50_2 : subtree50_2.checkKeys=true := by decide +kernel
theorem keys50_3 : subtree50_3.checkKeys=true := by decide +kernel
theorem keys50_4 : subtree50_4.checkKeys=true := by decide +kernel
theorem keys50_5 : subtree50_5.checkKeys=true := by decide +kernel
theorem keys50_6 : subtree50_6.checkKeys=true := by decide +kernel
theorem keys50_7 : subtree50_7.checkKeys=true := by decide +kernel
theorem keys50 : subtree50.checkKeys=true := by
  simp only [subtree50,Tree.checkKeys,keys50_0,keys50_1,keys50_2,keys50_3,keys50_4,keys50_5,keys50_6,keys50_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree50)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys50
