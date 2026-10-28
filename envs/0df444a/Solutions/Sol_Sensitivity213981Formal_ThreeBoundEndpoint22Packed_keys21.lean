-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys21
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:36:49.28434+00:00
-- url     : https://prove2.me/submissions/35195b96-94cb-43b5-966e-379f678b19bd

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree021
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData021
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
theorem keys21_0 : subtree21_0.checkKeys=true := by decide +kernel
theorem keys21_1 : subtree21_1.checkKeys=true := by decide +kernel
theorem keys21_2 : subtree21_2.checkKeys=true := by decide +kernel
theorem keys21_3 : subtree21_3.checkKeys=true := by decide +kernel
theorem keys21_4 : subtree21_4.checkKeys=true := by decide +kernel
theorem keys21_5 : subtree21_5.checkKeys=true := by decide +kernel
theorem keys21_6 : subtree21_6.checkKeys=true := by decide +kernel
theorem keys21_7 : subtree21_7.checkKeys=true := by decide +kernel
theorem keys21 : subtree21.checkKeys=true := by
  simp only [subtree21,Tree.checkKeys,keys21_0,keys21_1,keys21_2,keys21_3,keys21_4,keys21_5,keys21_6,keys21_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree21)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys21
