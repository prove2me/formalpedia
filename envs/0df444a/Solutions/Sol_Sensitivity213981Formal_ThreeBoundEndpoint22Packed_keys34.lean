-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys34
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:38:11.883148+00:00
-- url     : https://prove2.me/submissions/5e4d3f12-718c-4248-9e13-23c8c5df006e

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree034
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData034
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
theorem keys34_0 : subtree34_0.checkKeys=true := by decide +kernel
theorem keys34_1 : subtree34_1.checkKeys=true := by decide +kernel
theorem keys34_2 : subtree34_2.checkKeys=true := by decide +kernel
theorem keys34_3 : subtree34_3.checkKeys=true := by decide +kernel
theorem keys34_4 : subtree34_4.checkKeys=true := by decide +kernel
theorem keys34_5 : subtree34_5.checkKeys=true := by decide +kernel
theorem keys34_6 : subtree34_6.checkKeys=true := by decide +kernel
theorem keys34_7 : subtree34_7.checkKeys=true := by decide +kernel
theorem keys34 : subtree34.checkKeys=true := by
  simp only [subtree34,Tree.checkKeys,keys34_0,keys34_1,keys34_2,keys34_3,keys34_4,keys34_5,keys34_6,keys34_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree34)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys34
