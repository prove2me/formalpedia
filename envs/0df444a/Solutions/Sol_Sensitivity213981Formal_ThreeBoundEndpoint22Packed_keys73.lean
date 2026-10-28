-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys73
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:54:07.870595+00:00
-- url     : https://prove2.me/submissions/21d18e3b-8caf-4749-a748-27fcd90f01a9

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree073
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData073
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
theorem keys73_0 : subtree73_0.checkKeys=true := by decide +kernel
theorem keys73_1 : subtree73_1.checkKeys=true := by decide +kernel
theorem keys73_2 : subtree73_2.checkKeys=true := by decide +kernel
theorem keys73_3 : subtree73_3.checkKeys=true := by decide +kernel
theorem keys73_4 : subtree73_4.checkKeys=true := by decide +kernel
theorem keys73_5 : subtree73_5.checkKeys=true := by decide +kernel
theorem keys73_6 : subtree73_6.checkKeys=true := by decide +kernel
theorem keys73_7 : subtree73_7.checkKeys=true := by decide +kernel
theorem keys73 : subtree73.checkKeys=true := by
  simp only [subtree73,Tree.checkKeys,keys73_0,keys73_1,keys73_2,keys73_3,keys73_4,keys73_5,keys73_6,keys73_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree73)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys73
