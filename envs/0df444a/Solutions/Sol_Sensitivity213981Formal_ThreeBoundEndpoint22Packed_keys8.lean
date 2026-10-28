-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys8
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:36:13.330493+00:00
-- url     : https://prove2.me/submissions/72b441b3-7966-4113-8410-3b18cef2d74d

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree008
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData008
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
theorem keys8_0 : subtree8_0.checkKeys=true := by decide +kernel
theorem keys8_1 : subtree8_1.checkKeys=true := by decide +kernel
theorem keys8_2 : subtree8_2.checkKeys=true := by decide +kernel
theorem keys8_3 : subtree8_3.checkKeys=true := by decide +kernel
theorem keys8_4 : subtree8_4.checkKeys=true := by decide +kernel
theorem keys8_5 : subtree8_5.checkKeys=true := by decide +kernel
theorem keys8_6 : subtree8_6.checkKeys=true := by decide +kernel
theorem keys8_7 : subtree8_7.checkKeys=true := by decide +kernel
theorem keys8 : subtree8.checkKeys=true := by
  simp only [subtree8,Tree.checkKeys,keys8_0,keys8_1,keys8_2,keys8_3,keys8_4,keys8_5,keys8_6,keys8_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree8)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys8
