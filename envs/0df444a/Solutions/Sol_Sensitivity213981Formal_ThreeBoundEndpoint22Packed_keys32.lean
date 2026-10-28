-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys32
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:31:19.127023+00:00
-- url     : https://prove2.me/submissions/984d9f52-78f1-4f7f-8aa2-30b98c352b83

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree032
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData032
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
theorem keys32_0 : subtree32_0.checkKeys=true := by decide +kernel
theorem keys32_1 : subtree32_1.checkKeys=true := by decide +kernel
theorem keys32_2 : subtree32_2.checkKeys=true := by decide +kernel
theorem keys32_3 : subtree32_3.checkKeys=true := by decide +kernel
theorem keys32_4 : subtree32_4.checkKeys=true := by decide +kernel
theorem keys32_5 : subtree32_5.checkKeys=true := by decide +kernel
theorem keys32_6 : subtree32_6.checkKeys=true := by decide +kernel
theorem keys32_7 : subtree32_7.checkKeys=true := by decide +kernel
theorem keys32 : subtree32.checkKeys=true := by
  simp only [subtree32,Tree.checkKeys,keys32_0,keys32_1,keys32_2,keys32_3,keys32_4,keys32_5,keys32_6,keys32_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree32)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys32
