-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys53
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:43:45.819061+00:00
-- url     : https://prove2.me/submissions/c4492d91-5e86-4e9f-bca1-a2d8ec66407f

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree053
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData053
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
theorem keys53_0 : subtree53_0.checkKeys=true := by decide +kernel
theorem keys53_1 : subtree53_1.checkKeys=true := by decide +kernel
theorem keys53_2 : subtree53_2.checkKeys=true := by decide +kernel
theorem keys53_3 : subtree53_3.checkKeys=true := by decide +kernel
theorem keys53_4 : subtree53_4.checkKeys=true := by decide +kernel
theorem keys53_5 : subtree53_5.checkKeys=true := by decide +kernel
theorem keys53_6 : subtree53_6.checkKeys=true := by decide +kernel
theorem keys53_7 : subtree53_7.checkKeys=true := by decide +kernel
theorem keys53 : subtree53.checkKeys=true := by
  simp only [subtree53,Tree.checkKeys,keys53_0,keys53_1,keys53_2,keys53_3,keys53_4,keys53_5,keys53_6,keys53_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree53)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys53
