-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys26
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:37:08.094149+00:00
-- url     : https://prove2.me/submissions/5ef01491-06e3-4503-a30f-cdaefce2103b

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree026
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData026
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
theorem keys26_0 : subtree26_0.checkKeys=true := by decide +kernel
theorem keys26_1 : subtree26_1.checkKeys=true := by decide +kernel
theorem keys26_2 : subtree26_2.checkKeys=true := by decide +kernel
theorem keys26_3 : subtree26_3.checkKeys=true := by decide +kernel
theorem keys26_4 : subtree26_4.checkKeys=true := by decide +kernel
theorem keys26_5 : subtree26_5.checkKeys=true := by decide +kernel
theorem keys26_6 : subtree26_6.checkKeys=true := by decide +kernel
theorem keys26_7 : subtree26_7.checkKeys=true := by decide +kernel
theorem keys26 : subtree26.checkKeys=true := by
  simp only [subtree26,Tree.checkKeys,keys26_0,keys26_1,keys26_2,keys26_3,keys26_4,keys26_5,keys26_6,keys26_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree26)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys26
