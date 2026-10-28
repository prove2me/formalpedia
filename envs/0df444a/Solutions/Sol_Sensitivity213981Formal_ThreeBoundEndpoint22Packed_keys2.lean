-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys2
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:35:29.94863+00:00
-- url     : https://prove2.me/submissions/c1453ca3-dd31-44ff-9a75-ca5d46792368

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree002
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData002
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
theorem keys2_0 : subtree2_0.checkKeys=true := by decide +kernel
theorem keys2_1 : subtree2_1.checkKeys=true := by decide +kernel
theorem keys2_2 : subtree2_2.checkKeys=true := by decide +kernel
theorem keys2_3 : subtree2_3.checkKeys=true := by decide +kernel
theorem keys2_4 : subtree2_4.checkKeys=true := by decide +kernel
theorem keys2_5 : subtree2_5.checkKeys=true := by decide +kernel
theorem keys2_6 : subtree2_6.checkKeys=true := by decide +kernel
theorem keys2_7 : subtree2_7.checkKeys=true := by decide +kernel
theorem keys2 : subtree2.checkKeys=true := by
  simp only [subtree2,Tree.checkKeys,keys2_0,keys2_1,keys2_2,keys2_3,keys2_4,keys2_5,keys2_6,keys2_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree2)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys2
