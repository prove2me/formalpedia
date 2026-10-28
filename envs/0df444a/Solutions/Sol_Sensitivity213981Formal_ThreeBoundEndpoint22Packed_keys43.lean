-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys43
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:41:18.806846+00:00
-- url     : https://prove2.me/submissions/2fd93cd0-c24c-4412-bd9a-3d00b5fa61c2

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree043
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData043
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
theorem keys43_0 : subtree43_0.checkKeys=true := by decide +kernel
theorem keys43_1 : subtree43_1.checkKeys=true := by decide +kernel
theorem keys43_2 : subtree43_2.checkKeys=true := by decide +kernel
theorem keys43_3 : subtree43_3.checkKeys=true := by decide +kernel
theorem keys43_4 : subtree43_4.checkKeys=true := by decide +kernel
theorem keys43_5 : subtree43_5.checkKeys=true := by decide +kernel
theorem keys43_6 : subtree43_6.checkKeys=true := by decide +kernel
theorem keys43_7 : subtree43_7.checkKeys=true := by decide +kernel
theorem keys43 : subtree43.checkKeys=true := by
  simp only [subtree43,Tree.checkKeys,keys43_0,keys43_1,keys43_2,keys43_3,keys43_4,keys43_5,keys43_6,keys43_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree43)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys43
