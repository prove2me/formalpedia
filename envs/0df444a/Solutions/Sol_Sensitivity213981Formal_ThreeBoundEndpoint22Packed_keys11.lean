-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys11
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:36:14.610452+00:00
-- url     : https://prove2.me/submissions/bd1b9337-cd64-439f-8fb2-7d0245762696

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree011
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData011
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
theorem keys11_0 : subtree11_0.checkKeys=true := by decide +kernel
theorem keys11_1 : subtree11_1.checkKeys=true := by decide +kernel
theorem keys11_2 : subtree11_2.checkKeys=true := by decide +kernel
theorem keys11_3 : subtree11_3.checkKeys=true := by decide +kernel
theorem keys11_4 : subtree11_4.checkKeys=true := by decide +kernel
theorem keys11_5 : subtree11_5.checkKeys=true := by decide +kernel
theorem keys11_6 : subtree11_6.checkKeys=true := by decide +kernel
theorem keys11_7 : subtree11_7.checkKeys=true := by decide +kernel
theorem keys11 : subtree11.checkKeys=true := by
  simp only [subtree11,Tree.checkKeys,keys11_0,keys11_1,keys11_2,keys11_3,keys11_4,keys11_5,keys11_6,keys11_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree11)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys11
