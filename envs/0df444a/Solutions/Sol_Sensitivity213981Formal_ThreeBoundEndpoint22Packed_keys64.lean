-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys64
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:44:47.877601+00:00
-- url     : https://prove2.me/submissions/75c04d6e-5483-40ab-9828-08b34dcea3e8

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree064
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData064
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
theorem keys64_0 : subtree64_0.checkKeys=true := by decide +kernel
theorem keys64_1 : subtree64_1.checkKeys=true := by decide +kernel
theorem keys64_2 : subtree64_2.checkKeys=true := by decide +kernel
theorem keys64_3 : subtree64_3.checkKeys=true := by decide +kernel
theorem keys64_4 : subtree64_4.checkKeys=true := by decide +kernel
theorem keys64_5 : subtree64_5.checkKeys=true := by decide +kernel
theorem keys64_6 : subtree64_6.checkKeys=true := by decide +kernel
theorem keys64_7 : subtree64_7.checkKeys=true := by decide +kernel
theorem keys64 : subtree64.checkKeys=true := by
  simp only [subtree64,Tree.checkKeys,keys64_0,keys64_1,keys64_2,keys64_3,keys64_4,keys64_5,keys64_6,keys64_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree64)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys64
