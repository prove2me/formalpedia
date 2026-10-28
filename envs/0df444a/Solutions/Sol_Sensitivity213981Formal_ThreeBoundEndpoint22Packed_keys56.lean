-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys56
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:43:53.81012+00:00
-- url     : https://prove2.me/submissions/fcfce134-d388-4078-a09f-41cfc68f5b57

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree056
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData056
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
theorem keys56_0 : subtree56_0.checkKeys=true := by decide +kernel
theorem keys56_1 : subtree56_1.checkKeys=true := by decide +kernel
theorem keys56_2 : subtree56_2.checkKeys=true := by decide +kernel
theorem keys56_3 : subtree56_3.checkKeys=true := by decide +kernel
theorem keys56_4 : subtree56_4.checkKeys=true := by decide +kernel
theorem keys56_5 : subtree56_5.checkKeys=true := by decide +kernel
theorem keys56_6 : subtree56_6.checkKeys=true := by decide +kernel
theorem keys56_7 : subtree56_7.checkKeys=true := by decide +kernel
theorem keys56 : subtree56.checkKeys=true := by
  simp only [subtree56,Tree.checkKeys,keys56_0,keys56_1,keys56_2,keys56_3,keys56_4,keys56_5,keys56_6,keys56_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree56)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys56
