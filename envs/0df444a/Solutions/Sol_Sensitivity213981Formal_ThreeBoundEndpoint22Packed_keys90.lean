-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys90
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:31:25.45698+00:00
-- url     : https://prove2.me/submissions/bf5f3e46-7d74-4a83-a1be-d69e6a75610f

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree090
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData090
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
theorem keys90_0 : subtree90_0.checkKeys=true := by decide +kernel
theorem keys90_1 : subtree90_1.checkKeys=true := by decide +kernel
theorem keys90_2 : subtree90_2.checkKeys=true := by decide +kernel
theorem keys90_3 : subtree90_3.checkKeys=true := by decide +kernel
theorem keys90_4 : subtree90_4.checkKeys=true := by decide +kernel
theorem keys90_5 : subtree90_5.checkKeys=true := by decide +kernel
theorem keys90_6 : subtree90_6.checkKeys=true := by decide +kernel
theorem keys90_7 : subtree90_7.checkKeys=true := by decide +kernel
theorem keys90 : subtree90.checkKeys=true := by
  simp only [subtree90,Tree.checkKeys,keys90_0,keys90_1,keys90_2,keys90_3,keys90_4,keys90_5,keys90_6,keys90_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree90)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys90
