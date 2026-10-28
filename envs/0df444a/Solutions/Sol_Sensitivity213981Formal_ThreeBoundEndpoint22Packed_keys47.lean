-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys47
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:42:46.978861+00:00
-- url     : https://prove2.me/submissions/cc1c9fdb-c59a-4388-8dae-3ec161b35932

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree047
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData047
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
theorem keys47_0 : subtree47_0.checkKeys=true := by decide +kernel
theorem keys47_1 : subtree47_1.checkKeys=true := by decide +kernel
theorem keys47_2 : subtree47_2.checkKeys=true := by decide +kernel
theorem keys47_3 : subtree47_3.checkKeys=true := by decide +kernel
theorem keys47_4 : subtree47_4.checkKeys=true := by decide +kernel
theorem keys47_5 : subtree47_5.checkKeys=true := by decide +kernel
theorem keys47_6 : subtree47_6.checkKeys=true := by decide +kernel
theorem keys47_7 : subtree47_7.checkKeys=true := by decide +kernel
theorem keys47 : subtree47.checkKeys=true := by
  simp only [subtree47,Tree.checkKeys,keys47_0,keys47_1,keys47_2,keys47_3,keys47_4,keys47_5,keys47_6,keys47_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree47)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys47
