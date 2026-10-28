-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys68
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:54:05.031489+00:00
-- url     : https://prove2.me/submissions/b96cfb51-ef8e-4852-bc8a-e7f9a275640b

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree068
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData068
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
theorem keys68_0 : subtree68_0.checkKeys=true := by decide +kernel
theorem keys68_1 : subtree68_1.checkKeys=true := by decide +kernel
theorem keys68_2 : subtree68_2.checkKeys=true := by decide +kernel
theorem keys68_3 : subtree68_3.checkKeys=true := by decide +kernel
theorem keys68_4 : subtree68_4.checkKeys=true := by decide +kernel
theorem keys68_5 : subtree68_5.checkKeys=true := by decide +kernel
theorem keys68_6 : subtree68_6.checkKeys=true := by decide +kernel
theorem keys68_7 : subtree68_7.checkKeys=true := by decide +kernel
theorem keys68 : subtree68.checkKeys=true := by
  simp only [subtree68,Tree.checkKeys,keys68_0,keys68_1,keys68_2,keys68_3,keys68_4,keys68_5,keys68_6,keys68_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree68)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys68
