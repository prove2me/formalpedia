-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys18
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:36:33.095377+00:00
-- url     : https://prove2.me/submissions/a962eb01-7e82-460a-9d25-12b7c4e0a83c

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree018
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData018
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
theorem keys18_0 : subtree18_0.checkKeys=true := by decide +kernel
theorem keys18_1 : subtree18_1.checkKeys=true := by decide +kernel
theorem keys18_2 : subtree18_2.checkKeys=true := by decide +kernel
theorem keys18_3 : subtree18_3.checkKeys=true := by decide +kernel
theorem keys18_4 : subtree18_4.checkKeys=true := by decide +kernel
theorem keys18_5 : subtree18_5.checkKeys=true := by decide +kernel
theorem keys18_6 : subtree18_6.checkKeys=true := by decide +kernel
theorem keys18_7 : subtree18_7.checkKeys=true := by decide +kernel
theorem keys18 : subtree18.checkKeys=true := by
  simp only [subtree18,Tree.checkKeys,keys18_0,keys18_1,keys18_2,keys18_3,keys18_4,keys18_5,keys18_6,keys18_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree18)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys18
