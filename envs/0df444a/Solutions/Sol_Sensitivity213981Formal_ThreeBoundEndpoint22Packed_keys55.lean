-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys55
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:43:53.187069+00:00
-- url     : https://prove2.me/submissions/f2b92d20-c7c4-41c9-aefa-0f6527dc82c2

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree055
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData055
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
theorem keys55_0 : subtree55_0.checkKeys=true := by decide +kernel
theorem keys55_1 : subtree55_1.checkKeys=true := by decide +kernel
theorem keys55_2 : subtree55_2.checkKeys=true := by decide +kernel
theorem keys55_3 : subtree55_3.checkKeys=true := by decide +kernel
theorem keys55_4 : subtree55_4.checkKeys=true := by decide +kernel
theorem keys55_5 : subtree55_5.checkKeys=true := by decide +kernel
theorem keys55_6 : subtree55_6.checkKeys=true := by decide +kernel
theorem keys55_7 : subtree55_7.checkKeys=true := by decide +kernel
theorem keys55 : subtree55.checkKeys=true := by
  simp only [subtree55,Tree.checkKeys,keys55_0,keys55_1,keys55_2,keys55_3,keys55_4,keys55_5,keys55_6,keys55_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree55)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys55
