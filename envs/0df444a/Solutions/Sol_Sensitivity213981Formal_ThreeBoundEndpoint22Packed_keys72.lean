-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys72
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:54:07.284537+00:00
-- url     : https://prove2.me/submissions/e8a3602f-4ccd-4e14-a41c-0a6ba9457a75

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree072
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData072
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
theorem keys72_0 : subtree72_0.checkKeys=true := by decide +kernel
theorem keys72_1 : subtree72_1.checkKeys=true := by decide +kernel
theorem keys72_2 : subtree72_2.checkKeys=true := by decide +kernel
theorem keys72_3 : subtree72_3.checkKeys=true := by decide +kernel
theorem keys72_4 : subtree72_4.checkKeys=true := by decide +kernel
theorem keys72_5 : subtree72_5.checkKeys=true := by decide +kernel
theorem keys72_6 : subtree72_6.checkKeys=true := by decide +kernel
theorem keys72_7 : subtree72_7.checkKeys=true := by decide +kernel
theorem keys72 : subtree72.checkKeys=true := by
  simp only [subtree72,Tree.checkKeys,keys72_0,keys72_1,keys72_2,keys72_3,keys72_4,keys72_5,keys72_6,keys72_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree72)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys72
