-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys61
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:44:41.04288+00:00
-- url     : https://prove2.me/submissions/ed65e02d-7729-4dbc-ba7e-4052170d11f4

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree061
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData061
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
theorem keys61_0 : subtree61_0.checkKeys=true := by decide +kernel
theorem keys61_1 : subtree61_1.checkKeys=true := by decide +kernel
theorem keys61_2 : subtree61_2.checkKeys=true := by decide +kernel
theorem keys61_3 : subtree61_3.checkKeys=true := by decide +kernel
theorem keys61_4 : subtree61_4.checkKeys=true := by decide +kernel
theorem keys61_5 : subtree61_5.checkKeys=true := by decide +kernel
theorem keys61_6 : subtree61_6.checkKeys=true := by decide +kernel
theorem keys61_7 : subtree61_7.checkKeys=true := by decide +kernel
theorem keys61 : subtree61.checkKeys=true := by
  simp only [subtree61,Tree.checkKeys,keys61_0,keys61_1,keys61_2,keys61_3,keys61_4,keys61_5,keys61_6,keys61_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree61)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys61
