-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys49
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:43:08.731162+00:00
-- url     : https://prove2.me/submissions/7a540d36-07d3-4171-8f07-2ca521a49794

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree049
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData049
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
theorem keys49_0 : subtree49_0.checkKeys=true := by decide +kernel
theorem keys49_1 : subtree49_1.checkKeys=true := by decide +kernel
theorem keys49_2 : subtree49_2.checkKeys=true := by decide +kernel
theorem keys49_3 : subtree49_3.checkKeys=true := by decide +kernel
theorem keys49_4 : subtree49_4.checkKeys=true := by decide +kernel
theorem keys49_5 : subtree49_5.checkKeys=true := by decide +kernel
theorem keys49_6 : subtree49_6.checkKeys=true := by decide +kernel
theorem keys49_7 : subtree49_7.checkKeys=true := by decide +kernel
theorem keys49 : subtree49.checkKeys=true := by
  simp only [subtree49,Tree.checkKeys,keys49_0,keys49_1,keys49_2,keys49_3,keys49_4,keys49_5,keys49_6,keys49_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree49)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys49
