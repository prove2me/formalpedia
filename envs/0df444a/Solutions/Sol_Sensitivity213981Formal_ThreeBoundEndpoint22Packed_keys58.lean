-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys58
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:44:10.077654+00:00
-- url     : https://prove2.me/submissions/f5ec0b56-e74a-43ff-a3de-a8f036b4b226

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree058
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData058
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
theorem keys58_0 : subtree58_0.checkKeys=true := by decide +kernel
theorem keys58_1 : subtree58_1.checkKeys=true := by decide +kernel
theorem keys58_2 : subtree58_2.checkKeys=true := by decide +kernel
theorem keys58_3 : subtree58_3.checkKeys=true := by decide +kernel
theorem keys58_4 : subtree58_4.checkKeys=true := by decide +kernel
theorem keys58_5 : subtree58_5.checkKeys=true := by decide +kernel
theorem keys58_6 : subtree58_6.checkKeys=true := by decide +kernel
theorem keys58_7 : subtree58_7.checkKeys=true := by decide +kernel
theorem keys58 : subtree58.checkKeys=true := by
  simp only [subtree58,Tree.checkKeys,keys58_0,keys58_1,keys58_2,keys58_3,keys58_4,keys58_5,keys58_6,keys58_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree58)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys58
