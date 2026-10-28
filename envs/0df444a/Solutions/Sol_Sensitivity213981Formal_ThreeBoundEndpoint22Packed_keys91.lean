-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys91
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:31:26.161024+00:00
-- url     : https://prove2.me/submissions/c7726716-91ac-4f44-93a6-50753f0542ba

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree091
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData091
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
theorem keys91_0 : subtree91_0.checkKeys=true := by decide +kernel
theorem keys91_1 : subtree91_1.checkKeys=true := by decide +kernel
theorem keys91_2 : subtree91_2.checkKeys=true := by decide +kernel
theorem keys91_3 : subtree91_3.checkKeys=true := by decide +kernel
theorem keys91_4 : subtree91_4.checkKeys=true := by decide +kernel
theorem keys91_5 : subtree91_5.checkKeys=true := by decide +kernel
theorem keys91_6 : subtree91_6.checkKeys=true := by decide +kernel
theorem keys91_7 : subtree91_7.checkKeys=true := by decide +kernel
theorem keys91 : subtree91.checkKeys=true := by
  simp only [subtree91,Tree.checkKeys,keys91_0,keys91_1,keys91_2,keys91_3,keys91_4,keys91_5,keys91_6,keys91_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree91)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys91
