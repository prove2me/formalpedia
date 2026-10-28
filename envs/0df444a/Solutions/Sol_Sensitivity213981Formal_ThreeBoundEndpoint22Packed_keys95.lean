-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys95
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:31:28.578648+00:00
-- url     : https://prove2.me/submissions/05803383-ac3e-4022-9c2c-ab5624a4c515

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree095
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData095
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
theorem keys95_0 : subtree95_0.checkKeys=true := by decide +kernel
theorem keys95_1 : subtree95_1.checkKeys=true := by decide +kernel
theorem keys95_2 : subtree95_2.checkKeys=true := by decide +kernel
theorem keys95_3 : subtree95_3.checkKeys=true := by decide +kernel
theorem keys95_4 : subtree95_4.checkKeys=true := by decide +kernel
theorem keys95_5 : subtree95_5.checkKeys=true := by decide +kernel
theorem keys95_6 : subtree95_6.checkKeys=true := by decide +kernel
theorem keys95_7 : subtree95_7.checkKeys=true := by decide +kernel
theorem keys95 : subtree95.checkKeys=true := by
  simp only [subtree95,Tree.checkKeys,keys95_0,keys95_1,keys95_2,keys95_3,keys95_4,keys95_5,keys95_6,keys95_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree95)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys95
