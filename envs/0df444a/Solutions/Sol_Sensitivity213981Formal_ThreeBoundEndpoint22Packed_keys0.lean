-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys0
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:35:19.670988+00:00
-- url     : https://prove2.me/submissions/a1b3052a-c59e-4586-974b-65870fcdce2a

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree000
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData000
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
theorem keys0_0 : subtree0_0.checkKeys=true := by decide +kernel
theorem keys0_1 : subtree0_1.checkKeys=true := by decide +kernel
theorem keys0_2 : subtree0_2.checkKeys=true := by decide +kernel
theorem keys0_3 : subtree0_3.checkKeys=true := by decide +kernel
theorem keys0_4 : subtree0_4.checkKeys=true := by decide +kernel
theorem keys0_5 : subtree0_5.checkKeys=true := by decide +kernel
theorem keys0_6 : subtree0_6.checkKeys=true := by decide +kernel
theorem keys0_7 : subtree0_7.checkKeys=true := by decide +kernel
theorem keys0 : subtree0.checkKeys=true := by
  simp only [subtree0,Tree.checkKeys,keys0_0,keys0_1,keys0_2,keys0_3,keys0_4,keys0_5,keys0_6,keys0_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree0)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys0
