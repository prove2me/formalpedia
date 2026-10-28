-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys19
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:36:57.974247+00:00
-- url     : https://prove2.me/submissions/7c09a2c1-5ca7-4650-8bdd-8f5326d63cbf

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree019
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData019
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
theorem keys19_0 : subtree19_0.checkKeys=true := by decide +kernel
theorem keys19_1 : subtree19_1.checkKeys=true := by decide +kernel
theorem keys19_2 : subtree19_2.checkKeys=true := by decide +kernel
theorem keys19_3 : subtree19_3.checkKeys=true := by decide +kernel
theorem keys19_4 : subtree19_4.checkKeys=true := by decide +kernel
theorem keys19_5 : subtree19_5.checkKeys=true := by decide +kernel
theorem keys19_6 : subtree19_6.checkKeys=true := by decide +kernel
theorem keys19_7 : subtree19_7.checkKeys=true := by decide +kernel
theorem keys19 : subtree19.checkKeys=true := by
  simp only [subtree19,Tree.checkKeys,keys19_0,keys19_1,keys19_2,keys19_3,keys19_4,keys19_5,keys19_6,keys19_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree19)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys19
