-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys42
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:41:02.853566+00:00
-- url     : https://prove2.me/submissions/691ae1da-64d1-4147-b450-d0386581a353

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree042
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData042
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
theorem keys42_0 : subtree42_0.checkKeys=true := by decide +kernel
theorem keys42_1 : subtree42_1.checkKeys=true := by decide +kernel
theorem keys42_2 : subtree42_2.checkKeys=true := by decide +kernel
theorem keys42_3 : subtree42_3.checkKeys=true := by decide +kernel
theorem keys42_4 : subtree42_4.checkKeys=true := by decide +kernel
theorem keys42_5 : subtree42_5.checkKeys=true := by decide +kernel
theorem keys42_6 : subtree42_6.checkKeys=true := by decide +kernel
theorem keys42_7 : subtree42_7.checkKeys=true := by decide +kernel
theorem keys42 : subtree42.checkKeys=true := by
  simp only [subtree42,Tree.checkKeys,keys42_0,keys42_1,keys42_2,keys42_3,keys42_4,keys42_5,keys42_6,keys42_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree42)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys42
