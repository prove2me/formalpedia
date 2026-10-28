-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys89
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:31:24.77193+00:00
-- url     : https://prove2.me/submissions/fb01bc12-002c-468e-8f8a-87815b1f0fb0

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree089
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData089
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
theorem keys89_0 : subtree89_0.checkKeys=true := by decide +kernel
theorem keys89_1 : subtree89_1.checkKeys=true := by decide +kernel
theorem keys89_2 : subtree89_2.checkKeys=true := by decide +kernel
theorem keys89_3 : subtree89_3.checkKeys=true := by decide +kernel
theorem keys89_4 : subtree89_4.checkKeys=true := by decide +kernel
theorem keys89_5 : subtree89_5.checkKeys=true := by decide +kernel
theorem keys89_6 : subtree89_6.checkKeys=true := by decide +kernel
theorem keys89_7 : subtree89_7.checkKeys=true := by decide +kernel
theorem keys89 : subtree89.checkKeys=true := by
  simp only [subtree89,Tree.checkKeys,keys89_0,keys89_1,keys89_2,keys89_3,keys89_4,keys89_5,keys89_6,keys89_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree89)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys89
