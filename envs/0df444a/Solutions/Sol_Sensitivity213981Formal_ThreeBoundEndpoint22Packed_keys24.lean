-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys24
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:37:47.676042+00:00
-- url     : https://prove2.me/submissions/791cd137-f7b5-4c4d-bff1-d2678eb6e127

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree024
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData024
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
theorem keys24_0 : subtree24_0.checkKeys=true := by decide +kernel
theorem keys24_1 : subtree24_1.checkKeys=true := by decide +kernel
theorem keys24_2 : subtree24_2.checkKeys=true := by decide +kernel
theorem keys24_3 : subtree24_3.checkKeys=true := by decide +kernel
theorem keys24_4 : subtree24_4.checkKeys=true := by decide +kernel
theorem keys24_5 : subtree24_5.checkKeys=true := by decide +kernel
theorem keys24_6 : subtree24_6.checkKeys=true := by decide +kernel
theorem keys24_7 : subtree24_7.checkKeys=true := by decide +kernel
theorem keys24 : subtree24.checkKeys=true := by
  simp only [subtree24,Tree.checkKeys,keys24_0,keys24_1,keys24_2,keys24_3,keys24_4,keys24_5,keys24_6,keys24_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree24)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys24
