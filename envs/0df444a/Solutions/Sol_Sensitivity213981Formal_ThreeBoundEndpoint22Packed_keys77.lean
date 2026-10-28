-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys77
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:54:09.997146+00:00
-- url     : https://prove2.me/submissions/44343651-db66-4738-ba3a-cca1bf625c3d

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree077
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData077
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
theorem keys77_0 : subtree77_0.checkKeys=true := by decide +kernel
theorem keys77_1 : subtree77_1.checkKeys=true := by decide +kernel
theorem keys77_2 : subtree77_2.checkKeys=true := by decide +kernel
theorem keys77_3 : subtree77_3.checkKeys=true := by decide +kernel
theorem keys77_4 : subtree77_4.checkKeys=true := by decide +kernel
theorem keys77_5 : subtree77_5.checkKeys=true := by decide +kernel
theorem keys77_6 : subtree77_6.checkKeys=true := by decide +kernel
theorem keys77_7 : subtree77_7.checkKeys=true := by decide +kernel
theorem keys77 : subtree77.checkKeys=true := by
  simp only [subtree77,Tree.checkKeys,keys77_0,keys77_1,keys77_2,keys77_3,keys77_4,keys77_5,keys77_6,keys77_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree77)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys77
