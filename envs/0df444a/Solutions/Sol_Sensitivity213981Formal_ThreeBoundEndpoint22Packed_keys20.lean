-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys20
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:36:42.201984+00:00
-- url     : https://prove2.me/submissions/509aa534-4a51-4cfe-9139-d7d8076ea451

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree020
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData020
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
theorem keys20_0 : subtree20_0.checkKeys=true := by decide +kernel
theorem keys20_1 : subtree20_1.checkKeys=true := by decide +kernel
theorem keys20_2 : subtree20_2.checkKeys=true := by decide +kernel
theorem keys20_3 : subtree20_3.checkKeys=true := by decide +kernel
theorem keys20_4 : subtree20_4.checkKeys=true := by decide +kernel
theorem keys20_5 : subtree20_5.checkKeys=true := by decide +kernel
theorem keys20_6 : subtree20_6.checkKeys=true := by decide +kernel
theorem keys20_7 : subtree20_7.checkKeys=true := by decide +kernel
theorem keys20 : subtree20.checkKeys=true := by
  simp only [subtree20,Tree.checkKeys,keys20_0,keys20_1,keys20_2,keys20_3,keys20_4,keys20_5,keys20_6,keys20_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree20)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys20
