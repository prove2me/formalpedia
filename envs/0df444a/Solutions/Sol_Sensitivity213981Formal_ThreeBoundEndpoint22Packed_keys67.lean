-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys67
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:54:04.413874+00:00
-- url     : https://prove2.me/submissions/6cc09802-486d-4d80-8b1e-224999b356e7

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree067
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData067
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
theorem keys67_0 : subtree67_0.checkKeys=true := by decide +kernel
theorem keys67_1 : subtree67_1.checkKeys=true := by decide +kernel
theorem keys67_2 : subtree67_2.checkKeys=true := by decide +kernel
theorem keys67_3 : subtree67_3.checkKeys=true := by decide +kernel
theorem keys67_4 : subtree67_4.checkKeys=true := by decide +kernel
theorem keys67_5 : subtree67_5.checkKeys=true := by decide +kernel
theorem keys67_6 : subtree67_6.checkKeys=true := by decide +kernel
theorem keys67_7 : subtree67_7.checkKeys=true := by decide +kernel
theorem keys67 : subtree67.checkKeys=true := by
  simp only [subtree67,Tree.checkKeys,keys67_0,keys67_1,keys67_2,keys67_3,keys67_4,keys67_5,keys67_6,keys67_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree67)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys67
