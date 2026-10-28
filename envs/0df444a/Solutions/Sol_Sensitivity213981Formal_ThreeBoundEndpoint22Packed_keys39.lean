-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys39
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:40:09.04485+00:00
-- url     : https://prove2.me/submissions/4571a450-9532-43d0-84e8-c7954b469b1e

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree039
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData039
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
theorem keys39_0 : subtree39_0.checkKeys=true := by decide +kernel
theorem keys39_1 : subtree39_1.checkKeys=true := by decide +kernel
theorem keys39_2 : subtree39_2.checkKeys=true := by decide +kernel
theorem keys39_3 : subtree39_3.checkKeys=true := by decide +kernel
theorem keys39_4 : subtree39_4.checkKeys=true := by decide +kernel
theorem keys39_5 : subtree39_5.checkKeys=true := by decide +kernel
theorem keys39_6 : subtree39_6.checkKeys=true := by decide +kernel
theorem keys39_7 : subtree39_7.checkKeys=true := by decide +kernel
theorem keys39 : subtree39.checkKeys=true := by
  simp only [subtree39,Tree.checkKeys,keys39_0,keys39_1,keys39_2,keys39_3,keys39_4,keys39_5,keys39_6,keys39_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree39)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys39
