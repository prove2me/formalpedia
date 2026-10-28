-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys80
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:54:11.769215+00:00
-- url     : https://prove2.me/submissions/d47cb796-35fc-49c7-9f28-a98b42763d43

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedTree080
import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordTreeData080
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
theorem keys80_0 : subtree80_0.checkKeys=true := by decide +kernel
theorem keys80_1 : subtree80_1.checkKeys=true := by decide +kernel
theorem keys80_2 : subtree80_2.checkKeys=true := by decide +kernel
theorem keys80_3 : subtree80_3.checkKeys=true := by decide +kernel
theorem keys80_4 : subtree80_4.checkKeys=true := by decide +kernel
theorem keys80_5 : subtree80_5.checkKeys=true := by decide +kernel
theorem keys80_6 : subtree80_6.checkKeys=true := by decide +kernel
theorem keys80_7 : subtree80_7.checkKeys=true := by decide +kernel
theorem keys80 : subtree80.checkKeys=true := by
  simp only [subtree80,Tree.checkKeys,keys80_0,keys80_1,keys80_2,keys80_3,keys80_4,keys80_5,keys80_6,keys80_7,Bool.and_self]


end ThreeBoundEndpoint22Packed

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.checkKeys
    Sensitivity213981Formal.ThreeBoundEndpoint22Packed.subtree80)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.keys80
