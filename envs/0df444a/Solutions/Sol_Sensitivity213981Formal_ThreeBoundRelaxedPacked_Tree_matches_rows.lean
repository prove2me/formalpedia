-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.matches_rows
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:52:54.853855+00:00
-- url     : https://prove2.me/submissions/47e469a0-e33b-445e-9fd6-c9b5bbee6ba1

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
namespace ThreeBoundRelaxedPacked
open ThreeBoundEndpoint22Records (decodeRow)


theorem Tree.matches_rows (t : Tree) (u : ThreeBoundRecordLookup.Tree) (h : t.Matches u) :
    t.rows=u.elements := by
  induction t generalizing u with
  | leaf key code =>
      cases u with
      | leaf row =>
          change decodeRow 41 code=row at h
          exact congrArg (fun r : List ℕ=>[r]) h
      | branch pivot l r => exact False.elim h
  | branch pivot l r hl hr =>
      cases u with
      | leaf row => exact False.elim h
      | branch pivot' l' r' =>
          exact congrArg₂ List.append (hl l' h.1) (hr r' h.2)
end ThreeBoundRelaxedPacked

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (t : Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree) (u : Sensitivity213981Formal.ThreeBoundRecordLookup.Tree)
  (h : Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.Matches t u),
  @Eq.{1} (List.{0} (List.{0} Nat)) (Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.rows t)
    (Sensitivity213981Formal.ThreeBoundRecordLookup.Tree.elements u) := @Sensitivity213981Formal.ThreeBoundRelaxedPacked.Tree.matches_rows
