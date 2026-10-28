-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRelaxed.mem_options
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:57:12.790995+00:00
-- url     : https://prove2.me/submissions/884d8340-e405-46b2-81c8-10340b6ed461

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedStateSearch
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
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith


namespace Sensitivity213981Formal
section
/- Complete degree/incoming search for the relaxed q3 record table. -/


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

namespace ThreeBoundRelaxed
open ThreeBoundQ3











theorem mem_options (n ng : ℕ) (s : State) (hs : Local n ng s) :
    s∈options n ng s.kind := by
  obtain ⟨hd,hl,hu⟩ := hs
  apply List.mem_flatMap.mpr
  refine ⟨s.out,List.mem_range.mpr (by omega),?_⟩
  dsimp only
  rw [if_pos (by omega : ng-indicator s.kind-s.out≤ min (ng-indicator s.kind) (n-1-s.out))]
  apply List.mem_map.mpr
  refine ⟨s.incoming-(ng-indicator s.kind-s.out),List.mem_range.mpr (by omega),?_⟩
  cases s
  simp only [State.mk.injEq, true_and]
  simp only at hl
  omega







































end ThreeBoundRelaxed



end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (n ng : Nat) (s : Sensitivity213981Formal.ThreeBoundRelaxed.State)
  (hs : Sensitivity213981Formal.ThreeBoundRelaxed.Local n ng s),
  @Membership.mem.{0, 0} Sensitivity213981Formal.ThreeBoundRelaxed.State
    (List.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State)
    (@List.instMembership.{0} Sensitivity213981Formal.ThreeBoundRelaxed.State)
    (Sensitivity213981Formal.ThreeBoundRelaxed.options n ng (Sensitivity213981Formal.ThreeBoundRelaxed.State.kind s)) s := @Sensitivity213981Formal.ThreeBoundRelaxed.mem_options
