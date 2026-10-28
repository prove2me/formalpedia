-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRelaxedCoverage.typeLists_length
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:55:41.00285+00:00
-- url     : https://prove2.me/submissions/8020d117-42cb-435f-acf7-2172229009ec

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedRecordCoverage
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


namespace Sensitivity213981Formal
section
/- Composition of the canonical degree-state cover with finite lookup checks. -/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundRelaxedCoverage
open ThreeBoundQ3 ThreeBoundRelaxed



theorem typeLists_length (lo n : ℕ) (ts : List Kind)
    (h : ts∈ThreeBoundQ3.typeLists lo n) : ts.length=n := by
  induction n generalizing lo ts with
  | zero =>
      have he : ts=[] := by simpa only [ThreeBoundQ3.typeLists,List.mem_singleton] using h
      simp [he]
  | succ n ih =>
      obtain ⟨t,ht,hm⟩ := List.mem_flatMap.mp h
      by_cases hlo : lo≤ orderKey t
      · rw [if_pos hlo] at hm
        obtain ⟨rest,hr,rfl⟩ := List.mem_map.mp hm
        simp only [List.length_cons,ih (orderKey t) rest hr]
      · rw [if_neg hlo] at hm
        contradiction







end ThreeBoundRelaxedCoverage



end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (lo n : Nat) (ts : List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
  (h :
    @Membership.mem.{0, 0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind)
      (List.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind))
      (@List.instMembership.{0} (List.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind))
      (Sensitivity213981Formal.ThreeBoundQ3.typeLists lo n) ts),
  @Eq.{1} Nat (@List.length.{0} Sensitivity213981Formal.ThreeBoundQ3.Kind ts) n := @Sensitivity213981Formal.ThreeBoundRelaxedCoverage.typeLists_length
