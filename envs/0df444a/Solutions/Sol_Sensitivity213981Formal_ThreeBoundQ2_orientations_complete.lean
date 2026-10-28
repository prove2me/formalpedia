-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundQ2.orientations_complete
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:33:10.839965+00:00
-- url     : https://prove2.me/submissions/efcc8e51-f7c0-4049-80d3-f6e9f52ef6ac

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_Q2Enumeration
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort


namespace Sensitivity213981Formal
section
/-
An executable, exhaustive enumerator of the eight q <= 2 high-row types and
their budget-feasible tournament orientations.  The completeness proof is
structural, not an assertion that a foreign program enumerated all cases.

This module supplies finite combinatorial coverage.  It does not prove the
semantic charging inequalities for the sensitivity transfer.
-/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundQ2















section Orientations
variable {V : Type} [DecidableEq V]







theorem orientations_complete (es : List (V × V)) (ds : List Bool) (b : V → ℕ)
    (hlen : ds.length = es.length) (hb : ∀ v, outCount es ds v ≤  b v) :
    ds ∈ orientations b es := by
  induction es generalizing ds b with
  | nil =>
      have : ds = [] := List.length_eq_zero_iff.mp hlen
      subst ds
      simp [orientations]
  | cons e es ih =>
      cases ds with
      | nil => simp at hlen
      | cons d ds =>
          have hlen' : ds.length = es.length := by simpa using hlen
          cases d
          · have hpos : 0 <  b e.1 := by
              have h := hb e.1
              simp only [outCount, Bool.false_eq_true, ↓reduceIte] at h
              omega
            have hrest : ∀ v, outCount es ds v ≤  spend b e.1 v := by
              intro v
              have h := hb v
              by_cases hv : v = e.1
              · subst v
                simp only [outCount, Bool.false_eq_true, ↓reduceIte] at h
                simp only [spend, ↓reduceIte]
                omega
              · have hv' : e.1 ≠ v := Ne.symm hv
                simpa [outCount, spend, hv, hv'] using h
            apply List.mem_append_left
            rw [if_pos hpos]
            exact List.mem_map.mpr ⟨ds, ih ds (spend b e.1) hlen' hrest, rfl⟩
          · have hpos : 0 <  b e.2 := by
              have h := hb e.2
              simp only [outCount, ↓reduceIte] at h
              omega
            have hrest : ∀ v, outCount es ds v ≤  spend b e.2 v := by
              intro v
              have h := hb v
              by_cases hv : v = e.2
              · subst v
                simp only [outCount, ↓reduceIte] at h
                simp only [spend, ↓reduceIte]
                omega
              · have hv' : e.2 ≠ v := Ne.symm hv
                simpa [outCount, spend, hv, hv'] using h
            apply List.mem_append_right
            rw [if_pos hpos]
            exact List.mem_map.mpr ⟨ds, ih ds (spend b e.2) hlen' hrest, rfl⟩

end Orientations





















end ThreeBoundQ2





end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {V : Type} [inst : DecidableEq.{1} V] (es : List.{0} (Prod.{0, 0} V V)) (ds : List.{0} Bool) (b : V → Nat)
  (hlen : @Eq.{1} Nat (@List.length.{0} Bool ds) (@List.length.{0} (Prod.{0, 0} V V) es))
  (hb : ∀ (v : V), @LE.le.{0} Nat instLENat (@Sensitivity213981Formal.ThreeBoundQ2.outCount V inst es ds v) (b v)),
  @Membership.mem.{0, 0} (List.{0} Bool) (List.{0} (List.{0} Bool)) (@List.instMembership.{0} (List.{0} Bool))
    (@Sensitivity213981Formal.ThreeBoundQ2.orientations V inst b es) ds := @Sensitivity213981Formal.ThreeBoundQ2.orientations_complete
