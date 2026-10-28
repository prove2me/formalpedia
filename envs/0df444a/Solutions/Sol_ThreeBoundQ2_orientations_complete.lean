-- Prove2me | solution 1 for ThreeBoundQ2.orientations_complete
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:39:04.118591+00:00
-- url     : https://prove2.me/submissions/dfec95d6-a817-46ad-b794-e4972dcb14f2

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Definitions.Def_Sensitivity213303_Q2Enumeration


section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ThreeBoundQ2
end ThreeBoundQ2
open ThreeBoundQ2
variable {V : Type} [DecidableEq V]

theorem solution (es : List (V × V)) (ds : List Bool) (b : V → ℕ)
    (hlen : ds.length = es.length) (hb : ∀ v, outCount es ds v ≤ b v) :
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
          · have hpos : 0 < b e.1 := by
              have h := hb e.1
              simp only [outCount, Bool.false_eq_true, ↓reduceIte] at h
              omega
            have hrest : ∀ v, outCount es ds v ≤ spend b e.1 v := by
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
          · have hpos : 0 < b e.2 := by
              have h := hb e.2
              simp only [outCount, ↓reduceIte] at h
              omega
            have hrest : ∀ v, outCount es ds v ≤ spend b e.2 v := by
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
end
