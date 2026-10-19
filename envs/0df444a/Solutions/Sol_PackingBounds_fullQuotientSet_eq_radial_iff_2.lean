-- Prove2me | solution 2 for PackingBounds.fullQuotientSet_eq_radial_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:19:07.763091+00:00
-- url     : https://prove2.me/submissions/f00f2b55-f3d1-4dd2-af1f-2af68bf51cd7

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap Topology
open PackingBounds


theorem solution (d : ℕ) :
    fullQuotientSet d = CohnElkies.quotientSet d ↔
      ∀ f : FullAdmissible d,
        ∃ g : CohnElkies.Admissible d,
          CohnElkies.quotient g = fullQuotient f := by
  constructor
  · intro h f
    have hm : fullQuotient f ∈ fullQuotientSet d := ⟨f, rfl⟩
    rw [h] at hm
    obtain ⟨g, hg⟩ := hm
    exact ⟨g, hg⟩
  · intro h
    ext q; constructor
    · rintro ⟨f, rfl⟩
      obtain ⟨g, hg⟩ := h f
      exact ⟨g, hg⟩
    · rintro ⟨g, rfl⟩
      exact ⟨radialToFull g, rfl⟩

