-- Prove2me | solution 1 for PackingBounds.fullQuotientSet_eq_radial_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/eaf9083f-419c-42ba-9f0b-9c8a77f9f8db

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PackingBounds_fullQuotient_radialToFull

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
namespace PackingBounds
theorem _root_.solution (d : ℕ) :
    fullQuotientSet d = CohnElkies.quotientSet d ↔
      ∀ f : FullAdmissible d,
        ∃ g : CohnElkies.Admissible d,
          CohnElkies.quotient g = fullQuotient f := by
  constructor
  · intro h f
    have hf : fullQuotient f ∈ fullQuotientSet d := ⟨f, rfl⟩
    rw [h] at hf
    exact hf
  · intro h
    apply Set.Subset.antisymm
    · rintro _ ⟨f, rfl⟩
      exact h f
    · rintro _ ⟨f, rfl⟩
      exact ⟨radialToFull f, fullQuotient_radialToFull f⟩
end PackingBounds
