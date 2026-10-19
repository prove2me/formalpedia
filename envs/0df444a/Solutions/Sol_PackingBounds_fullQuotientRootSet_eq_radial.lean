-- Prove2me | solution 1 for PackingBounds.fullQuotientRootSet_eq_radial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/1d44f2d3-fec2-49c0-9209-acf85624a355

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PackingBounds_fullQuotient_radialToFull
import Theorems.Thm_SpherePacking_Alternative_schwartzDilation_apply
import Theorems.Thm_SpherePacking_Alternative_schwartzDilation_zero
import Theorems.Thm_PackingBounds_fullQuotientSet_eq_radial
attribute [local simp] SpherePacking.Alternative.schwartzDilation_apply
attribute [local simp] SpherePacking.Alternative.schwartzDilation_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxHeartbeats 1600000
noncomputable section
open Filter
open scoped Topology
open PackingBounds
namespace PackingBounds
theorem _root_.solution (d : ℕ) :
    {q : ℝ | ∃ f : FullAdmissible d,
      fullQuotient f ^ ((d : ℝ)⁻¹) = q} =
      {q : ℝ | ∃ f : CohnElkies.Admissible d,
        CohnElkies.quotient f ^ ((d : ℝ)⁻¹) = q} := by
  ext q
  constructor
  · rintro ⟨f, hq⟩
    have hf : fullQuotient f ∈ CohnElkies.quotientSet d := by
      rw [← fullQuotientSet_eq_radial d]
      exact ⟨f, rfl⟩
    obtain ⟨g, hg⟩ := hf
    exact ⟨g, by simpa [hg] using hq⟩
  · rintro ⟨f, hq⟩
    exact ⟨radialToFull f, by simpa [fullQuotient_radialToFull] using hq⟩
end PackingBounds
