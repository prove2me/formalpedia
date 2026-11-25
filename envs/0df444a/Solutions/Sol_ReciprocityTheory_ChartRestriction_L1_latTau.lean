-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.latTau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:45:33.486544+00:00
-- url     : https://prove2.me/submissions/14e14d1a-16cd-4787-a9e7-144a2d0e9c10

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLatTau
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_latTau_snd_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_latTau_im_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (L : PeriodPair) : ∃ (c : ℂ) (τ : ℍ), IsTauOf L c τ := by
  have h2 := latTau_snd_ne L
  rcases lt_or_gt_of_ne (latTau_im_ne L) with hneg | hpos
  · refine ⟨L.ω₂, ⟨-(L.ω₁ / L.ω₂), by rw [Complex.neg_im]; linarith⟩, h2, fun x => ?_⟩
    rw [PeriodPair.mem_lattice]
    try simp only [UpperHalfPlane.coe_mk]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨-m, n, by push_cast; field_simp; try ring⟩
    · rintro ⟨u, v, rfl⟩
      exact ⟨-u, v, by push_cast; field_simp; try ring⟩
  · refine ⟨L.ω₂, ⟨L.ω₁ / L.ω₂, hpos⟩, h2, fun x => ?_⟩
    rw [PeriodPair.mem_lattice]
    try simp only [UpperHalfPlane.coe_mk]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m, n, by field_simp; try ring⟩
    · rintro ⟨u, v, rfl⟩
      exact ⟨u, v, by field_simp; try ring⟩
end ReciprocityTheory.ChartRestriction.L1
