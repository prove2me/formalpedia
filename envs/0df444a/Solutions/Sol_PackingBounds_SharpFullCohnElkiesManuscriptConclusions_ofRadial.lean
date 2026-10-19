-- Prove2me | solution 1 for PackingBounds.SharpFullCohnElkiesManuscriptConclusions.ofRadial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/4cdeaf30-8554-4a28-9401-0535a53574ac

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_sharpCohnElkiesManuscriptConclusions
import Theorems.Thm_SpherePacking_Alternative_schwartzDilation_apply
import Theorems.Thm_SpherePacking_Alternative_schwartzDilation_zero
import Theorems.Thm_PackingBounds_fullQuotientSet_eq_radial
import Theorems.Thm_PackingBounds_fullLinearProgram_eq_radial
import Theorems.Thm_PackingBounds_fullQuotientRootSet_eq_radial
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
namespace SharpFullCohnElkiesManuscriptConclusions
theorem _root_.solution :
    SharpFullCohnElkiesManuscriptConclusions := by
  have hradial := CohnElkies.sharpCohnElkiesManuscriptConclusions
  refine
    { root_before_infimum := ?_
      root_before_infimum_vanishing_error := ?_
      linear_program_root := ?_
      natural_logarithmic_rate := ?_
      natural_vanishing_exponential_error := ?_
      universal_nonnegative_delta := ?_
      base_two_exponent_positive := hradial.base_two_exponent_positive
      base_two_decimal_certificate := hradial.base_two_decimal_certificate
      base_two_logarithmic_rate := ?_
      base_two_vanishing_exponential_error := ?_ }
  · simpa only [fullQuotientRootSet_eq_radial] using
      hradial.root_before_infimum
  · obtain ⟨err, herr, hformula⟩ :=
      hradial.root_before_infimum_vanishing_error
    exact ⟨err, herr, by simpa only [fullQuotientRootSet_eq_radial] using hformula⟩
  · simpa only [fullLinearProgram_eq_radial] using
      hradial.linear_program_root
  · simpa only [fullLinearProgram_eq_radial] using
      hradial.natural_logarithmic_rate
  · obtain ⟨err, herr, hformula⟩ :=
      hradial.natural_vanishing_exponential_error
    exact ⟨err, herr, by simpa only [fullLinearProgram_eq_radial] using hformula⟩
  · obtain ⟨δ, hδ, hnonneg, hbound⟩ :=
      hradial.universal_nonnegative_delta
    refine ⟨δ, hδ, hnonneg, ?_⟩
    filter_upwards [hbound] with d hd f
    have hf : fullQuotient f ∈ CohnElkies.quotientSet d := by
      rw [← fullQuotientSet_eq_radial d]
      exact ⟨f, rfl⟩
    obtain ⟨g, hg⟩ := hf
    simpa [hg] using hd g
  · simpa only [fullLinearProgram_eq_radial] using
      hradial.base_two_logarithmic_rate
  · obtain ⟨err, herr, hformula⟩ :=
      hradial.base_two_vanishing_exponential_error
    exact ⟨err, herr, by simpa only [fullLinearProgram_eq_radial] using hformula⟩
end SharpFullCohnElkiesManuscriptConclusions
end PackingBounds
