-- Prove2me | solution 1 for SoficGroups.ErshovJaikinFiniteSpectral.inv_sqrt_eight_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/a1283f74-13ec-45a1-bf27-38e6f19c2d2a

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ErshovJaikinFiniteSpectral
open Filter Topology
universe u v
namespace SoficGroups.ErshovJaikinFiniteSpectral
theorem _root_.solution : 0 < (Real.sqrt (8 : ℝ))⁻¹ := by
  positivity
end SoficGroups.ErshovJaikinFiniteSpectral
