-- Prove2me | solution 1 for SoficGroups.ThompsonFFiniteQuotient.conjugation_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/24cbcc5d-1a29-4dbd-ba3d-cf4a51370da9

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFFiniteQuotient
variable {G : Type*} [Group G]
namespace SoficGroups.ThompsonFFiniteQuotient
theorem _root_.solution (a u v w : G)
    (h : u⁻¹ * v * u = w) :
    (a⁻¹ * u * a)⁻¹ * (a⁻¹ * v * a) *
        (a⁻¹ * u * a) = a⁻¹ * w * a := by
  calc
    (a⁻¹ * u * a)⁻¹ * (a⁻¹ * v * a) *
        (a⁻¹ * u * a) = a⁻¹ * (u⁻¹ * v * u) * a := by
      group
    _ = a⁻¹ * w * a := by rw [h]
end SoficGroups.ThompsonFFiniteQuotient
