-- Prove2me | solution 1 for SoficGroups.ejThreeProjectionAverage_fixed_iff_residualMap_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/41b11d43-2ad6-4da6-b216-d6046d6bce77

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
variable (V : Fin 3 → Submodule ℂ H)
  [∀ i, (V i).HasOrthogonalProjection]
namespace SoficGroups
theorem _root_.solution (x : H) :
    ejThreeProjectionAverage V x = x ↔
      ejThreeResidualMap V x = 0 := by
  constructor
  · intro h
    rw [ejThreeProjectionAverage_apply] at h
    have hz : (3 : ℂ)⁻¹ • ejThreeResidualMap V x = 0 :=
      sub_eq_self.mp h
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  · intro h
    simp [ejThreeProjectionAverage_apply, h]
end SoficGroups
