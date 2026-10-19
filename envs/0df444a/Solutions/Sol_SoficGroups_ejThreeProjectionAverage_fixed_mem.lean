-- Prove2me | solution 1 for SoficGroups.ejThreeProjectionAverage_fixed_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/b249a1ee-17cf-44f1-b3e5-6087405512a0

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ejThreeResidualEnergy_eq_re_inner
import Theorems.Thm_SoficGroups_ejThreeProjectionAverage_fixed_iff_residualMap_eq_zero
import Theorems.Thm_SoficGroups_ejThreeResidualEnergy_eq_zero_iff

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
variable (V : Fin 3 → Submodule ℂ H)
  [∀ i, (V i).HasOrthogonalProjection]
namespace SoficGroups
theorem _root_.solution
    (x : H) (hx : ejThreeProjectionAverage V x = x)
    (i : Fin 3) : x ∈ V i := by
  have hD : ejThreeResidualMap V x = 0 :=
    (ejThreeProjectionAverage_fixed_iff_residualMap_eq_zero V x).mp hx
  have hE : ejThreeResidualEnergy V x = 0 := by
    rw [ejThreeResidualEnergy_eq_re_inner V x, hD]
    simp
  have hres : ejResidualProjection (V i) x = 0 :=
    (ejThreeResidualEnergy_eq_zero_iff V x).mp hE i
  rw [ejResidualProjection_apply, sub_eq_zero] at hres
  exact Submodule.starProjection_eq_self_iff.mp hres.symm
end SoficGroups
