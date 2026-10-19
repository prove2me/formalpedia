-- Prove2me | solution 1 for SoficGroups.ejThreeResidualEnergy_average_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/5e373669-9b24-472b-8462-bbaa958f1807

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ejThreeResidualEnergy_le_three_norm_sq
import Theorems.Thm_SoficGroups_ejThreeResidualEnergy_average

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
    (x : H) (δ : ℝ)
    (hgap : δ * ejThreeResidualEnergy V x ≤
      ‖ejThreeResidualMap V x‖ ^ 2) :
    ejThreeResidualEnergy V (ejThreeProjectionAverage V x) ≤
      (1 - δ / 3) * ejThreeResidualEnergy V x := by
  rw [ejThreeResidualEnergy_average]
  have hupper := ejThreeResidualEnergy_le_three_norm_sq V
    (ejThreeResidualMap V x)
  nlinarith
end SoficGroups
