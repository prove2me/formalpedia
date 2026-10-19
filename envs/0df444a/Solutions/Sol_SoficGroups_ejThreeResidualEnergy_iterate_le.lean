-- Prove2me | solution 1 for SoficGroups.ejThreeResidualEnergy_iterate_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/3e2b56f4-90a5-47b7-9400-8130bbe4dc0a

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ejThreeResidualEnergy_average_le

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
    (δ : ℝ) (hδ : δ ≤ 3)
    (hgap : ∀ x : H,
      δ * ejThreeResidualEnergy V x ≤ ‖ejThreeResidualMap V x‖ ^ 2)
    (x : H) (n : ℕ) :
    ejThreeResidualEnergy V
        (((ejThreeProjectionAverage V : H → H)^[n]) x) ≤
      (1 - δ / 3) ^ n * ejThreeResidualEnergy V x := by
  have hnonneg : 0 ≤ 1 - δ / 3 := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc
        ejThreeResidualEnergy V
            (ejThreeProjectionAverage V
              (((ejThreeProjectionAverage V : H → H)^[n]) x)) ≤
          (1 - δ / 3) * ejThreeResidualEnergy V
            (((ejThreeProjectionAverage V : H → H)^[n]) x) :=
          ejThreeResidualEnergy_average_le V _ δ (hgap _)
        _ ≤ (1 - δ / 3) *
            ((1 - δ / 3) ^ n * ejThreeResidualEnergy V x) :=
          mul_le_mul_of_nonneg_left ih hnonneg
        _ = (1 - δ / 3) ^ n.succ *
            ejThreeResidualEnergy V x := by
          rw [pow_succ]
          ring
end SoficGroups
