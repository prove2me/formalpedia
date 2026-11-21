-- Prove2me | solution 1 for RiemannMasullo.elementarySchwartzSeminorm_zero
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:18:37.90928+00:00
-- url     : https://prove2.me/submissions/b8466423-7a26-4260-b2c7-eefc5d617a19

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L430-L431
import Theorems.Thm_RiemannMasullo_elementarySchwartzBound_zero
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
open RiemannMasullo
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
theorem solution (f : ElementarySchwartz m n r F) :
    elementarySchwartzSeminorm (0, 0, 0, 0) f = ⨆ g, ‖f g‖ := by
  change (elementarySchwartzBound f.val (0,0,0,0)).toReal = _
  rw [elementarySchwartzBound_zero, ENNReal.toReal_iSup (fun _ ↦ ENNReal.coe_ne_top)]
  rfl
