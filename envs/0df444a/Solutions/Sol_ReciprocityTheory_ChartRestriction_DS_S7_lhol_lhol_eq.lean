-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.lhol_lhol_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:07.227178+00:00
-- url     : https://prove2.me/submissions/86160329-4ea9-4b30-a8e8-c278756ecdc0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {z : Matrix (Fin n) (Fin n) ℂ}
    (hF : ContDiffAt ℂ 2 F z) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Lhol X (Lhol Y F) z = fderiv ℂ F z (Y * (X * z)) + fderiv ℂ (fderiv ℂ F) z (X * z) (Y * z) := by
  unfold Lhol
  have hc : DifferentiableAt ℂ (fderiv ℂ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hu : HasFDerivAt (fun y : Matrix (Fin n) (Fin n) ℂ => Y * y) (mulLeftCLM Y) z :=
    (mulLeftCLM Y).hasFDerivAt
  have h := hc.hasFDerivAt.clm_apply hu
  erw [h.fderiv]
  rfl
end ReciprocityTheory.ChartRestriction.DS.S7
