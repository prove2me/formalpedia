-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_gbPot_contDiff_2c49dcd22e3f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:00.254822+00:00
-- url     : https://prove2.me/submissions/ed74915e-14d7-4dd9-98c0-5354c8099fdb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbG_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbPot_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo
open scoped ENNReal ComplexOrder
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
theorem _root_.solution : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbPot (D := 1)) := by
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG (D := 1)) := by
    unfold ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG
    exact contDiff_const.add (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i))
  have h := (hG.log fun y => (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG_pos y).ne').div_const 2
  have e : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbPot (D := 1) =
      fun y => Real.log (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG y) / 2 :=
    funext fun y => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbPot_eq y
  rw [e]
  exact h
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
