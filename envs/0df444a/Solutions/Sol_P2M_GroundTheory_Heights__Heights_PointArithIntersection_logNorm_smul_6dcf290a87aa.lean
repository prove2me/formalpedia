-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointArithIntersection_logNorm_smul_6dcf290a87aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:47:20.422872+00:00
-- url     : https://prove2.me/submissions/13a9d48e-9134-451d-b623-2abf6b14a05c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIsSheetFinZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPointArInt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_scaleBlock


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.PointArithIntersection
open IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
variable {T : Type} [Fintype T]
namespace GroundTheory.Heights₂.Heights.PointArithIntersection
theorem _root_.solution {A : HermLine (fun _ : Unit => T)} {s : MRing (fun _ : Unit => T)}
    {P : Ideal (MRing (fun _ : Unit => T))} (hs : IsSectionOn P A s) (c : ℂ) (hc : c ≠ 0)
    (z : (Σ _ : Unit, T) → ℂ) : logNorm A s (fun p => c * z p) = logNorm A s z := by
  obtain ⟨a, ha, hhom, -⟩ := hs
  have hz : (fun p : Σ _ : Unit, T => c * z p) = scaleBlock () c z := by
    funext p
    simp [scaleBlock]
  have hh : A.h (fun p => c * z p) = ‖c‖ ^ A.a () * A.h z := by
    simpa using A.smul (fun _ => c) z (fun _ => hc)
  unfold logNorm
  rw [hh, hz, eval_scaleBlock () c z s a hhom, ha (), zpow_natCast, norm_mul, norm_pow]
  rw [mul_div_mul_left _ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hc))]
end GroundTheory.Heights₂.Heights.PointArithIntersection
