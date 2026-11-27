-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjStdMassAt_proof_4e8665ed6da9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:07:41.592826+00:00
-- url     : https://prove2.me/submissions/2e8eb10f-1a62-4735-abe3-7a184104dfb2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjStdMassAt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_sheetDensity_eq_9d629b041c12
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_fibre_eq_077cda411379
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_planePt_injective_df97cc17290a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_isSheet_planePt_91ba55760afb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_integral_maDensity_gbPot


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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology Matrix NumberField
noncomputable section
open ProjectiveStandardMassAtPoint
namespace GroundTheory.Heights₂.Heights
namespace ProjStdMassAt
theorem _root_.solution (hOn : ProjPtsOnPlane.Statement) (hOf : ProjPtsOfPlane.Statement) :
    ProjStdMassAt.Statement := by
  intro K _ _ D F hF
  have hint : ∀ y : Fin D → ℂ, ∑ᶠ w ∈ fibre (projSpaceIdeal K (D + 1)) projProj y,
      sheetDensity (projSpaceIdeal K (D + 1)) projProj (fun _ z => Real.log ((latticeLine F).h z))
        (fun _ => 1) y w = (Fintype.card (K →+* ℂ) : ℝ) * maDensity (fun _ : Fin D => gbPot) y := by
    intro y
    rw [fibre_eq hOn hOf y, finsum_mem_range (planePt_injective y),
      finsum_eq_sum_of_fintype,
      Finset.sum_congr rfl fun σ _ => sheetDensity_eq hOn hF ⟨_, isSheet_planePt hOf σ y⟩,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold ptsIntegralAt
  simp only [hint]
  rw [integral_const_mul, integral_maDensity_gbPot, mul_one]
end ProjStdMassAt
end GroundTheory.Heights₂.Heights
