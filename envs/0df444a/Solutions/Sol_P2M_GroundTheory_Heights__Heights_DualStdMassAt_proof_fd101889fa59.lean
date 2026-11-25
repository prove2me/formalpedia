-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualStdMassAt_proof_fd101889fa59
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:49:27.380993+00:00
-- url     : https://prove2.me/submissions/c4fef2a0-0ff7-4de4-9186-662b9509167e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdMassAt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_sheetDensity_eq_214530a51d79
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_fibre_eq_0dc2611b461d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_planePt_injective_171c08794023
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_isSheet_planePt_d21b65221f69
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology Matrix
noncomputable section
open StandardDualMassAtPoint
namespace GroundTheory.Heights₂.Heights
namespace DualStdMassAt
theorem _root_.solution (hOn : DualPtsOnPlane.Statement) (hOf : DualPtsOfPlane.Statement) :
    DualStdMassAt.Statement := by
  intro K _ _ D F T _ _ b hb hF
  have hint : ∀ y : Fin D → ℂ, ∑ᶠ w ∈ fibre (dualIdeal b) (dualProj b hb) y,
      sheetDensity (dualIdeal b) (dualProj b hb) (fun _ z => Real.log ((dualLine F b hb).h z))
        (fun _ => 1) y w = (Fintype.card (K →+* ℂ) : ℝ) * maDensity (fun _ : Fin D => gbPot) y := by
    intro y
    rw [fibre_eq hOn hOf b hb y, finsum_mem_range (planePt_injective b hb y),
      finsum_eq_sum_of_fintype,
      Finset.sum_congr rfl fun σ _ => sheetDensity_eq hOn hF b hb ⟨_, isSheet_planePt hOf b hb σ y⟩,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold ptsIntegralAt
  simp only [hint]
  rw [integral_const_mul, integral_maDensity_gbPot, mul_one]
end DualStdMassAt
end GroundTheory.Heights₂.Heights
