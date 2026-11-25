-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_resProj_eq_local_78e4d1ce2a23
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:50:49.082053+00:00
-- url     : https://prove2.me/submissions/721004d5-a9a9-4528-bad4-d759065408cd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResBadNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UnitChartOperator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullLift
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_psi_pt_eq_07dfae5440e6
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
theorem _root_.solution (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {x y : R.R.M}
    (hy : y ∈ R.R.src (R.idx x)) :
    resProj R Ψ y = fun i => Ψ (segre (R.liftAt x y)) i.succ / Ψ (segre (R.liftAt x y)) 0 := by
  obtain ⟨μ, hμ, hμeq⟩ := psi_pt_eq R hy Ψ
  funext i
  simp only [resProj, hμeq, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hμ
end GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
