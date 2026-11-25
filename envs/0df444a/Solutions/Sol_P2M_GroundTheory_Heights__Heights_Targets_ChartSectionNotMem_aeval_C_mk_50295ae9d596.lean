-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ChartSectionNotMem_aeval_C_mk_50295ae9d596
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:32:25.094775+00:00
-- url     : https://prove2.me/submissions/e0e91def-7e67-4129-b956-64f92bd6f39e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothMetricOfIsSmoothHerm
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PChartSectionNotMem
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial Algebra
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsSectionOn mcPts segre)
open GroundTheory.Heights₂.Heights.Targets.ChartSectionNotMem
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets.ChartSectionNotMem
theorem _root_.solution (𝔮 : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (f : MvPolynomial (Σ k, ι k) ℂ) :
    aeval (fun q => (C (Ideal.Quotient.mk 𝔮 (X q)) : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))) f =
      C (Ideal.Quotient.mk 𝔮 f) := by
  have : (aeval fun q => (C (Ideal.Quotient.mk 𝔮 (X q)) : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))) =
      (IsScalarTower.toAlgHom ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)
        (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))).comp (Ideal.Quotient.mkₐ ℂ 𝔮) := by
    apply MvPolynomial.algHom_ext
    intro q
    simp [MvPolynomial.algebraMap_eq]
  rw [this]
  simp [MvPolynomial.algebraMap_eq]
end GroundTheory.Heights₂.Heights.Targets.ChartSectionNotMem
