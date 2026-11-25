-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_integrable_fibreSum_degZero_510e47a67880
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:38:43.453982+00:00
-- url     : https://prove2.me/submissions/f811b350-8143-4adf-b22f-a1752bfb1084

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsAddFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDeLeSemiPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegrePartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_LogRegLineTensor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_LelongSectionLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_LelongChartLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongSectionLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSectionOn_one_8921dcb39a7e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isSectionOn_one


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution (hInt : PtsIntegrableStatement) {Q : Ideal (MRing ι)} {e : ℕ}
    (hQ : IsArithVar Q (e + 1)) {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ : IsGoodProj Q Ψ)
    {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) {u : ((Σ k, ι k) → ℂ) → ℝ}
    (hu : IsDegZeroSmooth u) :
    Integrable (fun y => ∑ᶠ w ∈ fibre Q Ψ y, sheetDensity Q Ψ (pot L) u y w) := by
  have hsm : IsSmoothHerm (HermLine.ofWeight u hu.2) :=
    Real.contDiff_exp.comp_contDiffOn hu.1.neg
  have h := hInt K ι Q e Ψ L (HermLine.ofWeight u hu.2) 1 hQ hΨ hL hsm
    (Inter.isSectionOn_one hQ rfl)
  have hlog : logNorm (HermLine.ofWeight u hu.2) 1 = u := by
    funext z
    simp [logNorm, HermLine.ofWeight, Real.log_inv, Real.log_exp]
  rwa [hlog] at h
end GroundTheory.Heights₂.Heights.Targets
