-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegreChartDim_mem_mcPts_iff_053177c2ad13
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:16:51.769748+00:00
-- url     : https://prove2.me/submissions/fb02ee62-e0b6-4c6f-9930-c46badab4a9b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothMetricOfIsSmoothHerm
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar mcPts segre)
open GroundTheory.Heights₂.Heights.SegreChartDim
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.SegreChartDim
theorem _root_.solution {P : Ideal (MRing ι)} (z : (Σ k, ι k) → ℂ) :
    z ∈ mcPts P ↔ z ∈ ReciprocityTheory.AnForm.R.conePts (P.map (MvPolynomial.map (Int.castRingHom ℂ))) := by
  refine and_congr_right fun _ => ⟨fun h f hf => ?_, fun h f hf => h _ (Ideal.mem_map_of_mem _ hf)⟩
  have hle : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ RingHom.ker (MvPolynomial.eval z) := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    exact h g hg
  exact hle hf
end GroundTheory.Heights₂.Heights.SegreChartDim
