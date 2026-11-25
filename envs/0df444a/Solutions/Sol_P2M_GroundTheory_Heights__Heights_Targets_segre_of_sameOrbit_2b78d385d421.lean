-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_segre_of_sameOrbit_2b78d385d421
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:21:59.765802+00:00
-- url     : https://prove2.me/submissions/5028396c-b79e-48cf-bc20-af600c3fcc27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegularFibre

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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    ∃ c : ℂ, c ≠ 0 ∧ segre z = c • (segre z' : ((k : K) → ι k) → ℂ) := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨∏ k, c k, Finset.prod_ne_zero_iff.mpr fun k _ => hc k, ?_⟩
  funext i
  simp [segre, Finset.prod_mul_distrib]
end GroundTheory.Heights₂.Heights.Targets
