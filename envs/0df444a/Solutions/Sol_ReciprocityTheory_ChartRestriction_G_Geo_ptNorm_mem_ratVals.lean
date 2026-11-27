-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.ptNorm_mem_ratVals
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:26:05.612985+00:00
-- url     : https://prove2.me/submissions/15474fc3-0392-499a-ba7d-3b64f4073afe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenVol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial Filter
variable {o : Type*} [CommRing o] {Ω : Type*} [CommRing Ω] [Algebra o Ω] {ι : Type*}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (m : ConeMetric ℂ ι) (σ : o →+* ℂ) (x : ι → Ω) {τ : ℕ}
    {f : MvPolynomial ι o} (hf : f ∈ homogeneousSubmodule ι o τ) {z : ι → ℂ}
    (hz : z ∈ conePts σ (coordIdeal o x)) :
    ptNorm m σ τ f z ∈ ratVals m σ x τ (aeval x f) := by
  refine ⟨0, f, 1, z, by simpa using hf, ?_, by simp, hz, by simp, ?_⟩
  · exact (MvPolynomial.mem_homogeneousSubmodule 0 1).2 (MvPolynomial.isHomogeneous_one ι o)
  · simp [ptNorm]
end ReciprocityTheory.ChartRestriction.G.Geo
