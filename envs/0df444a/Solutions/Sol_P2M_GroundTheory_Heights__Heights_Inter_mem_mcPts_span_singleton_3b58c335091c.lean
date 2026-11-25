-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_mem_mcPts_span_singleton_3b58c335091c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:03:21.151733+00:00
-- url     : https://prove2.me/submissions/bf77e37a-7f80-43d1-baa3-e3eaaf7814df

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PZeroSetNull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {s : MRing ι} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    (hs : eval z (map (Int.castRingHom ℂ) s) = 0) : z ∈ mcPts (Ideal.span {s}) := by
  refine ⟨hz.1, fun f hf => ?_⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
  rw [map_mul, map_mul, hs, mul_zero]
end GroundTheory.Heights₂.Heights.Inter
