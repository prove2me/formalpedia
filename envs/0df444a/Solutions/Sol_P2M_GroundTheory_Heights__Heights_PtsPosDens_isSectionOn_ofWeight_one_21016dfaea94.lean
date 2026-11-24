-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsPosDens_isSectionOn_ofWeight_one_21016dfaea94
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:56:58.974406+00:00
-- url     : https://prove2.me/submissions/68285e38-c797-4e8b-bb81-34ffe9b30fbc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosDensIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsSumMeasurableA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsPosDensMeasurable

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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo InnerProductSpace Laplacian
open GroundTheory.Heights₂.Heights.PtsPosDens
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.PtsPosDens
theorem _root_.solution {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d)
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) :
    IsSectionOn P (HermLine.ofWeight g hg.2) 1 := by
  refine ⟨0, fun k => by simp [HermLine.ofWeight], fun m hm k => ?_,
    fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)⟩
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp
end GroundTheory.Heights₂.Heights.PtsPosDens
