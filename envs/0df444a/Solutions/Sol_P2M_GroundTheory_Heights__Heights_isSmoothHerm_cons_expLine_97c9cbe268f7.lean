-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isSmoothHerm_cons_expLine_97c9cbe268f7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:45:29.895524+00:00
-- url     : https://prove2.me/submissions/a98ec4c5-0026-4a88-a4b3-27209e75d8e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isOpen_blockNonzero


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
open Filter Topology
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre isOpen_blockNonzero)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {n : ℕ}
    (v : ((Σ k, ι k) → ℂ) → ℝ) (hv : IsDegZeroSmooth v) (L : Fin n → HermLine ι)
    (hL : ∀ j, IsSmoothHerm (L j)) :
    ∀ j, IsSmoothHerm ((Fin.cons (expLine v hv) L : Fin (n + 1) → HermLine ι) j) := by
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · exact Real.contDiff_exp.comp_contDiffOn hv.1.neg.neg
  · simpa using hL j
end GroundTheory.Heights₂.Heights
