-- Prove2me | solution 1 for P2M_GlobalTheory_riemannTheta_unique_eq_jacobiTheta__4a1958799f58
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:53:02.861805+00:00
-- url     : https://prove2.me/submissions/a8c06fef-d6e5-45e7-99eb-b7bfe7119e49

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ]
namespace GlobalTheory
theorem _root_.solution [Unique ι] (a b : ι → ℝ) (Ω : Matrix ι ι ℂ)
    (v : ι → ℂ) :
    riemannTheta a b Ω v =
      cexp (π * I * (a default) ^ 2 * Ω default default +
        2 * π * I * a default * (v default + b default)) *
      jacobiTheta₂ (v default + b default + a default * Ω default default) (Ω default default) := by
  rw [riemannTheta_unique_eq_tsum, jacobiTheta₂, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [jacobiTheta₂_term, ← Complex.exp_add]
  congr 1
  ring
end GlobalTheory
