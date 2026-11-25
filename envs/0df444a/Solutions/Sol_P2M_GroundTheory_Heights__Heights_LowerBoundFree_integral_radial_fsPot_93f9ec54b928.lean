-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_integral_radial_fsPot_93f9ec54b928
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:03:46.848553+00:00
-- url     : https://prove2.me/submissions/58f9d9e0-c480-4b5e-9256-98eb6574028d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFsPotLaplacian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PFsPotLaplacian

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open InnerProductSpace Laplacian Real MeasureTheory Filter Topology Set
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution :
    ∫ s in Ioi (0 : ℝ), s ^ (2 - 1) • (2 / (1 + s ^ 2) ^ 2) = 1 := by
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun s : ℝ => -(1 + s ^ 2)⁻¹)
      (x ^ (2 - 1) • (2 / (1 + x ^ 2) ^ 2)) x := by
    intro x _
    have hx : (1 + x ^ 2) ≠ 0 := by positivity
    have h := (((hasDerivAt_pow 2 x).const_add 1).inv hx).neg
    refine h.congr_deriv ?_
    rw [smul_eq_mul, neg_div, neg_neg]
    push_cast
    ring
  have htend : Tendsto (fun s : ℝ => -(1 + s ^ 2)⁻¹) atTop (𝓝 0) := by
    have h : Tendsto (fun s : ℝ => 1 + s ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero)
    simpa using h.inv_tendsto_atTop.neg
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv (fun x hx => by
    have : (0 : ℝ) < x := hx
    positivity) htend
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend]
  norm_num
end GroundTheory.Heights₂.Heights.LowerBoundFree
