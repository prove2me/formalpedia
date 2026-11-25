-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_lagrange_9c3712389ff7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:03:50.380171+00:00
-- url     : https://prove2.me/submissions/54099361-3597-42f5-9b41-bf2c3af75a24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_reInner_apply_5e2c6f879ab5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_sum_line_820fc4227819

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
theorem _root_.solution (z w : (Σ _ : Unit, Fin 2) → ℂ) :
    sqSum z * sqSum w - (reInner z w ^ 2 + reInner z (Complex.I • w) ^ 2) =
      Complex.normSq (z ⟨(), 0⟩ * w ⟨(), 1⟩ - z ⟨(), 1⟩ * w ⟨(), 0⟩) := by
  simp only [sqSum, reInner_apply, sum_line, Complex.sq_norm, Complex.normSq_apply, Pi.smul_apply,
    smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sub_re,
    Complex.sub_im]
  ring
end GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
