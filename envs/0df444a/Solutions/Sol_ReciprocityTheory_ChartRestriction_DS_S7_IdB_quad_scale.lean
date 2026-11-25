-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.IdB.quad_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:31.052502+00:00
-- url     : https://prove2.me/submissions/1ec00f19-3fa2-4f4f-8d08-80ba28d57cc6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IdThmB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.IdB
namespace ReciprocityTheory.ChartRestriction.DS.S7.IdB
theorem _root_.solution (x : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (t : ℝ) :
    (star ((t : ℂ) • v) ⬝ᵥ (x *ᵥ ((t : ℂ) • v))).re = t ^ 2 * (star v ⬝ᵥ (x *ᵥ v)).re := by
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    ← mul_assoc]
  have : (t : ℂ) * star (t : ℂ) = ((t ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]; push_cast; ring
  rw [this, Complex.re_ofReal_mul]
end ReciprocityTheory.ChartRestriction.DS.S7.IdB
