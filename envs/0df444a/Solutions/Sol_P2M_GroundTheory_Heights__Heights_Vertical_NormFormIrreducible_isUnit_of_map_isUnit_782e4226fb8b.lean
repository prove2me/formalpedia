-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_isUnit_of_map_isUnit_782e4226fb8b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:23:20.018731+00:00
-- url     : https://prove2.me/submissions/759ff2fd-6a3a-40b6-8bdc-9287fede6f63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial TensorProduct Matrix
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
open GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
variable {E L K : Type*} [Field E] [Field L] [Field K] [Algebra E L] [Algebra E K] {n : ℕ}
  {x : Fin n → L} {t : Fin n → E}
namespace GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
theorem _root_.solution {p : MvPolynomial (Fin n) E} (h : IsUnit (p.map (algebraMap E K))) :
    IsUnit p := by
  obtain ⟨r, hr, hpr⟩ := isUnit_iff_eq_C_of_isReduced.mp h
  have hc : ∀ m, m ≠ 0 → p.coeff m = 0 := fun m hm => by
    have := congrArg (coeff m) hpr
    rw [coeff_map, coeff_C, if_neg (Ne.symm hm)] at this
    exact (algebraMap E K).injective (by rw [this, map_zero])
  have hp : p = C (p.coeff 0) := by
    ext m
    rw [coeff_C]
    split_ifs with h0
    · rw [h0]
    · exact hc m (Ne.symm h0)
  have h0 : p.coeff 0 ≠ 0 := by
    intro h0
    have := congrArg (coeff 0) hpr
    rw [coeff_map, h0, map_zero, coeff_C, if_pos rfl] at this
    exact hr.ne_zero this.symm
  rw [hp]
  exact (Ne.isUnit h0).map C
end GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
