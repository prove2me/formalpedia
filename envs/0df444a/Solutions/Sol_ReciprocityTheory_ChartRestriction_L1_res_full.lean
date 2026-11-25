-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.res_full
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:47:22.00586+00:00
-- url     : https://prove2.me/submissions/706d3d9d-10a9-450c-ba52-89849a6b57cb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TchOfIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormEqOfNormSubLt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorRes
import Theorems.Thm_ReciprocityTheory_ChartRestriction_PadicPolynomialApproximation_monic_X_pow_add_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_PadicPolynomialApproximation_exists_nat_poly_near
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_tch_of_integral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_PadicPolynomialApproximation_exists_root_near


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve Polynomial
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (x : ℂ_[l]) (hx : ‖x‖ ≤ 1) : ∃ ξ ∈ Tch l, ‖x - ξ‖ < 1 := by
  obtain ⟨y, hy⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt x one_pos
  rw [dist_eq_norm] at hy
  have hy1 : ‖y‖ ≤ 1 := by
    rw [← PadicComplex.norm_extends]
    calc ‖(y : ℂ_[l])‖ = ‖x - (x - y)‖ := by rw [sub_sub_cancel]
      _ ≤ max ‖x‖ ‖x - y‖ := by
        have := IsUltrametricDist.norm_add_le_max x (-(x - (y : ℂ_[l])))
        rwa [← sub_eq_add_neg, norm_neg] at this
      _ ≤ 1 := max_le hx hy.le
  obtain ⟨d, c, hQ⟩ := ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.exists_nat_poly_near l y hy1
  set Q' : (Rmu l)[X] := X ^ d + ∑ i ∈ Finset.range d, C ((c i : ℕ) : Rmu l) * X ^ i with hQ'
  have hmon : Q'.Monic := ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.monic_X_pow_add_sum d (fun i => ((c i : ℕ) : Rmu l))
  have hmap : Q'.map (algebraMap (Rmu l) ℂ_[l]) =
      X ^ d + ∑ i ∈ Finset.range d, C ((c i : ℕ) : ℂ_[l]) * X ^ i := by
    rw [hQ', Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, map_natCast]
  obtain ⟨α, hroot, hα⟩ := ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.exists_root_near l
    (X ^ d + ∑ i ∈ Finset.range d, C ((c i : ℕ) : ℂ_[l]) * X ^ i)
    (by rw [← hmap]; exact hmon.map _) (y : ℂ_[l]) hQ
  have hint : IsIntegral (Rmu l) α := ⟨Q', hmon, by rw [eval₂_eq_eval_map, hmap]; exact hroot⟩
  obtain ⟨ξ, hξ, hξα⟩ := tch_of_integral l α hint
  refine ⟨ξ, hξ, ?_⟩
  have e : x - ξ = (x - y) + ((y - α) + (α - ξ)) := by ring
  rw [e]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hy ?_)
  exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hα hξα)
end ReciprocityTheory.ChartRestriction.L1
