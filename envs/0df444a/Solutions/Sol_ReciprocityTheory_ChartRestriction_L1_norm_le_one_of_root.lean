-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.norm_le_one_of_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:54:04.776263+00:00
-- url     : https://prove2.me/submissions/dbe93393-141e-4e31-89d2-6ac9fd9e1aee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_Interface
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_IsIntegralOfRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormLeOneOfIntegralInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {l : ℕ} [Fact l.Prime] {x : ℂ_[l]} (P : Polynomial ℤ) (hm : P.Monic)
    (h : P.eval₂ (Int.castRingHom ℂ_[l]) x = 0) : ‖x‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  have hsum := hm.as_sum
  rw [hsum] at h
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at h
  have hx1 : (1 : ℝ) ≤ ‖x‖ := hlt.le
  have hn0 : P.natDegree ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  have hbound : ‖∑ i ∈ Finset.range P.natDegree, (Int.castRingHom ℂ_[l]) (P.coeff i) * x ^ i‖ ≤
      ‖x‖ ^ (P.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow]
    have hc : ‖(Int.castRingHom ℂ_[l]) (P.coeff i)‖ ≤ 1 := by
      rw [eq_intCast (Int.castRingHom ℂ_[l])]
      exact IsUltrametricDist.norm_intCast_le_one _ _
    calc ‖(Int.castRingHom ℂ_[l]) (P.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (P.natDegree - 1) :=
          mul_le_mul hc (pow_le_pow_right₀ hx1 (by omega)) (by positivity) zero_le_one
      _ = ‖x‖ ^ (P.natDegree - 1) := one_mul _
  have heq := eq_neg_of_add_eq_zero_left h
  have h1 : ‖x‖ ^ P.natDegree ≤ ‖x‖ ^ (P.natDegree - 1) := by
    rw [← norm_pow, heq, norm_neg]
    exact hbound
  have h2 : ‖x‖ ^ (P.natDegree - 1) < ‖x‖ ^ P.natDegree := pow_lt_pow_right₀ hlt (by omega)
  linarith
end ReciprocityTheory.ChartRestriction.L1
