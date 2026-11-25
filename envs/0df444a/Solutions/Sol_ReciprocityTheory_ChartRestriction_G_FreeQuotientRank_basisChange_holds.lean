-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.basisChange_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:06:56.204506+00:00
-- url     : https://prove2.me/submissions/70a26e26-d517-459e-a799-9f0b97deb8fa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_BasisChangePf_cb_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_BasisChangePf_cb_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_BasisChangePf_cb_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_BasisChangePf_cb_C_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_BasisChangePf_cb_lin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open BasisChangePf
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution : BasisChangeStatement := by
  intro K _ _ ι _ P d hP hP1 A C hC hA μ
  classical
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hL : ∀ i, CB (∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k : MvPolynomial ι K) C :=
    fun i => cb_lin A hC0 hA i
  have key : CB (MvPolynomial.bind₁ (fun i => ∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k) P) (C ^ d) := by
    conv => arg 1; rw [P.as_sum]
    rw [map_sum]
    refine cb_sum _ _ (pow_nonneg hC0 d) (fun v hv => ?_)
    rw [MvPolynomial.bind₁_monomial]
    have hdeg : v.degree = d := by
      rw [Finsupp.degree_eq_weight_one]
      exact hP (MvPolynomial.mem_support_iff.1 hv)
    have hprod : CB (∏ i ∈ v.support, (∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k) ^ v i)
        (∏ i ∈ v.support, C ^ v i) :=
      cb_prod _ _ _ (fun i => pow_nonneg hC0 _) (fun i _ => cb_pow hC0 (hL i) (v i))
    have hb := cb_C_mul (MvPolynomial.coeff v P) hprod
    have hpow : ∏ i ∈ v.support, C ^ v i = C ^ d := by
      rw [Finset.prod_pow_eq_pow_sum, ← hdeg]
      rfl
    intro ν
    calc ‖MvPolynomial.coeff ν (MvPolynomial.C (MvPolynomial.coeff v P) *
          ∏ i ∈ v.support, (∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k) ^ v i)‖
        ≤ ‖MvPolynomial.coeff v P‖ * ∏ i ∈ v.support, C ^ v i := hb ν
      _ ≤ 1 * C ^ d := by
          rw [hpow]
          exact mul_le_mul_of_nonneg_right (hP1 v) (pow_nonneg hC0 d)
      _ = C ^ d := one_mul _
  exact key μ
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
