-- Prove2me | solution 1 for PI.OddDualWeyl.Red.aeval_mul_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:59:19.080816+00:00
-- url     : https://prove2.me/submissions/6acf1470-1357-463f-8ae5-9f6baf50e2f4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial Matrix
noncomputable section
namespace PI.OddDualWeyl.Red
variable {R : Type*} [CommRing R] {k : ℕ}
private theorem sum_support_eq_degree_of_isHomogeneous' {σ : Type*} {p : MvPolynomial σ R} {D : ℕ} (hp : p.IsHomogeneous D)
    {m : σ →₀ ℕ} (hm : m ∈ p.support) : ∑ i ∈ m.support, m i = D := by
  have h1 := hp (MvPolynomial.mem_support_iff.mp hm)
  first
  | simpa [Finsupp.weight_apply, Finsupp.sum] using h1
  | simpa [Finsupp.degree] using h1
  | (rw [← h1]; simp [Finsupp.weight_apply, Finsupp.sum])
  | (rw [← h1]; simp [Finsupp.degree, Finsupp.weight_apply, Finsupp.sum])
  | (simp only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] at h1; exact h1)
section Field
variable {K : Type*} [Field K] {k : ℕ}
end Field
end PI.OddDualWeyl.Red
namespace PI.OddDualWeyl
open Red
end PI.OddDualWeyl
end
end

set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.Red
variable {R : Type*} [CommRing R] {k : ℕ}
namespace PI.OddDualWeyl.Red
theorem _root_.solution {σ S : Type*} [CommRing S] [Algebra R S] (b : σ → S) (c : S)
    {p : MvPolynomial σ R} {D : ℕ} (hp : p.IsHomogeneous D) :
    aeval (fun v => c * b v) p = c ^ D * aeval b p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [_root_.map_sum, _root_.map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hsum := sum_support_eq_degree_of_isHomogeneous' hp hm
  have hc : ∏ i ∈ m.support, c ^ m i = c ^ D := by
    rw [Finset.prod_pow_eq_pow_sum, hsum]
  rw [aeval_monomial, aeval_monomial]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, hc]
  ring
end PI.OddDualWeyl.Red
