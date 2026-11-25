-- Prove2me | solution 1 for PI.OddDualWeyl.Red.rowAct_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:58:51.61103+00:00
-- url     : https://prove2.me/submissions/07a447b6-a46c-41f0-a98a-0d7b6e964f4f

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
theorem _root_.solution (g : Matrix (Fin k) (Fin k) R) {p : MvPolynomial (Fin k × Fin k) R} {D : ℕ}
    (hp : p.IsHomogeneous D) : (rowAct R g p).IsHomogeneous D := by
  classical
  have hL : ∀ v : Fin k × Fin k,
      (∑ b : Fin k, C (g v.1 b) * X (b, v.2) : MvPolynomial (Fin k × Fin k) R).IsHomogeneous 1 := by
    intro v
    apply IsHomogeneous.sum
    intro b _
    have hC : IsHomogeneous (C (g v.1 b) : MvPolynomial (Fin k × Fin k) R) 0 := by
      first | exact isHomogeneous_C _ _ | exact isHomogeneous_C _
    have hX : IsHomogeneous (X (b, v.2) : MvPolynomial (Fin k × Fin k) R) 1 := by
      first | exact isHomogeneous_X _ _ | exact isHomogeneous_X _
    have h1 := hC.mul hX
    rwa [zero_add] at h1
  rw [p.as_sum, _root_.map_sum]
  apply IsHomogeneous.sum
  intro m hm
  have hsum := sum_support_eq_degree_of_isHomogeneous' hp hm
  have hmon : PI.OddDualWeyl.rowAct R g (monomial m (coeff m p)) =
      C (coeff m p) * ∏ i ∈ m.support, (∑ b : Fin k, C (g i.1 b) * X (b, i.2)) ^ m i := by
    rw [PI.OddDualWeyl.rowAct, aeval_monomial, algebraMap_eq, Finsupp.prod]
  rw [hmon]
  have hC : IsHomogeneous (C (coeff m p) : MvPolynomial (Fin k × Fin k) R) 0 := by
    first | exact isHomogeneous_C _ _ | exact isHomogeneous_C _
  have hprod := IsHomogeneous.prod m.support (fun i => (∑ b : Fin k, C (g i.1 b) * X (b, i.2)) ^ m i)
    (fun i => 1 * m i) (fun i _ => (hL i).pow (m i))
  have h2 := hC.mul hprod
  have hdeg : 0 + ∑ i ∈ m.support, 1 * m i = D := by simp [hsum]
  rw [hdeg] at h2
  exact h2
end PI.OddDualWeyl.Red
