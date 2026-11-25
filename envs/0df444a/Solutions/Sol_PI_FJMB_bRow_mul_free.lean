-- Prove2me | solution 1 for PI.FJMB.bRow_mul_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:38:21.756473+00:00
-- url     : https://prove2.me/submissions/98d743f4-6e59-40ee-a9a6-075b8cb9899b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurDiag
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurCauchy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPolynomial Classical
namespace PI.FJMB
variable {σ : Type*}
private theorem pderiv_eq_zero_of_forall_support_apply_eq_zero {v : σ} {Q : MvPolynomial σ ℂ} (h : ∀ e ∈ Q.support, e v = 0) :
    pderiv v Q = 0 := by
  conv_lhs => rw [Q.as_sum]
  rw [map_sum]
  refine Finset.sum_eq_zero fun e he => ?_
  simp [pderiv_monomial, h e he]
end PI.FJMB
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}
namespace PI.FJMB
theorem _root_.solution {m n : ℕ} (ι : Fin m × Fin n → σ) (a b : Fin m) (S Q : MvPolynomial σ ℂ)
    (hQ : ∀ e ∈ Q.support, ∀ x, e (ι x) = 0) : PI.FJM.bRow ι a b (S * Q) = PI.FJM.bRow ι a b S * Q := by
  show (∑ k : Fin n, LinearMap.mulLeft ℂ (X (ι (a, k))) * (pderiv (ι (b, k))).toLinearMap : Module.End ℂ (MvPolynomial σ ℂ)) (S * Q) =
    (∑ k : Fin n, LinearMap.mulLeft ℂ (X (ι (a, k))) * (pderiv (ι (b, k))).toLinearMap : Module.End ℂ (MvPolynomial σ ℂ)) S * Q
  rw [LinearMap.sum_apply, LinearMap.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  change X (ι (a, k)) * pderiv (ι (b, k)) (S * Q) = X (ι (a, k)) * pderiv (ι (b, k)) S * Q
  have hl := (pderiv (ι (b, k))).leibniz S Q
  rw [pderiv_eq_zero_of_forall_support_apply_eq_zero fun e he => hQ e he (b, k), smul_zero, zero_add, smul_eq_mul] at hl
  rw [hl]
  ring
end PI.FJMB
