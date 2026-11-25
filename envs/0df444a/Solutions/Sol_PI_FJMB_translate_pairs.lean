-- Prove2me | solution 1 for PI.FJMB.translate_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:03.517406+00:00
-- url     : https://prove2.me/submissions/1b071c69-e91e-4bb9-93e6-21dc2af084c7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurChain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
import Theorems.Thm_PI_FJMB_aeval_translate_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMB
variable {σ : Type*}
namespace PI.FJMB
theorem _root_.solution {R : Type*} [CommRing R] {κ : Type*} [Fintype κ] [DecidableEq σ] (u w : κ → σ)
    (_hw : Function.Injective w) (huw : ∀ k k', u k ≠ w k') (f : MvPolynomial σ R)
    (h : ∑ k, X (u k) * pderiv (w k) f = 0) {K : Type*} [Field K] [CharZero K] [Algebra R K] (y : σ → K) (t : K) :
    aeval (fun v => y v + t * ∑ k, if w k = v then y (u k) else 0) f = aeval y f := by
  classical
  refine aeval_translate_eq f (Finset.univ.image w) (fun v => ∑ k, if w k = v then X (u k) else 0) ?_ y
    (fun v => ∑ k, if w k = v then y (u k) else 0) ?_ ?_ t
  · calc ∑ v ∈ Finset.univ.image w, (∑ k, if w k = v then (X (u k) : MvPolynomial σ R) else 0) * pderiv v f
        = ∑ k, ∑ v ∈ Finset.univ.image w, if w k = v then X (u k) * pderiv v f else 0 := by
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun k _ => ?_); split_ifs <;> simp
      _ = ∑ k, X (u k) * pderiv (w k) f := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.sum_ite_eq]; simp
      _ = 0 := h
  · intro v hv
    refine Finset.sum_eq_zero (fun k _ => ?_)
    have : w k ≠ v := fun e => hv (by rw [← e]; exact Finset.mem_image_of_mem w (Finset.mem_univ k))
    simp [this]
  · intro v _
    have hz : ∀ k, (∑ k', if w k' = u k then (Polynomial.C (y (u k')) : Polynomial K) else 0) = 0 :=
      fun k => Finset.sum_eq_zero (fun k' _ => by simp [Ne.symm (huw k k')])
    simp only [map_sum, apply_ite (aeval _), aeval_X, map_zero, apply_ite Polynomial.C]
    simp only [hz, mul_zero, add_zero]
end PI.FJMB
