-- Prove2me | solution 1 for PI.FJMB.hwb_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:45:56.998983+00:00
-- url     : https://prove2.me/submissions/9c5b8010-9538-496a-8cfb-2364ab68a6a3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Theorems.Thm_PI_FJMB_pderiv_aeval_killS
import Theorems.Thm_PI_FJMB_edge_succ_succ
import Theorems.Thm_PI_FJMB_bCol_apply
import Theorems.Thm_PI_FJMB_bRow_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}
variable {m n : ℕ} (ι : Fin (m + 1) × Fin (n + 1) → σ) (hι : Function.Injective ι)
include hι
namespace PI.FJMB
theorem _root_.solution (f : MvPolynomial σ ℂ) (hf : HWB ι f) :
    HWB (fun x : Fin m × Fin n => ι (x.1.succ, x.2.succ)) (aeval (killS (edge ι)) f) := by
  constructor
  · intro a b hab
    rw [bRow_apply]
    have h0 := congrArg (aeval (killS (edge ι))) (hf.1 a.succ b.succ (Fin.succ_lt_succ_iff.2 hab))
    rw [bRow_apply, map_zero, map_sum, Fin.sum_univ_succ] at h0
    have e0 : ι (a.succ, 0) ∈ edge ι := Or.inr ⟨a, rfl⟩
    simp only [map_mul, aeval_X, killS, e0, if_true, zero_mul, zero_add] at h0
    rw [← h0]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [pderiv_aeval_killS _ _ (edge_succ_succ ι hι b k)]
    simp [edge_succ_succ ι hι a k]
  · intro c d hcd
    rw [bCol_apply]
    have h0 := congrArg (aeval (killS (edge ι))) (hf.2 c.succ d.succ (Fin.succ_lt_succ_iff.2 hcd))
    rw [bCol_apply, map_zero, map_sum, Fin.sum_univ_succ] at h0
    have e0 : ι (0, c.succ) ∈ edge ι := Or.inl ⟨c, rfl⟩
    simp only [map_mul, aeval_X, killS, e0, if_true, zero_mul, zero_add] at h0
    rw [← h0]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [pderiv_aeval_killS _ _ (edge_succ_succ ι hι i d)]
    simp [edge_succ_succ ι hι i c]
end PI.FJMB
