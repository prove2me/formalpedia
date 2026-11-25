-- Prove2me | solution 1 for PI.AmpRootJacW.hSh_dep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:03.653011+00:00
-- url     : https://prove2.me/submissions/a8c30130-975c-4094-b746-f418bc8adc29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupJacobian_SUpPowEqZero
import Theorems.Thm_PI_AmpRootJacW_sUp_neg
import Theorems.Thm_PI_AmpRootJacW_pow_apply_eq_of_agree
import Theorems.Thm_PI_AmpRootJacW_sUp_vM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.AmpRootJacW
variable {n : ℕ}
variable (S : Finset (Fin n × Fin n))
namespace PI.AmpRootJacW
theorem _root_.solution (hS : ∀ q ∈ S, q.1 < q.2) (q : S) (v w : S → ℂ) (h : ∀ p, rk S p < rk S q → v p = w p) :
    hSh S q v = hSh S q w := by
  unfold hSh
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hq : q.1.1 < q.1.2 := hS q.1 q.2
  rw [Fin.lt_def] at hq
  have hr : rk S q = q.1.2.val - q.1.1.val := rfl
  refine pow_apply_eq_of_agree (sUp_neg (sUp_vM S hS v)) (sUp_neg (sUp_vM S hS w)) (rk S q) ?_ m q.1.1 q.1.2 ?_
  · intro a b hab
    simp only [Matrix.neg_apply, vM]
    split_ifs with hm
    · rw [h ⟨(a, b), hm⟩ ?_]
      show b.val - a.val < rk S q
      rw [hr] at hab ⊢
      omega
    · rfl
  · rw [hr]
    omega
end PI.AmpRootJacW
