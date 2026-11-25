-- Prove2me | solution 1 for PI.ZuckTensorWork.compact_dominant_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:16:27.560785+00:00
-- url     : https://prove2.me/submissions/4db297b9-7bc1-424b-8a19-538725cea8b5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_RevNum
import Theorems.Thm_PI_ZuckTensorWork_Cj_mk_un
import Theorems.Thm_PI_ZuckTensorWork_Cj_un_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.ZuckTensorWork.Cj.mk_un
attribute [local simp] PI.ZuckTensorWork.Cj.un_mk


section
open Matrix Finset
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
variable {n : ℕ}
private lemma revNum_single (s x : Fin n) :
    (Pi.single (Fin.rev s) (1 : ℝ) : Fin n → ℝ) x = (Pi.single s (1 : ℝ) : Fin n → ℝ) (Fin.rev x) := by
  simp only [Pi.single_apply, Fin.rev_eq_iff]
end PI.ZuckTensorWork
end
end

set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
variable {n : ℕ}
namespace PI.ZuckTensorWork
theorem _root_.solution : CDomRev := by
  intro n ε μ Λ ⟨c, hc, hsum⟩
  refine ⟨fun a b => c (Fin.rev b) (Fin.rev a), fun a b h => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hc _ _ h
    exact ⟨Fin.rev_lt_rev.mp h1, h2.symm⟩
  · funext x
    have key : ∀ a b : Fin n, root (Fin.rev b) (Fin.rev a) x = - root a b (Fin.rev x) := by
      intro a b
      simp only [root, Pi.sub_apply, revNum_single]
      ring
    have hx := congrFun hsum (Fin.rev x)
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx
    have re : (∑ a : Fin n, ∑ b : Fin n, (c (Fin.rev b) (Fin.rev a) : ℝ) * root a b x) =
        ∑ a : Fin n, ∑ b : Fin n, (c a b : ℝ) * root (Fin.rev b) (Fin.rev a) x := by
      rw [Finset.sum_comm]
      refine Fintype.sum_equiv Fin.revPerm _ _ (fun b => ?_)
      refine Fintype.sum_equiv Fin.revPerm _ _ (fun a => ?_)
      simp only [Fin.revPerm_apply, Fin.rev_rev]
    simp only [Pi.sub_apply, revP, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [re]
    simp only [key, mul_neg, Finset.sum_neg_distrib, ← hx]
    ring
end PI.ZuckTensorWork
