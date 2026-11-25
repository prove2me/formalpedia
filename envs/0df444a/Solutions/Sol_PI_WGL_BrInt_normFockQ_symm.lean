-- Prove2me | solution 1 for PI.WGL.BrInt.normFockQ_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:09:02.817905+00:00
-- url     : https://prove2.me/submissions/97587f3a-2f4a-4f7e-a624-2c2d92c79233

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ConstructionBrInt
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
namespace PI.WGL
open Formalism.BasicNotions MvPolynomial
namespace BrInt
open Formalism.REAL Formalism.GradedWeylDivisibility
section fock
variable {σ : Type}
end fock
private theorem fockQ_eq_sum_of_support_subset {σ : Type*} (f g : MvPolynomial σ ℚ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    fockQ f g = ∑ m ∈ S, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) := by
  unfold fockQ
  apply Finset.sum_subset hS
  intro m _ hm
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  simp [h0]
end BrInt
end PI.WGL
end
end

set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions MvPolynomial
open PI.WGL.BrInt
open Formalism.REAL Formalism.GradedWeylDivisibility
namespace PI.WGL.BrInt
theorem _root_.solution {N : ℕ} (lam : DomWeight N) (a b : MvPolynomial (Fin N × Fin N) ℚ) :
    normFockQ lam a b = normFockQ lam b a := by
  classical
  unfold normFockQ
  congr 1
  rw [fockQ_eq_sum_of_support_subset a b (a.support ∪ b.support) Finset.subset_union_left,
    fockQ_eq_sum_of_support_subset b a (a.support ∪ b.support) Finset.subset_union_right]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring
end PI.WGL.BrInt
