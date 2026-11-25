-- Prove2me | solution 1 for PI.WGL.BrInt.normFock_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:10:55.495978+00:00
-- url     : https://prove2.me/submissions/3471f98f-b197-48b4-810e-28fd506e9822

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
private theorem fockF_eq_sum_lemma {σ : Type*} (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    fockF f g = ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  apply Finset.sum_subset hS
  intro m _ hm
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  simp [h0]
private theorem fockF_swap_eq_star {σ : Type*} [DecidableEq σ] (f g : MvPolynomial σ ℂ) :
    fockF g f = star (fockF f g) := by
  classical
  rw [fockF_eq_sum_lemma g f (f.support ∪ g.support) Finset.subset_union_right,
    fockF_eq_sum_lemma f g (f.support ∪ g.support) Finset.subset_union_left, star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [star_mul', star_star, star_natCast]
  ring
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
theorem _root_.solution {N : ℕ} (lam : DomWeight N) (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam g f = star (normFock lam f g) := by
  unfold normFock
  rw [star_div₀, ← fockF_swap_eq_star f g, ← fockF_swap_eq_star (extremal ℂ N lam) (extremal ℂ N lam)]
end PI.WGL.BrInt
