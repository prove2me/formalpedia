-- Prove2me | solution 1 for PI.WGL.BrInt.brFockF_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:05.791961+00:00
-- url     : https://prove2.me/submissions/7bd96aa0-6347-41e5-a1a8-98a2558b0d6c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ConstructionBrInt
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
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
private theorem fockF_eq_sum_of_support_subset (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    fockF f g = ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  apply Finset.sum_subset hS
  intro m _ hm
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  simp [h0]
end fock
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
variable {σ : Type}
namespace PI.WGL.BrInt
theorem _root_.solution (f g : MvPolynomial σ ℚ) :
    fockF (map (algebraMap ℚ ℂ) f) (map (algebraMap ℚ ℂ) g) = ((fockQ f g : ℚ) : ℂ) := by
  rw [fockF_eq_sum_of_support_subset _ _ f.support (MvPolynomial.support_map_subset _ _)]
  unfold fockQ
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [MvPolynomial.coeff_map]
end PI.WGL.BrInt
