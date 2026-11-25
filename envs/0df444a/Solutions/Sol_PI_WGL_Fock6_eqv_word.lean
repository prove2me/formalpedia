-- Prove2me | solution 1 for PI.WGL.Fock6.eqv_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:08:46.318985+00:00
-- url     : https://prove2.me/submissions/1891a126-816c-48f9-b3d5-34803ac9801f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftFock
import Theorems.Thm_PI_WGL_Fock6_applyWord_cons
import Theorems.Thm_Formalism_GradedWeylDivisibility_applyWord_cons
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivStable
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



set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.REAL MvPolynomial
open PI.WGL.Fock6
namespace PI.WGL.Fock6
theorem _root_.solution (hD : EqvDiv) {n N : ℕ} (h : n + 1 = N) (mu : DomWeight n) (lam : DomWeight N)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ)
    (w : List (Fin n × Fin n × ℕ)) (hw : OffDiag w) (s : MvPolynomial (Fin n × Fin n) ℂ)
    (hs : s ∈ nablaSq ℂ n mu) :
    applyWord ℂ w s ∈ nablaSq ℂ n mu ∧ φ (applyWord ℂ w s) = applyWord ℂ (liftWord h w) (φ s) := by
  induction w with
  | nil => exact ⟨hs, rfl⟩
  | cons x w ih =>
    have hx : x.1 ≠ x.2.1 := hw x (by simp)
    obtain ⟨hm, he⟩ := ih (fun y hy => hw y (by simp [hy]))
    refine ⟨?_, ?_⟩
    · rw [applyWord_cons]
      exact Formalism.GradedWeylDivisibility.rowDivStable ℂ n n mu.natW x.1 x.2.1 x.2.2 _ hm
    · rw [applyWord_cons, hD n N h mu lam φ hφ x.1 x.2.1 hx x.2.2 _ hm, he]
      rfl
end PI.WGL.Fock6
