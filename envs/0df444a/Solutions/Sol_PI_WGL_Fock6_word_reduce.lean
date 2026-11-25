-- Prove2me | solution 1 for PI.WGL.Fock6.word_reduce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:01.344532+00:00
-- url     : https://prove2.me/submissions/c6512bf4-e798-4a70-9221-0f3fa4d8c977

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftFock
import Theorems.Thm_PI_WGL_Fock6_rowDiv_diag
import Theorems.Thm_PI_WGL_Fock6_word_homog
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



set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.REAL MvPolynomial
open PI.WGL.Fock6
namespace PI.WGL.Fock6
theorem _root_.solution {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hf : ∀ c : Fin r, ∃ H : ℤ, IsWeightedHomogeneous (rw1 c) f H) (w : List (Fin r × Fin r × ℕ)) :
    ∃ w', OffDiag w' ∧ ∃ z : ℂ, applyWord ℂ w f = z • applyWord ℂ w' f := by
  have hsm : ∀ (a b : Fin r) (k : ℕ) (z : ℂ) (g : MvPolynomial (Fin r × Fin n) ℂ),
      rowDiv ℂ a b k (z • g) = z • rowDiv ℂ a b k g := by
    intro a b k z g
    unfold rowDiv
    rw [map_smul, Polynomial.coeff_smul]
  induction w with
  | nil => exact ⟨[], fun x hx => by simp at hx, 1, by rw [one_smul]⟩
  | cons x w ih =>
    obtain ⟨w', hw', z, hz⟩ := ih
    obtain ⟨a, b, k⟩ := x
    by_cases hab : a = b
    · subst hab
      obtain ⟨H, hH⟩ := word_homog w' f hf a
      refine ⟨w', hw', z * ((H.toNat.choose k : ℕ) : ℂ), ?_⟩
      show rowDiv ℂ a a k (applyWord ℂ w f) = _
      rw [hz, hsm, rowDiv_diag a k _ H hH, smul_smul]
    · refine ⟨(a, b, k) :: w', ?_, z, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hab
        · exact hw' y hy
      · show rowDiv ℂ a b k (applyWord ℂ w f) = z • rowDiv ℂ a b k (applyWord ℂ w' f)
        rw [hz, hsm]
end PI.WGL.Fock6
