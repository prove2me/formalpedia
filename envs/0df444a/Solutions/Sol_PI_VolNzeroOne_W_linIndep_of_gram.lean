-- Prove2me | solution 1 for PI.VolNzeroOne.W.linIndep_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:56:07.531796+00:00
-- url     : https://prove2.me/submissions/509db7a1-0a0f-439d-96a5-22ac347021c3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolNzeroOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NilpotentVolumeOne_LinearIndependentFrameWithNormal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolNzeroOne PI.VolNzeroOne.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace PI.VolNzeroOne.W
theorem _root_.solution {n M : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) (h : (gramE σ J X).det ≠ 0) : LinearIndependent E X := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have key : ∀ a, ∑ b, gramE σ J X a b * c b = hE σ J (X a) (∑ b, c b • X b) := by
    intro a
    simp only [gramE, hE, Formalism.UG.hform, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hG : Matrix.mulVec (gramE σ J X) c = 0 := by
    funext a
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [key, hc]
    simp [hE, Formalism.UG.hform]
  have hc0 := Matrix.eq_zero_of_mulVec_eq_zero h hG
  intro i
  exact congrFun hc0 i
end PI.VolNzeroOne.W
