-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.toFS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:34:57.550607+00:00
-- url     : https://prove2.me/submissions/71bd516b-1330-4f93-be3f-8e1c7a28446c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace PI.UnitaryGroupMassFormula.UsCompose
theorem _root_.solution {k j ρ o κ : ℕ} {Θ : DiffOp k (j + ρ) Wp Wq} (h : InDD k j ρ o κ Θ) :
    ∃ L : FS k (j + ρ), Bd k j ρ κ o L ∧ ∀ H g, opApply Θ H g = shape k j ρ H L g := by
  induction Θ with
  | nil => exact ⟨[], fun e he => by simp at he, fun H g => by simp [opApply, shape]⟩
  | cons T Θ ih =>
    obtain ⟨L, hL, hEq⟩ := ih (fun T' hT' => h T' (List.mem_cons_of_mem _ hT'))
    obtain ⟨hlen, P, a, b, ⟨q, hq, hPq⟩, hc⟩ := h T (by simp)
    refine ⟨((q, a, b), T.word) :: L, ?_, ?_⟩
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact ⟨hq, hlen, T.word_lie⟩
      · exact hL e he
    · intro H g
      have e1 : opApply (T :: Θ) H g = T.coef g (Rw T.word H g) + opApply Θ H g := by
        simp [opApply]
      rw [e1, hEq H g, hc g]
      simp only [shape, List.map_cons, List.sum_cons, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply]
      congr 1
      rw [hPq g]
      rfl
end PI.UnitaryGroupMassFormula.UsCompose
