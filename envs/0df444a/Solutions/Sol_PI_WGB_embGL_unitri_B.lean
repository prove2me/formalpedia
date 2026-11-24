-- Prove2me | solution 1 for PI.WGB.embGL_unitri_B
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:46.507833+00:00
-- url     : https://prove2.me/submissions/777d55d4-e556-47b6-a9fd-06554140371c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB
import Theorems.Thm_PI_WGB_embGL_apply_B


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGB
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) (u : GL (Fin n) ℂ) (hl : ∀ i j, j < i → u i j = 0)
    (hd : ∀ i, u i i = 1) :
    (∀ a, ((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) a a = 1) ∧
    (∀ a b, a ≠ b → ((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) b a ≠ 0 →
      prowB n N a < prowB n N b) ∧
    (∀ a b, a < b → ((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) b a = 0) := by
  refine ⟨fun a => ?_, fun a b hab hne => ?_, fun a b hab => ?_⟩
  · rw [embGL_apply_B]
    by_cases ha : a.1 < n
    · rw [dif_pos ha, dif_pos ha]; exact hd _
    · rw [dif_neg ha, if_neg ha]
  · have ha2 := a.2
    have hb2 := b.2
    rw [embGL_apply_B] at hne
    by_cases hb : b.1 < n <;> by_cases ha : a.1 < n
    · rw [dif_pos hb, dif_pos ha] at hne
      have hba : ¬ (a.1 < b.1) := fun hlt => hne (hl _ _ (Fin.mk_lt_mk.mpr hlt))
      have hne' : a.1 ≠ b.1 := fun e => hab (Fin.ext e)
      unfold prowB
      rw [if_pos ha, if_pos hb]
      omega
    · rw [dif_pos hb, dif_neg ha] at hne; exact absurd rfl hne
    · rw [dif_neg hb, if_pos ha] at hne; exact absurd rfl hne
    · exact absurd (Fin.ext (by omega)) hab
  · have ha2 := a.2
    have hb2 := b.2
    rw [embGL_apply_B]
    by_cases hb : b.1 < n <;> by_cases ha : a.1 < n
    · rw [dif_pos hb, dif_pos ha]
      exact hl _ _ (Fin.mk_lt_mk.mpr (Fin.lt_def.mp hab))
    · exact absurd (lt_trans (Fin.lt_def.mp hab) hb) ha
    · rw [dif_neg hb, if_pos ha]
    · have := Fin.lt_def.mp hab
      omega
end PI.WGB
