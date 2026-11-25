-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.inN_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:32.598362+00:00
-- url     : https://prove2.me/submissions/b92f9e72-80bc-4585-ae71-afcec041a824

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_hJ_mulVec
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_fix_span
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_conj_sub_one
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable {n r : ℕ}
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ}
    {h h' x : Matrix (Fin n) (Fin n) ℂ} (hU : Formalism.REAL.inUJ ε h) (hh : h * h' = 1) (hh' : h' * h = 1)
    (he : ∀ a, h *ᵥ e a = e a) (hz : h *ᵥ z = z) (hx : InN ε e z x) : InN ε e z (h * x * h') := by
  have hfix : ∀ (a : ℕ), ∀ v ∈ spanLt e a, h *ᵥ v = v := fun a =>
    fix_span (fun v hv => by obtain ⟨b, _, rfl⟩ := hv; exact he b)
  have h'e : ∀ v, h *ᵥ v = v → h' *ᵥ v = v := fun v hv => by
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, hh', Matrix.one_mulVec]
  have key : ∀ v, (h * x * h' - 1) *ᵥ v = h *ᵥ ((x - 1) *ᵥ (h' *ᵥ v)) := fun v => by
    rw [conj_sub_one hh]
    simp only [Matrix.mulVec_mulVec, mul_assoc]
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [key, h'e _ (he a), hfix a.1 _ (hx.1.1 a)]
    exact hx.1.1 a
  · rw [key, h'e _ hz, hfix r _ hx.1.2]
    exact hx.1.2
  · have hy' : ∀ a, hJ ε (e a) (h' *ᵥ y) = 0 := fun a => by
      rw [← hJ_mulVec hU, he a, Matrix.mulVec_mulVec, hh, Matrix.one_mulVec]
      exact hy a
    rw [key, hfix r _ (hx.2 _ hy')]
    exact hx.2 _ hy'
end PI.ScMuExists.UnitaryGroupMassFormula
