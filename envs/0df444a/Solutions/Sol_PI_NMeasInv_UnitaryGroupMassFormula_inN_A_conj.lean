-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.inN_A_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:24:52.527301+00:00
-- url     : https://prove2.me/submissions/62f4c35f-73d5-4ab4-8be6-c68bf84ad75a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Alin_apply
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Amat_mulVec
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_e_A
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_A_inv
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_A_e
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_A_orth
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_A_spanLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
variable {n r : ℕ} (ε : Fin n → Bool)
variable {ε} {e f : Fin r → Fin n → ℂ}
variable (hG : Gram ε e f)
include hG
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (s : Fin r → ℝ) (hs : ∀ b, s b ≠ 0) {z : Fin n → ℂ} (hez : ∀ a, hJ ε (e a) z = 0)
    (hfz : ∀ a, hJ ε (f a) z = 0) {g : Matrix (Fin n) (Fin n) ℂ} (hg : InN ε e z g) :
    InN ε e z (Amat ε e f s * g * Amat ε e f s⁻¹) := by
  have hconj : ∀ v, (Amat ε e f s * g * Amat ε e f s⁻¹ - 1) *ᵥ v =
      Afun ε e f s ((g - 1) *ᵥ Afun ε e f s⁻¹ v) := fun v => by
    have e1 : Afun ε e f s ((g - 1) *ᵥ Afun ε e f s⁻¹ v) =
        Afun ε e f s (g *ᵥ Afun ε e f s⁻¹ v) - v := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Alin_apply (s := s), map_sub, Alin_apply,
        Alin_apply, A_inv hG s hs]
    rw [e1, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Amat_mulVec, Amat_mulVec]
  obtain ⟨⟨hSe, hSz⟩, hN⟩ := hg
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [hconj, A_e hG s⁻¹ a, Matrix.mulVec_smul]
    exact A_spanLt hG s _ (Submodule.smul_mem _ _ (hSe a))
  · rw [hconj, A_orth hG s⁻¹ z hez hfz]
    exact A_spanLt hG s _ hSz
  · rw [hconj]
    apply A_spanLt hG s
    apply hN
    intro b
    rw [e_A hG, hy b, mul_zero]
end PI.NMeasInv.UnitaryGroupMassFormula
