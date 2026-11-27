-- Prove2me | solution 1 for PIW.AdelClassFin.isImg_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:18:39.760326+00:00
-- url     : https://prove2.me/submissions/a8d0e11d-2f5a-4101-97b9-3816fdd628ae

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_IsImgTrans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ} {γ γ₀ : GL (Fin n) E}
    {M₀ M₁ M : Submodule (𝓞 E) (Fin n → E)} (h₁ : IsImg γ₀ M₀ M₁) (h : IsImg γ M₀ M) :
    IsImg (γ * γ₀⁻¹) M₁ M := by
  intro v
  constructor
  · intro hv
    obtain ⟨w0, hw0, rfl⟩ := (h v).1 hv
    refine ⟨(γ₀ : Matrix (Fin n) (Fin n) E) *ᵥ w0, (h₁ _).2 ⟨w0, hw0, rfl⟩, ?_⟩
    rw [Units.val_mul, Matrix.mulVec_mulVec, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      mul_one]
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨w0, hw0, rfl⟩ := (h₁ w).1 hw
    refine (h _).2 ⟨w0, hw0, ?_⟩
    rw [Units.val_mul, Matrix.mulVec_mulVec, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      mul_one]
end PIW.AdelClassFin
