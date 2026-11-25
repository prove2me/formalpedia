-- Prove2me | solution 1 for PIW.AdelClassFin.dual_denominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:43:35.271316+00:00
-- url     : https://prove2.me/submissions/bc126ac9-34f9-4ee8-ab25-c7797ec70cc4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StrongApproximation_DedekindLFunctions
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Theorems.Thm_PIW_AdelClassFin_DictRing_af_denom
import Theorems.Thm_PIW_AdelClassFin_DictRing_tmul_mem
import Theorems.Thm_PIW_AdelClassFin_DictRing_e_denom

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
open Formalism.MainNotions.S PI.AdelClassFin NumberField IsDedekindDomain
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
theorem _root_.solution : DDenom := by
  intro F E _ _ _ _ _ r
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [mul_zero]; exact zero_mem _⟩
  | tmul e a =>
    obtain ⟨m₁, hm₁, he⟩ := DictRing.e_denom e
    obtain ⟨m₂, hm₂, ha⟩ := DictRing.af_denom a
    refine ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, ?_⟩
    have hc : ((m₁ * m₂ : ℕ) : E ⊗[F] Af F) = (m₁ : E) ⊗ₜ[F] (m₂ : Af F) := by
      rw [Nat.cast_mul, Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.natCast_def',
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hc, Algebra.TensorProduct.tmul_mul_tmul]
    exact DictRing.tmul_mem he ha
  | add x y hx hy =>
    obtain ⟨m₁, hm₁, h₁⟩ := hx
    obtain ⟨m₂, hm₂, h₂⟩ := hy
    refine ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, ?_⟩
    have e : ((m₁ * m₂ : ℕ) : E ⊗[F] Af F) * (x + y) =
        (m₂ : E ⊗[F] Af F) * ((m₁ : E ⊗[F] Af F) * x) + (m₁ : E ⊗[F] Af F) * ((m₂ : E ⊗[F] Af F) * y) := by
      push_cast; ring
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ _) h₁) (mul_mem (natCast_mem _ _) h₂)
end PIW.AdelClassFin
