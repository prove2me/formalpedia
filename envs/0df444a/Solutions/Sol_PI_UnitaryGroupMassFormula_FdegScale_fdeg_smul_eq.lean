-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FdegScale.fdeg_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:40:36.252801+00:00
-- url     : https://prove2.me/submissions/f4af4344-008c-4e2d-a5f9-7d20335585c6

import Definitions.Def_Formalism_PeriodIntegrals_FdegScale
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeScaling_FdegScaleOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FdegScale
open PI PI.UpqRep MeasureTheory Finset
open scoped InnerProductSpace
namespace PI.UnitaryGroupMassFormula.FdegScale
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [Nontrivial V] (μ : Measure (UJ ε)) (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (s : NNReal)
    (hs : 0 < s) (d₁ d : ℝ) (h₁ : IsFdeg μ σ d₁) (h₂ : IsFdeg ((s : ENNReal) • μ) σ d) :
    d = d₁ / (s : ℝ) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have e₁ := (h₁.2 x x x x).2
  have e₂ := (h₂.2 x x x x).2
  rw [integral_smul_measure, e₁, ENNReal.coe_toReal, Complex.real_smul] at e₂
  have hA : (⟪x, x⟫_ℂ) ≠ 0 := inner_self_ne_zero.mpr hx
  have hd₁ : (d₁ : ℂ) ≠ 0 := by exact_mod_cast h₁.1.ne'
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast h₂.1.ne'
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hsC : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsR
  have key : (d : ℂ) * ((s : ℝ) : ℂ) = d₁ := by
    field_simp at e₂
    linear_combination e₂
  have key' : d * (s : ℝ) = d₁ := by exact_mod_cast key
  field_simp
  exact key'
end PI.UnitaryGroupMassFormula.FdegScale
