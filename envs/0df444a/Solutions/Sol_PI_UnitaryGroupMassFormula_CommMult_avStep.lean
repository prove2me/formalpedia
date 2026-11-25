-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CommMult.avStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:44:30.083335+00:00
-- url     : https://prove2.me/submissions/739fc14d-6464-4dbe-bdc2-f35f8cf02f30

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_SchurStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_IntegrableEntry
import Theorems.Thm_PI_UnitaryGroupMassFormula_CommMult_mul_mInt
import Theorems.Thm_PI_UnitaryGroupMassFormula_CommMult_mInt_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_CommMult_mInt_const
import Theorems.Thm_PI_UnitaryGroupMassFormula_CommMult_mInt_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CommMult
open MeasureTheory Matrix
namespace PI.UnitaryGroupMassFormula.CommMult
theorem _root_.solution : AvStep := by
  intro H _ _ _ _ _ N M π σ hπ hσ T X hT hXT
  let _ : MeasurableSpace H := borel H
  have : BorelSpace H := ⟨rfl⟩
  set μ : Measure H := Measure.haar with hμ
  set F : H → Matrix (Fin M) (Fin N) ℂ := fun h =>
    ((σ h : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) * X *
      ((π h⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) with hFdef
  have hπi : Continuous (fun h : H => ((π h⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) :=
    (show Continuous (fun g : H => ((π g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) from hπ).comp
      continuous_inv
  have hF : Continuous F :=
    ((show Continuous (fun g : H => ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ)) from
      hσ).matrix_mul continuous_const).matrix_mul hπi
  set S₀ := mInt μ F with hS₀
  have hequi : ∀ g, ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) * S₀ =
      S₀ * ((π g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := by
    intro g
    have hFg : Continuous (fun h => F (g * h)) := hF.comp (continuous_const.mul continuous_id)
    have hpt : (fun h => ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) * F h) =
        (fun h => F (g * h) * ((π g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) := by
      funext h
      simp only [hFdef, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ), ← Units.val_mul,
        ← map_mul, ← Units.val_mul (π (g * h)⁻¹), ← map_mul, _root_.mul_inv_rev, inv_mul_cancel_right]
    rw [hS₀, mul_mInt μ _ hF, hpt, ← mInt_mul μ hFg, mInt_left μ F g]
  have hST : S₀ * T = μ.real Set.univ • (1 : Matrix (Fin M) (Fin M) ℂ) := by
    have hpt : (fun h => F h * T) = (fun _ => (1 : Matrix (Fin M) (Fin M) ℂ)) := by
      funext h
      simp only [hFdef]
      rw [Matrix.mul_assoc, hT h⁻¹, ← Matrix.mul_assoc, Matrix.mul_assoc _ X T,
        hXT, Matrix.mul_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    rw [hS₀, mInt_mul μ hF, hpt, mInt_const]
  have hc : 0 < μ.real Set.univ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (isOpen_univ.measure_pos μ Set.univ_nonempty).ne'
      (measure_ne_top μ _)
  refine ⟨(μ.real Set.univ)⁻¹ • S₀, fun g => ?_, ?_⟩
  · rw [Matrix.mul_smul, hequi g, Matrix.smul_mul]
  · rw [Matrix.smul_mul, hST, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
end PI.UnitaryGroupMassFormula.CommMult
