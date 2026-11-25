-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CapelliEig.Hecke_multiplication
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:32:09.782091+00:00
-- url     : https://prove2.me/submissions/cee61ea5-1b17-4b80-812d-facfe403428d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_SmRight
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_inUJ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PI.UpqRep
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CapelliEig
namespace PI.UnitaryGroupMassFormula.CapelliEig
theorem _root_.solution : MulH := by
  intro k r ε lam Hs _ _ σ hσ x hx y hy
  obtain ⟨P₀, ⟨⟨hunit, hcay⟩, _⟩, hds⟩ := hσ
  have hdet : IsUnit P₀.det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hPQ : P₀ * P₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hQP : P₀⁻¹ * P₀ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hH : Formalism.QuantumDeterminants.Hpk k r = P₀ᴴ * Formalism.REAL.Jm ε * P₀ := hcay.symm
  have hx' : Formalism.REAL.inUJ ε (P₀ * x * P₀⁻¹) := Formalism.QuantumDeterminants.ioh_inUJ ε _ P₀ P₀⁻¹ x hPQ hH hx
  have hy' : Formalism.REAL.inUJ ε (P₀ * y * P₀⁻¹) := Formalism.QuantumDeterminants.ioh_inUJ ε _ P₀ P₀⁻¹ y hPQ hH hy
  have hm := hds.2.2.1.1.2 (P₀ * x * P₀⁻¹) hx' (P₀ * y * P₀⁻¹) hy'
  have e1 : P₀⁻¹ * (P₀ * x * P₀⁻¹ * (P₀ * y * P₀⁻¹)) * P₀ = x * y := by
    calc P₀⁻¹ * (P₀ * x * P₀⁻¹ * (P₀ * y * P₀⁻¹)) * P₀
        = (P₀⁻¹ * P₀) * x * (P₀⁻¹ * P₀) * y * (P₀⁻¹ * P₀) := by simp only [Matrix.mul_assoc]
      _ = x * y := by rw [hQP]; simp only [Matrix.one_mul, Matrix.mul_one]
  have e2 : ∀ z, P₀⁻¹ * (P₀ * z * P₀⁻¹) * P₀ = z := by
    intro z
    calc P₀⁻¹ * (P₀ * z * P₀⁻¹) * P₀ = (P₀⁻¹ * P₀) * z * (P₀⁻¹ * P₀) := by simp only [Matrix.mul_assoc]
      _ = z := by rw [hQP, Matrix.one_mul, Matrix.mul_one]
  simp only [e1, e2] at hm
  exact hm
end PI.UnitaryGroupMassFormula.CapelliEig
