-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GelfCpt.intMat_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:54:49.425819+00:00
-- url     : https://prove2.me/submissions/a0bf4db3-81b1-4b50-9ea4-36592e984cf3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_AvgStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_MulIntMatMul
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfCpt_integral_conj
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfCpt_mul_intMat_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GelfCpt
open MeasureTheory Matrix
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace PI.UnitaryGroupMassFormula.GelfCpt
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] {N : ℕ} (ρ : G →* GL (Fin N) ℂ)
    (hc : PI.UMultOne.Cont ρ) {f : G → ℂ} (hf : Continuous f) (h : G)
    (hA : ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * intMat μ ρ f =
      intMat μ ρ f * ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) (i j : Fin N) :
    ∫ g, f (h⁻¹ * g * h) * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ =
      intMat μ ρ f i j := by
  have hRmul : ∀ x y, ((ρ (x * y) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      ((ρ x : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
        ((ρ y : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := fun x y => by
    rw [map_mul, Units.val_mul]
  have e : ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * intMat μ ρ f *
      ((ρ h⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = intMat μ ρ f := by
    rw [hA, Matrix.mul_assoc, ← hRmul, mul_inv_cancel, map_one, Units.val_one, Matrix.mul_one]
  rw [← e, mul_intMat_mul μ ρ hc hf]
  refine (integral_conj μ (fun x => f (h⁻¹ * x * h) *
    ((ρ x : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j) h).symm.trans ?_
  congr 1
  funext g
  have hg : h⁻¹ * (h * g * h⁻¹) * h = g := by group
  simp only [hg, hRmul]
end PI.UnitaryGroupMassFormula.GelfCpt
