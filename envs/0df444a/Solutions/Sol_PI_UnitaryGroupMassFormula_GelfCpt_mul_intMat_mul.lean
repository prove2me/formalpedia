-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GelfCpt.mul_intMat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:36.452792+00:00
-- url     : https://prove2.me/submissions/db3ce26b-3495-4127-a912-b35e2758bb61

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_AvgStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_MulIntMatMul
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfCpt_integrable_of_cont

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
theorem _root_.solution (μ : Measure G) [IsFiniteMeasure μ] {N : ℕ} (ρ : G →* GL (Fin N) ℂ)
    (hc : PI.UMultOne.Cont ρ) {f : G → ℂ} (hf : Continuous f) (M M' : Matrix (Fin N) (Fin N) ℂ)
    (i j : Fin N) :
    (M * intMat μ ρ f * M') i j =
      ∫ g, f g * (M * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * M') i j ∂μ := by
  have hR : ∀ k l, Continuous fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) k l :=
    fun k l => (continuous_apply l).comp ((continuous_apply k).comp hc)
  simp only [Matrix.mul_apply, intMat, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← integral_const_mul, ← integral_mul_const]
      congr 1
      funext g
      ring
    · intro k _
      exact integrable_of_cont μ (hf.mul ((continuous_const.mul (hR k l)).mul continuous_const))
  · intro l _
    exact integrable_finsetSum _ (fun k _ =>
      integrable_of_cont μ (hf.mul ((continuous_const.mul (hR k l)).mul continuous_const)))
end PI.UnitaryGroupMassFormula.GelfCpt
