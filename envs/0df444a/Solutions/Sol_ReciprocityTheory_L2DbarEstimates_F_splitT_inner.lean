-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.splitT_inner
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:11.451797+00:00
-- url     : https://prove2.me/submissions/9842bd19-72fb-4427-b327-52863b6d977c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_SplitTest
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n}
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ph : M → ℝ) (hph : Continuous ph) (F : M → E) (hF : MemLp F 2 (wvol n z ph))
    (G : Lp E 2 (wvol n z ph)) :
    ⟪hF.toLp F, G⟫_ℂ = ∫ x, ⟪F x, G x⟫_ℂ * (Real.exp (-ph x) : ℂ) ∂vol n z := by
  have hd : Measurable (fun x => (Real.exp (-ph x)).toNNReal) :=
    (Real.continuous_exp.comp hph.neg).measurable.real_toNNReal
  have hae : (fun a => ⟪(hF.toLp F) a, G a⟫_ℂ) =ᵐ[wvol n z ph] fun a => ⟪F a, G a⟫_ℂ :=
    hF.coeFn_toLp.mono fun x hx => by dsimp only; rw [hx]
  rw [MeasureTheory.L2.inner_def, integral_congr_ae hae]
  show ∫ a, ⟪F a, G a⟫_ℂ ∂((vol n z).withDensity fun x => ((Real.exp (-ph x)).toNNReal : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hd]
  congr 1
  funext x
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_nonneg _), Complex.real_smul]
  ring
end ReciprocityTheory.L2DbarEstimates.F
