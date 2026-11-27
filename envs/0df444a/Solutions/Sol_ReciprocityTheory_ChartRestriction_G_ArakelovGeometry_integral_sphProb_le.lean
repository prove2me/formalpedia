-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.integral_sphProb_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:42:10.748044+00:00
-- url     : https://prove2.me/submissions/2f36d9c1-2a44-46fb-bdc7-026d98c4afec

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CNormSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_HadZSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStA
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coe_dehK
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphProb_compl_sphere
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.coe_dehK



set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {D : ℕ} (F : (Fin (D + 1) → ℂ) → ℝ) (hF0 : ∀ w, 0 ≤ F w) {B : ℝ}
    (hB : ∀ w, sqN w = 1 → F w ≤ B) : ∫ w, F w ∂(sphProb (D + 1)) ≤ B := by
  have hae : ∀ᵐ w ∂(sphProb (D + 1)), sqN w = 1 := by
    rw [ae_iff]
    exact sphProb_compl_sphere D
  calc ∫ w, F w ∂(sphProb (D + 1)) ≤ ∫ _w, B ∂(sphProb (D + 1)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall hF0) (integrable_const B)
          (hae.mono fun w hw => hB w hw)
    _ = B := by simp
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
