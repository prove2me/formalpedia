-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.paPF_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:20.09927+00:00
-- url     : https://prove2.me/submissions/9e7464fd-6091-433b-a6b0-f14f77efe106

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paPF_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paPF_X_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (p : MvPolynomial ι ℂ) : ContDiff ℂ (⊤ : ℕ∞) (paPF p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have e : paPF (MvPolynomial.C a) = fun _ : EuclideanSpace ℂ ι => a := by funext v; simp [paPF]
    rw [e]; exact contDiff_const
  | add p r hp hr => rw [paPF_add]; exact hp.add hr
  | mul_X p k hp =>
    rw [paPF_X_mul]
    exact hp.mul (EuclideanSpace.proj k : EuclideanSpace ℂ ι →L[ℂ] ℂ).contDiff
end ReciprocityTheory.ChartRestriction.G.I2
