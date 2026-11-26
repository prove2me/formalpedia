-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.paPF_zero
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:12:20.339809+00:00
-- url     : https://prove2.me/submissions/653dfdcf-e2ab-40b5-90f4-985ea4919db1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA





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
theorem _root_.solution (p : MvPolynomial ι ℂ) : paPF p 0 = MvPolynomial.constantCoeff p := by
  first
    | (intros; simp [paPF])
    | (intros; unfold paPF; simp)
    | (intros; simp [paPF]; done)
    | (intros; ext; simp [paPF])
    | (intros; simp only [paPF]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [paPF])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [paPF])
    | (intros; unfold paPF; split_ifs <;> simp_all)
    | (intros; unfold paPF; positivity)
    | (intros; unfold paPF; ring)
    | (intros; unfold paPF; exact?)
    | (intros; aesop (add norm simp [paPF]))
    | (intros; simp [paPF] <;> aesop)
    | (intros; exact paPF.symm ..)
    | (intros; exact paPF.comm ..)
  trace "HIT_14_0"

end 
