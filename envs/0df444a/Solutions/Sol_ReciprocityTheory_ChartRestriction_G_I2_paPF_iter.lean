-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.paPF_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:24:25.196368+00:00
-- url     : https://prove2.me/submissions/ad9d2bd0-91c9-4110-baa6-0bb2b2635145

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paPF_diff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paPF_contDiff

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
theorem _root_.solution (n : ℕ) : ∀ (p : MvPolynomial ι ℂ) (m : Fin n → ι) (x : EuclideanSpace ℂ ι),
    iteratedFDeriv ℂ n (paPF p) x (fun k => EuclideanSpace.single (m k) 1) = paPF (paPD n m p) x := by
  induction n with
  | zero => intro p m x; simp [paPD]
  | succ n ih =>
    intro p m x
    rw [iteratedFDeriv_succ_apply_right]
    have hc : ContDiff ℂ (⊤ : ℕ∞) (fderiv ℂ (paPF p)) :=
      (paPF_contDiff p).fderiv_right (by simp)
    rw [← iteratedFDeriv_clm_apply_const_apply hc (by exact_mod_cast le_top)]
    have e : (fun y => fderiv ℂ (paPF p) y (EuclideanSpace.single (m (Fin.last n)) 1)) =
        paPF (MvPolynomial.pderiv (m (Fin.last n)) p) := by
      funext y; exact (paPF_diff p).2 _ y
    rw [e]
    exact ih _ (Fin.init m) x
end ReciprocityTheory.ChartRestriction.G.I2
