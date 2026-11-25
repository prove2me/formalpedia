-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.paPF_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:12:41.800021+00:00
-- url     : https://prove2.me/submissions/a904293d-c76b-4d48-a14a-76c87f63f2b6

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
theorem _root_.solution (p : MvPolynomial ι ℂ) : Differentiable ℂ (paPF p) ∧
    ∀ (j : ι) (y : EuclideanSpace ℂ ι),
      fderiv ℂ (paPF p) y (EuclideanSpace.single j 1) = paPF (MvPolynomial.pderiv j p) y := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have e : paPF (MvPolynomial.C a) = fun _ : EuclideanSpace ℂ ι => a := by funext v; simp [paPF]
    rw [e]
    refine ⟨differentiable_const a, fun j y => ?_⟩
    simp [paPF]
  | add p r hp hr =>
    rw [paPF_add]
    refine ⟨hp.1.add hr.1, fun j y => ?_⟩
    rw [fderiv_add (hp.1 y) (hr.1 y), ContinuousLinearMap.add_apply, hp.2, hr.2, map_add, paPF_add]
    rfl
  | mul_X p k hp =>
    have hd : Differentiable ℂ (fun v : EuclideanSpace ℂ ι => v k) :=
      (EuclideanSpace.proj k : EuclideanSpace ℂ ι →L[ℂ] ℂ).differentiable
    rw [paPF_X_mul]
    refine ⟨hp.1.mul hd, fun j y => ?_⟩
    rw [fderiv_mul (hp.1 y) (hd y)]
    have e1 : fderiv ℂ (fun v : EuclideanSpace ℂ ι => v k) y =
        (EuclideanSpace.proj k : EuclideanSpace ℂ ι →L[ℂ] ℂ) :=
      (EuclideanSpace.proj k : EuclideanSpace ℂ ι →L[ℂ] ℂ).fderiv
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      e1, hp.2, Derivation.leibniz, MvPolynomial.pderiv_X]
    simp only [EuclideanSpace.coe_proj, EuclideanSpace.single_apply, smul_eq_mul, paPF, map_add,
      map_mul, MvPolynomial.eval_X, Pi.single_apply]
    by_cases h : j = k
    · subst h; simp <;> ring
    · simp [h, Ne.symm h] <;> ring
end ReciprocityTheory.ChartRestriction.G.I2
