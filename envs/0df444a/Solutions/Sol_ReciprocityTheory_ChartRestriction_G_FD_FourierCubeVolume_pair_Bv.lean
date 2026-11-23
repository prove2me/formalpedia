-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume.pair_Bv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:10.071803+00:00
-- url     : https://prove2.me/submissions/4a581449-0932-4914-ab18-a2d60a603c80

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeVolume

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section
variable {ι : Type} [Fintype ι] {N : ℕ} (ω : Fin N → ι → Fin 2 → Fin 2 → ℂ)
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
theorem _root_.solution (χ : ι → Fin 2 → Fin 2 → ℂ) (t : Fin N → ℝ) :
    pr χ (Bv ω t) = ∑ j, t j * pr χ (ω j) := by
  have hadd : ∀ b b' : ι → Fin 2 → Fin 2 → ℂ, pr χ (b + b') = pr χ b + pr χ b' := by
    intro b b'
    simp only [pr, Pi.add_apply, mul_add, Finset.sum_add_distrib, Complex.add_re]
  have hsm : ∀ (c : ℝ) (b : ι → Fin 2 → Fin 2 → ℂ), pr χ ((c : ℂ) • b) = c * pr χ b := by
    intro c b
    simp only [pr, Pi.smul_apply, smul_eq_mul]
    rw [← Complex.re_ofReal_mul]
    congr 1
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun τ _ => Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun k _ => by ring)))
  let P : (ι → Fin 2 → Fin 2 → ℂ) →+ ℝ := AddMonoidHom.mk' (pr χ) hadd
  have h1 : pr χ (Bv ω t) = P (Bv ω t) := rfl
  rw [h1, Bv, map_sum]
  exact Finset.sum_congr rfl (fun j _ => hsm _ _)
end ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
