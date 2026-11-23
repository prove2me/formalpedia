-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.lemS_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:19.919798+00:00
-- url     : https://prove2.me/submissions/d8c41116-84b4-499a-ba1c-317b48b5c544

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RSubMean
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_lemS_Hf_eq_inner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex Metric
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (Y : GT ι) (q : ℕ) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ Y.Sec q)
    {γ : EuclideanSpace ℂ ι} (hγ : γ ∈ lat Y.b) (v : EuclideanSpace ℂ ι) :
    Y.ptN2 q F (γ + v) = Y.ptN2 q F v := by
  obtain ⟨_, hF'⟩ := hF
  have h := hF' γ hγ v
  have hnorm : ‖v + γ‖ ^ 2 = ‖v‖ ^ 2 + 2 * (Hf v γ).re + ‖γ‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ), lemS_Hf_eq_inner, inner_re_symm]
    rfl
  have hγγ : Hf γ γ = ((‖γ‖ ^ 2 : ℝ) : ℂ) := by
    rw [lemS_Hf_eq_inner]
    first
      | exact_mod_cast inner_self_eq_norm_sq_to_K (𝕜 := ℂ) γ
      | (rw [inner_self_eq_norm_sq_to_K]; simp)
      | (rw [inner_self_eq_norm_sq_to_K]; norm_cast)
  have hA : ∀ z : ℂ, ((q : ℂ) * (Real.pi : ℂ) * z + (q : ℂ) * (Real.pi : ℂ) * ((‖γ‖ ^ 2 : ℝ) : ℂ) / 2).re =
      q * Real.pi * z.re + q * Real.pi * ‖γ‖ ^ 2 / 2 := by
    intro z
    simp
    first
      | (left; rw [← Complex.ofReal_pow, Complex.ofReal_re])
      | ring
  have key : Real.exp (q * Real.pi * (Hf v γ).re + q * Real.pi * ‖γ‖ ^ 2 / 2) ^ 2 *
      Real.exp (-(q * Real.pi) * (‖v‖ ^ 2 + 2 * (Hf v γ).re + ‖γ‖ ^ 2)) =
        Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  simp only [GT.ptN2]
  rw [add_comm γ v, h, norm_mul, norm_mul, Y.ka_abs γ hγ, Complex.norm_exp, hnorm, hγγ, hA]
  linear_combination ‖F v‖ ^ 2 * key
end ReciprocityTheory.ChartRestriction.G.I2
