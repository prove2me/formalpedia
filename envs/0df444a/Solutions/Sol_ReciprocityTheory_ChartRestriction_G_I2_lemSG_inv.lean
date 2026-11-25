-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.lemSG_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:25:31.272007+00:00
-- url     : https://prove2.me/submissions/041e7c8f-d658-4199-8cab-0f833d996908

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_lemS_Hf_sum

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
open scoped Matrix
noncomputable section
variable {ι : Type} [Fintype ι]
set_option maxHeartbeats 800000
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (Y : GT ι) :
    ∃ C : Matrix (Fin (2 * Fintype.card ι)) (Fin (2 * Fintype.card ι)) ℤ,
      (C.map (Int.cast : ℤ → ℝ)) * lemSG Y.b = 1 := by
  classical
  have hx : ∀ k, ∃ x ∈ lat Y.b, ∀ y : lat Y.b,
      ((((Y.b.restrictScalars ℤ).coord k).toAddMonoidHom y : ℤ) : ℝ) =
        (Hf x (y : EuclideanSpace ℂ ι)).im :=
    fun k => Y.perfect _
  choose x hxl hxφ using hx
  refine ⟨Matrix.of fun k i => (Y.b.restrictScalars ℤ).repr ⟨x k, hxl k⟩ i, ?_⟩
  ext k m
  have hsum : x k = ∑ i, ((Y.b.restrictScalars ℤ).repr ⟨x k, hxl k⟩ i) • Y.b i := by
    have h := congrArg (fun v : lat Y.b => (v : EuclideanSpace ℂ ι))
      ((Y.b.restrictScalars ℤ).sum_repr ⟨x k, hxl k⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Module.Basis.restrictScalars_apply] at h
    exact h.symm
  have h2 : (Hf (x k) (Y.b m)).im =
      ∑ i, (((Y.b.restrictScalars ℤ).repr ⟨x k, hxl k⟩ i : ℤ) : ℝ) * (Hf (Y.b i) (Y.b m)).im := by
    conv_lhs => rw [hsum]
    exact lemS_Hf_sum _ _ _
  have h3 : (Hf (x k) (Y.b m)).im =
      ((((Y.b.restrictScalars ℤ).coord k) ((Y.b.restrictScalars ℤ) m) : ℤ) : ℝ) := by
    have h := hxφ k ((Y.b.restrictScalars ℤ) m)
    rw [LinearMap.toAddMonoidHom_coe, Module.Basis.restrictScalars_apply] at h
    exact h.symm
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, lemSG, Matrix.one_apply]
  rw [← h2, h3, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  rcases eq_or_ne k m with rfl | hkm
  · simp
  · simp [hkm, Ne.symm hkm]
end ReciprocityTheory.ChartRestriction.G.I2
