-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.pi_bij
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:09:46.172209+00:00
-- url     : https://prove2.me/submissions/23e7a2aa-2694-42df-96d5-dba322a54ea9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q)
    (hπ : IsPi X q π) : Function.Bijective π := by
  have hinj : Function.Injective π := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have h0 : (q : ℂ) * Hf v v = 0 := by
      rw [← hπ.2.2.1 v v, hv]
      simp [Hf]
    have h1 : Hf v v = 0 := (mul_eq_zero.1 h0).resolve_left hq
    have h2 : ∑ i, Complex.normSq (v i) = 0 := by
      have := congrArg Complex.re h1
      simpa [Hf, Complex.mul_conj, Complex.re_sum] using this
    ext i
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (v i))).1 h2 i
      (Finset.mem_univ _)
    simpa using h3
  exact ⟨hinj, LinearMap.surjective_of_injective hinj⟩
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
