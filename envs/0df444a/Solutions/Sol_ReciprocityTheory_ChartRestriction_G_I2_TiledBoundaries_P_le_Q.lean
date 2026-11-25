-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.P_le_Q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:20:35.927413+00:00
-- url     : https://prove2.me/submissions/588777bc-58b1-4c7e-af1b-863a863804c9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanBn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_mem_P
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_mem_Q
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
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory MeasureTheory.Measure Complex Module Set Submodule
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) :
    span ℤ (range (bP X hq hπ)) ≤ span ℤ (range (bQ X hq)) := by
  intro x hx
  rw [mem_P] at hx
  rw [mem_Q]
  have hH : ∀ a c : Vsp X.dim, Hf a c = @inner ℂ _ _ c a := fun a c => by
    simp only [Hf, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hround : ∀ y : Vsp X.dim, y ∈ X.L →
      ((round (Hf (π x) (π y)).im : ℤ) : ℝ) = (Hf (π x) (π y)).im := by
    intro y hy
    obtain ⟨k, hk⟩ := X.integral _ _ hx (hπ.2.1 y hy)
    rw [hk, round_intCast]
  have hadd : ∀ y1 y2 : Vsp X.dim,
      (Hf (π x) (π (y1 + y2))).im = (Hf (π x) (π y1)).im + (Hf (π x) (π y2)).im := by
    intro y1 y2
    rw [hH, hH, hH, map_add, inner_add_left, Complex.add_im]
  let φ : X.L →+ ℤ :=
    { toFun := fun y => round (Hf (π x) (π y)).im
      map_zero' := by simp [hH]
      map_add' := fun y1 y2 => by
        apply Int.cast_injective (α := ℝ)
        simp only [Submodule.coe_add, Int.cast_add]
        rw [hround _ (X.L.add_mem y1.2 y2.2), hround _ y1.2, hround _ y2.2]
        exact hadd _ _ }
  obtain ⟨w, hwL, hw⟩ := X.perfect φ
  have hLu : ∀ y ∈ X.L, (@inner ℂ _ _ y (w - (q : ℝ) • x)).im = 0 := by
    intro y hy
    have h1 := hw ⟨y, hy⟩
    have h2 := hπ.2.2.1 x y
    simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h1
    rw [hround _ hy, h2, hH, hH] at h1
    rw [inner_sub_right, ← Complex.coe_smul, inner_smul_right, Complex.sub_im, ← h1]
    simp
  let Lf : Vsp X.dim →ₗ[ℝ] ℝ := Complex.imLm.comp ((innerₛₗ ℂ (w - (q : ℝ) • x)).restrictScalars ℝ)
  have hLf : Lf = 0 := X.b.ext fun i => by
    have h := hLu _ (Submodule.subset_span (Set.mem_range_self i))
    rw [← inner_conj_symm, Complex.conj_im, neg_eq_zero] at h
    simpa [Lf, inner_sub_left] using h
  have hall : ∀ y, (@inner ℂ _ _ (w - (q : ℝ) • x) y).im = 0 := fun y => by
    exact LinearMap.congr_fun hLf y
  have hu0 : w - (q : ℝ) • x = 0 := by
    have h1 := hall (Complex.I • (w - (q : ℝ) • x))
    rw [inner_smul_right] at h1
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] at h1
    have h2 : ‖w - (q : ℝ) • x‖ ^ 2 = 0 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
      exact h1
    exact norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h2)
  rw [← sub_eq_zero.mp hu0]
  exact hwL
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
