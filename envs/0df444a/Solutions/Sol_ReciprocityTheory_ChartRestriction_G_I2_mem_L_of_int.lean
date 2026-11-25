-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.mem_L_of_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:09:49.266809+00:00
-- url     : https://prove2.me/submissions/0fb52557-c5ca-4aea-a308-655b3f3a2a94

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceMinima
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_eq_zero_of_im_L
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (X : PT E) {a : Vsp X.dim} (h : ∀ y ∈ X.L, ∃ k : ℤ, (Hf y a).im = k) :
    a ∈ X.L := by
  have hadd : ∀ y y' : Vsp X.dim, (Hf (y + y') a).im = (Hf y a).im + (Hf y' a).im :=
    fun y y' => by simp [Hf, add_mul, Finset.sum_add_distrib]
  let φ : X.L →+ ℤ :=
    { toFun := fun y => (h (y : Vsp X.dim) y.2).choose
      map_zero' := by
        have e := (h ((0 : X.L) : Vsp X.dim) (0 : X.L).2).choose_spec
        have e' : (((h ((0 : X.L) : Vsp X.dim) (0 : X.L).2).choose : ℤ) : ℝ) = 0 := by
          rw [← e]
          simp [Hf]
        exact_mod_cast e'
      map_add' := fun y y' => by
        have e1 := (h ((y + y' : X.L) : Vsp X.dim) (y + y').2).choose_spec
        have e2 := (h (y : Vsp X.dim) y.2).choose_spec
        have e3 := (h (y' : Vsp X.dim) y'.2).choose_spec
        have e' : (((h ((y + y' : X.L) : Vsp X.dim) (y + y').2).choose : ℤ) : ℝ) =
            (h (y : Vsp X.dim) y.2).choose + (h (y' : Vsp X.dim) y'.2).choose := by
          rw [← e1, ← e2, ← e3, Submodule.coe_add, hadd]
        exact_mod_cast e' }
  obtain ⟨x, hx, hxy⟩ := X.perfect φ
  have key : a + x = 0 := by
    apply eq_zero_of_im_L X
    intro y hy
    have h1 : ((φ ⟨y, hy⟩ : ℤ) : ℝ) = (Hf x y).im := hxy ⟨y, hy⟩
    have hφ : ((φ ⟨y, hy⟩ : ℤ) : ℝ) = (Hf y a).im := (h y hy).choose_spec.symm
    have hc : (Hf y x).im = -(Hf x y).im := by
      have hcj : Hf y x = starRingEnd ℂ (Hf x y) := by simp [Hf, map_sum, mul_comm]
      rw [hcj, Complex.conj_im]
    have hr : Hf y (a + x) = Hf y a + Hf y x := by simp [Hf, mul_add, Finset.sum_add_distrib]
    rw [hr, Complex.add_im, hc, ← h1, hφ]
    ring
  have ha : a = -x := eq_neg_of_add_eq_zero_left key
  rw [ha]
  exact neg_mem hx
end ReciprocityTheory.ChartRestriction.G.I2
