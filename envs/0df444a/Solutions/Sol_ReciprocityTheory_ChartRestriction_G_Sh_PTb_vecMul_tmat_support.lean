-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.vecMul_tmat_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:36:27.256802+00:00
-- url     : https://prove2.me/submissions/43cbda7e-5994-4f79-8d54-66a3a9810530

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_EqZeroOfVecMulTmat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_eq_zero_of_vecMul_tmat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution {h : ℕ} (ty : Fin d → ZMod h) {γ : Fin d → Fin d → PowerSeries C}
    (hdet : v (tmat γ).det = 0) (ht : ∀ b c, ty c ≠ ty b → tangent (γ b) c = 0)
    (x : Fin d → C) (τ : ZMod h) (hw : ∀ c, ty c ≠ τ → Matrix.vecMul x (tmat γ) c = 0) :
    ∀ b, ty b ≠ τ → x b = 0 := by
  intro b hb
  set x' : Fin d → C := fun b => if ty b ≠ τ then x b else 0 with hx'
  have hz : Matrix.vecMul x' (tmat γ) = 0 := by
    funext c
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    by_cases hc : ty c = τ
    · apply Finset.sum_eq_zero
      intro b' _
      by_cases hb' : ty b' ≠ τ
      · have h0 : tangent (γ b') c = 0 := ht b' c (by rw [hc]; exact fun h => hb' h.symm)
        simp [hx', hb', tmat, h0]
      · simp [hx', hb']
    · have h0 := hw c hc
      simp only [Matrix.vecMul, dotProduct] at h0
      rw [← h0]
      apply Finset.sum_congr rfl
      intro b' _
      by_cases hb' : ty b' ≠ τ
      · simp [hx', hb']
      · have hb2 : ty b' = τ := not_not.mp hb'
        have h1 : tangent (γ b') c = 0 := ht b' c (by rw [hb2]; exact hc)
        simp [hx', hb', tmat, h1]
  have h3 := congrFun (eq_zero_of_vecMul_tmat hdet hz) b
  simpa [hx', hb] using h3
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
