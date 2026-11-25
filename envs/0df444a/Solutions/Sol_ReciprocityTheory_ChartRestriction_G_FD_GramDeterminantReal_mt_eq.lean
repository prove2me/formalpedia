-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.mt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:59:38.782971+00:00
-- url     : https://prove2.me/submissions/9e256e82-0091-4e35-bafc-acf8d1501f0c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hC_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hC_pv_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
variable {τ G} (hG : ∀ a b, τ (G b a) = conj (τ (G a b)))
include hG
namespace ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
theorem _root_.solution {n : ℕ} (f : Fin n → Fin r → ℂ) (e : Fin r → ℂ) (hA : IsUnit (gramF τ G f).det) :
    mt τ G f e = hermC τ G (pv τ G f e) (pv τ G f e) := by
  rw [hC_pv_self hG f e hA]
  have hH : (gramF τ G f)ᴴ = gramF τ G f := by
    ext a b
    rw [Matrix.conjTranspose_apply]
    simp only [gramF, Matrix.of_apply]
    rw [hC_conj hG (f b) (f a), starRingEnd_apply]
  have hI : ∀ a b, conj ((gramF τ G f)⁻¹ a b) = (gramF τ G f)⁻¹ b a := by
    intro a b
    have h3 := congrFun (congrFun (Matrix.conjTranspose_nonsing_inv (gramF τ G f)) b) a
    rw [hH, Matrix.conjTranspose_apply] at h3
    rw [starRingEnd_apply]
    exact h3
  unfold mt yv
  simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, hI, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
