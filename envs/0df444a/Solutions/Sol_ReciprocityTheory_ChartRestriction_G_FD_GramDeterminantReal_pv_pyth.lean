-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.pv_pyth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:53:47.508274+00:00
-- url     : https://prove2.me/submissions/0c56ff74-4b45-4972-8bd3-8383348eed1d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_dv_orth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hC_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hC_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hC_sum_right

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
variable {n : ℕ} (f : Fin (n + 1) → Fin r → ℂ) (e : Fin r → ℂ)
namespace ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
theorem _root_.solution (hA : IsUnit (gramF τ G f).det)
    (hA' : IsUnit (gramF τ G (fun a : Fin n => f a.castSucc)).det) :
    hermC τ G (pv τ G f e) (pv τ G f e) =
      hermC τ G (pv τ G (fun a : Fin n => f a.castSucc) e)
        (pv τ G (fun a : Fin n => f a.castSucc) e) + hermC τ G (dv τ G f e) (dv τ G f e) := by
  have hp : pv τ G f e = pv τ G (fun a : Fin n => f a.castSucc) e + dv τ G f e := by
    unfold dv
    abel
  have h0 : hermC τ G (dv τ G f e) (pv τ G (fun a : Fin n => f a.castSucc) e) = 0 := by
    rw [show hermC τ G (dv τ G f e) (pv τ G (fun a : Fin n => f a.castSucc) e) =
        hermC τ G (dv τ G f e) (∑ b, yv τ G (fun a : Fin n => f a.castSucc) e b • f b.castSucc)
        from rfl, hC_sum_right hG]
    exact Finset.sum_eq_zero fun b _ => by simp only [dv_orth τ G f e hA hA' b, mul_zero]
  have h1 : hermC τ G (pv τ G (fun a : Fin n => f a.castSucc) e) (dv τ G f e) = 0 := by
    rw [hC_conj hG (dv τ G f e) _, h0, map_zero]
  rw [hp, hC_add_left, hC_add_right hG, hC_add_right hG, h0, h1]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
