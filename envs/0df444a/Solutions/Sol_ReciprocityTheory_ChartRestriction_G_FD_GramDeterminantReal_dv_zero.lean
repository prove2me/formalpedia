-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.dv_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:55:07.561064+00:00
-- url     : https://prove2.me/submissions/52171da3-e155-4e15-8415-f41b56049ab9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_dv_orth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_comb_orth_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_dv_eq

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
variable {n : ℕ} (f : Fin (n + 1) → Fin r → ℂ) (e : Fin r → ℂ)
namespace ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
theorem _root_.solution {n : ℕ} (f : Fin (n + 1) → Fin r → ℂ) (e : Fin r → ℂ) (hA : IsUnit (gramF τ G f).det)
    (hA' : IsUnit (gramF τ G (fun a : Fin n => f a.castSucc)).det)
    (hy : yv τ G f e (Fin.last n) = 0) : dv τ G f e = 0 := by
  have h : dv τ G f e = ∑ a : Fin n,
      (yv τ G f e a.castSucc - yv τ G (fun a : Fin n => f a.castSucc) e a) • f a.castSucc := by
    rw [dv_eq, Fin.sum_univ_castSucc]
    simp [Fin.snoc_castSucc, Fin.snoc_last, hy]
  rw [h]
  refine comb_orth_zero τ G (fun a : Fin n => f a.castSucc) hA'
    (fun a => yv τ G f e a.castSucc - yv τ G (fun a : Fin n => f a.castSucc) e a) ?_
  intro d
  have hd := dv_orth τ G f e hA hA' d
  rw [h] at hd
  exact hd
end ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
