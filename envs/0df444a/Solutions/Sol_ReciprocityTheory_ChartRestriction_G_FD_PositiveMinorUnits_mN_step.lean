-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:17:18.64603+00:00
-- url     : https://prove2.me/submissions/cce939c9-9b32-4fd0-9065-0356d7c664a9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveMinorUnits
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_famN_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_unit_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_mN_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_det_gramF_real
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_det_step
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hC_self_real


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
variable {τ G} (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (p0 : ℕ) (hp0 : p0 ≤ r)
  (x : Matrix (Fin r) (Fin r) ℂ) (hx : x.det ≠ 0)
  (hsg : ∀ i (h : i ≤ r), 0 < psgn p0 i * (gramF τ G (famN x i h)).det.re)
  (e : Fin r → ℂ) (he : hermC τ G e e = 0)
include hsg
include hG
namespace ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
theorem _root_.solution (i : ℕ) (h : i + 1 ≤ r) : 0 ≤ sgn p0 i * (mN τ G x e (i + 1) - mN τ G x e i) := by
  have hA1 := unit_of p0 x hsg (i + 1) h
  have hA0 := unit_of p0 x hsg i (Nat.le_of_succ_le h)
  have hs := det_step hG (famN x (i + 1) h) e hA1 hA0
  rw [famN_succ] at hs
  rw [mN_succ hG p0 x hsg e i h, add_sub_cancel_left]
  set y := yv τ G (famN x (i + 1) h) e (Fin.last i)
  set hd := hermC τ G (dv τ G (famN x (i + 1) h) e) (dv τ G (famN x (i + 1) h) e)
  have hre := congrArg Complex.re hs
  rw [Complex.mul_conj, Complex.mul_re, Complex.mul_re, det_gramF_real hG, hC_self_real hG,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul, sub_zero] at hre
  have hps : psgn p0 (i + 1) = psgn p0 i * sgn p0 i := Finset.prod_range_succ _ _
  have key : (psgn p0 i * (gramF τ G (famN x i (Nat.le_of_succ_le h))).det.re) * (sgn p0 i * hd.re) =
      Complex.normSq y * (psgn p0 (i + 1) * (gramF τ G (famN x (i + 1) h)).det.re) := by
    rw [hps]; linear_combination (psgn p0 i * sgn p0 i) * hre
  have h1 := hsg i (Nat.le_of_succ_le h)
  have h2 := hsg (i + 1) h
  refine le_of_mul_le_mul_left ?_ h1
  rw [mul_zero, key]
  exact mul_nonneg (Complex.normSq_nonneg _) h2.le
end ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
