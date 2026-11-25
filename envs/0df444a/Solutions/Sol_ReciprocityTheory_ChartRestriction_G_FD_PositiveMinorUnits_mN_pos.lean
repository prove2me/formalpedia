-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:42:26.827528+00:00
-- url     : https://prove2.me/submissions/b545fdbe-6ad9-466e-8814-fe34b8e1d503

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveMinorUnits
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_famN_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_unit_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_mN_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_pN_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_mN_bounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_det_gramF_real
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_det_step
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_dv_zero
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
include hp0 hx he
namespace ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
theorem _root_.solution (hne : e ≠ 0) : 0 < mN τ G x e p0 := by
  by_contra hle
  rw [not_lt] at hle
  have hz : ∀ i, i ≤ r → mN τ G x e i = 0 := fun i hi => by
    have := mN_bounds hG p0 hp0 x hx hsg e he i hi; linarith
  have hstep : ∀ i (h : i + 1 ≤ r), pN τ G x e (i + 1) = pN τ G x e i := by
    intro i h
    have hA1 := unit_of p0 x hsg (i + 1) h
    have hA0 := unit_of p0 x hsg i (Nat.le_of_succ_le h)
    have hd0 : (hermC τ G (dv τ G (famN x (i + 1) h) e) (dv τ G (famN x (i + 1) h) e)).re = 0 := by
      have := mN_succ hG p0 x hsg e i h
      rw [hz i (by omega), hz (i + 1) h] at this; linarith
    have hs := det_step hG (famN x (i + 1) h) e hA1 hA0
    have hre := congrArg Complex.re hs
    rw [Complex.mul_conj, Complex.mul_re, Complex.mul_re, det_gramF_real hG, hC_self_real hG,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul, sub_zero, hd0,
      mul_zero] at hre
    have hd1 : (gramF τ G (famN x (i + 1) h)).det.re ≠ 0 := fun h0 => by
      have := hsg (i + 1) h; rw [h0, mul_zero] at this; exact lt_irrefl _ this
    have hy : yv τ G (famN x (i + 1) h) e (Fin.last i) = 0 :=
      Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hre.symm).resolve_right hd1)
    have hdv := dv_zero τ G (famN x (i + 1) h) e hA1 hA0 hy
    rw [dv, famN_succ, sub_eq_zero] at hdv
    simp only [pN, dif_pos h, dif_pos (Nat.le_of_succ_le h)]
    exact hdv
  have hall : ∀ i, i ≤ r → pN τ G x e i = 0 := by
    intro i hi
    induction i with
    | zero => rw [pN, dif_pos (Nat.zero_le r), pv]; exact Finset.sum_empty
    | succ i ih => rw [hstep i hi, ih (by omega)]
  exact hne ((pN_top hG p0 x hx hsg e).symm.trans (hall r le_rfl))
end ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
