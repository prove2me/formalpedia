-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:59:57.683837+00:00
-- url     : https://prove2.me/submissions/a4d56272-8032-4f6f-8353-66aeec30855a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveMinorUnits
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_famN_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_unit_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_pv_pyth


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
theorem _root_.solution (i : ℕ) (h : i + 1 ≤ r) : mN τ G x e (i + 1) = mN τ G x e i +
    (hermC τ G (dv τ G (famN x (i + 1) h) e) (dv τ G (famN x (i + 1) h) e)).re := by
  have hp := pv_pyth hG (famN x (i + 1) h) e (unit_of p0 x hsg (i + 1) h)
    (unit_of p0 x hsg i (Nat.le_of_succ_le h))
  rw [famN_succ] at hp
  simp only [mN, pN, dif_pos h, dif_pos (Nat.le_of_succ_le h)]
  rw [hp, Complex.add_re]
end ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
