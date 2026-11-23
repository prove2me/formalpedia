-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:46.672918+00:00
-- url     : https://prove2.me/submissions/ee99c3cc-bc02-4a43-a602-571aa7721a09

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveMinorUnits
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_pN_top

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
include hx he
namespace ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
theorem _root_.solution : mN τ G x e r = 0 := by
  unfold mN
  rw [pN_top (hG := hG) (p0 := p0) (x := x) (hx := hx) (hsg := hsg) (e := e), he]
  simp
end ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
