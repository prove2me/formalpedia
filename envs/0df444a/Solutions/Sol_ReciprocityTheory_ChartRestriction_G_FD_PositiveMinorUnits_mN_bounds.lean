-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:35:15.458275+00:00
-- url     : https://prove2.me/submissions/2c4ed73d-9b1a-40c5-adc7-4c0abaa989b2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveMinorUnits
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_mN_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_mN_up
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_mN_down
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_mN_top

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
theorem _root_.solution (i : ℕ) (hi : i ≤ r) : 0 ≤ mN τ G x e i ∧ mN τ G x e i ≤ mN τ G x e p0 := by
  rcases le_total i p0 with hi0 | hi0
  · constructor
    · have h1 := mN_up (hG := hG) (p0 := p0) (hp0 := hp0) (x := x) (hsg := hsg) (e := e)
        (j := i) (hj := hi0) (i := 0) (hi := Nat.zero_le _)
      rw [mN_zero] at h1
      exact h1
    · exact mN_up (hG := hG) (p0 := p0) (hp0 := hp0) (x := x) (hsg := hsg) (e := e)
        (j := p0) (hj := le_rfl) (i := i) (hi := hi0)
  · constructor
    · have h1 := mN_down (hG := hG) (p0 := p0) (x := x) (hsg := hsg) (e := e)
        (i := i) (hi := hi0) (j := r) (hij := hi) (hj := le_rfl)
      rw [mN_top (hG := hG) (p0 := p0) (x := x) (hx := hx) (hsg := hsg) (e := e) (he := he)] at h1
      exact h1
    · exact mN_down (hG := hG) (p0 := p0) (x := x) (hsg := hsg) (e := e)
        (i := p0) (hi := le_rfl) (j := i) (hij := hi0) (hj := hi)
end ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
