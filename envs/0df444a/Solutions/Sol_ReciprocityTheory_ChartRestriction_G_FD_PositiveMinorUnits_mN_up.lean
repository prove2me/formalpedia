-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:28:30.145445+00:00
-- url     : https://prove2.me/submissions/f49bace7-cdcf-429c-b559-a3e784ceffbf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveMinorUnits
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_mN_step

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
include hp0
namespace ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
theorem _root_.solution (j : ℕ) (hj : j ≤ p0) (i : ℕ) (hi : i ≤ j) : mN τ G x e i ≤ mN τ G x e j := by
  have step : ∀ k, k < p0 → mN τ G x e k ≤ mN τ G x e (k + 1) := by
    intro k hk
    have h1 := mN_step (hG := hG) (p0 := p0) (x := x) (hsg := hsg) (e := e) (i := k) (h := by omega)
    have hs : sgn p0 k = 1 := by simp [sgn, hk]
    rw [hs] at h1
    linarith
  revert hj
  induction j, hi using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ j hij ih => intro hj; exact (ih (by omega)).trans (step j (by omega))
end ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
