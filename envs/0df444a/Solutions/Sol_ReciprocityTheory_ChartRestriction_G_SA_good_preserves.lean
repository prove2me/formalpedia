-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.good_preserves
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:49:48.304587+00:00
-- url     : https://prove2.me/submissions/7d431390-4e61-4016-97f9-2cd8d78fea98

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ConjMemEichSet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ReachableFixingAddSmulSecond
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_eich_preserves
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_tor_preserves


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1) {s : ℕ} {a : Fin s → ι → K}
  (hae : ∀ j, hf σ J (a j) e = 0) (haf : ∀ j, hf σ J (a j) f = 0)
include hσ hJ he hff hef
include hae haf
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {p : Matrix ι ι K} (hp : p ∈ Good σ J e f) (x y : ι → K) :
    hf σ J (p *ᵥ x) (p *ᵥ y) = hf σ J x y := by
  obtain ⟨n, hn, l, m, hml, rfl⟩ := hp
  have key : ∀ g ∈ Submonoid.closure (eichSet σ J e f), ∀ x y : ι → K,
      hf σ J (g *ᵥ x) (g *ᵥ y) = hf σ J x y := by
    intro g hg
    induction hg using Submonoid.closure_induction with
    | mem g hg =>
      intro x y
      rcases hg with ⟨u, c, hue, huf, hc, rfl⟩ | ⟨u, c, huf, hue, hc, rfl⟩
      · apply eich_preserves <;> assumption
      · apply eich_preserves <;> assumption
    | one => intro x y; simp
    | mul g h _ _ ihg ihh =>
      intro x y
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ihg, ihh]
  have ht : ∀ x y : ι → K, hf σ J (tor σ J e f l m *ᵥ x) (tor σ J e f l m *ᵥ y) = hf σ J x y := by
    intro x y
    apply tor_preserves <;> assumption
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, key n hn, ht]
end ReciprocityTheory.ChartRestriction.G.SA
