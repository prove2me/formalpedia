-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.snc_eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:06:06.308795+00:00
-- url     : https://prove2.me/submissions/731d7b9d-2850-4a84-9bcb-c8ae63c490d1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_SNCAtlas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {L : LocPot X} {s : X → X → ℂ} {r : ℕ} {m : Fin r → ℕ} {W : Fin r → Set X}
    (h : IsSNC A L s m W) {k : Fin r} {x : X} (hx : x ∈ W k) (hm : m k ≠ 0) : s x x = 0 := by
  obtain ⟨ψ, -, hxs, -, σ, -, hW, u, -, -, hs⟩ := h x
  have hx' : x ∈ W k ∩ ψ.source := ⟨hx, hxs⟩
  rw [hW k] at hx'
  obtain ⟨-, i, hσ, hψ⟩ := hx'
  rw [hs x hxs]
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  simp [hσ, hψ, hm]
end ReciprocityTheory.ChartRestriction.G.Geo
