-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.exists_away_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:57:55.808868+00:00
-- url     : https://prove2.me/submissions/c93fa120-727d-4735-964b-dfcca305fd2b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PairCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsAwayNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {S : Type} [CommRing S] {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤)
    (p : Ideal S) [p.IsPrime] : ∃ k, s k ∉ p := by
  by_contra hne
  push_neg at hne
  have hle : Ideal.span (Set.range s) ≤ p := by
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    exact hne k
  rw [hs, top_le_iff] at hle
  exact Ideal.IsPrime.ne_top ‹p.IsPrime› hle
end ReciprocityTheory.ChartRestriction.G.Chart
