-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.exists_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:12:54.783616+00:00
-- url     : https://prove2.me/submissions/5571498c-6367-4b23-8189-b5c602ca9422

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ChartAway
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_chart_away

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
variable {S : Type} [CommRing S] (G : Over (Spec (CommRingCat.of S))) [GrpObj G]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution : ∃ (n : ℕ) (s : Fin n → S), Ideal.span (Set.range s) = ⊤ ∧ ∀ i, Nonempty (Chart (Gs G (s i))) := by
  classical
  have htop : Ideal.span {t : S | Nonempty (Chart (Gs G t))} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    let p : Spec (CommRingCat.of S) := ⟨M, hM.isPrime⟩
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset
      (show (η[G]).left p ∈ (⊤ : G.left.Opens) by simp)
    obtain ⟨V, ⟨t, rfl⟩, hpV, hVle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (PrimeSpectrum.isBasis_basic_opens (R := S)))
      (show p ∈ ((η[G]).left ⁻¹ᵁ U : (Spec (CommRingCat.of S)).Opens) from hpU)
    have hc : Nonempty (Chart (Gs G t)) := chart_away G U hU t (fun x hx => hVle hx)
    exact hpV (hle (Ideal.subset_span hc))
  obtain ⟨T, hsub, hspan⟩ := (Ideal.span_eq_top_iff_finite _).mp htop
  refine ⟨T.card, fun i => (T.equivFin.symm i : S), ?_, ?_⟩
  · have hr : Set.range (fun i => (T.equivFin.symm i : S)) = (T : Set S) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (T.equivFin.symm i).2
      · intro hx
        exact ⟨T.equivFin ⟨x, hx⟩, by simp⟩
    rw [hr]
    exact hspan
  · intro i
    exact hsub (T.equivFin.symm i).2
end ReciprocityTheory.ChartRestriction.G.Chart
