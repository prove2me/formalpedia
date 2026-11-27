-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_bundleA_isFinite_a4e03d594faf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:59:18.725262+00:00
-- url     : https://prove2.me/submissions/69d0d123-1418-4850-8100-0d5ecc9afe91

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
open MvPolynomial
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω]
open Classical
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
theorem _root_.solution (x : Fin (N + 1) → Ω) : (SubFamily.ofBundle (bundleA S x)).IsFinite := by
  intro i hi
  refine ⟨{x i}, le_antisymm ?_ ?_⟩
  · rw [SubFamily.mods, Submodule.span_le]
    intro e he
    obtain ⟨a, ha, rfl⟩ := (mem_lineLat x 1 i e).1 he
    exact Submodule.subset_span ⟨a, ha, x i, by simp, by simp⟩
  · rw [Submodule.span_le]
    rintro _ ⟨a, ha, _, hb, rfl⟩
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hb
    subst hb
    exact Submodule.subset_span ((mem_lineLat x 1 i _).2 ⟨a, ha, by simp⟩)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
