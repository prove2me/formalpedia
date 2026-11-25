-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_comap_eq_34c4a652edd5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:16:13.609592+00:00
-- url     : https://prove2.me/submissions/ba522ff7-323f-464f-85a7-e85201dd4f51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialMultAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.LinEmbed
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
set_option linter.unusedSectionVars false
variable {F : Type} [Field F] {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k', Fintype (ι' k')] {e : K' ≃ K} {A : ∀ k', ι' k' → ι (e k') → F}
variable (hA : ∀ k', Function.Injective (Matrix.of (A k')).mulVec)
include hA
open Classical
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.LinEmbed
theorem _root_.solution (V : Ideal (MRingOver F ι)) :
    V.comap (blockLinSubst e A).toRingHom =
      Ideal.span (Set.range fun q => (X q : MRingOver F ι') - sect hA (blockLinSubst e A (X q))) ⊔
        V.map (sect hA) := by
  set J := Ideal.span (Set.range fun q => (X q : MRingOver F ι') - sect hA (blockLinSubst e A (X q)))
  apply le_antisymm
  · intro g hg
    have hJ : g - sect hA (blockLinSubst e A g) ∈ J := by
      rw [← Ideal.Quotient.eq]
      have h : (Ideal.Quotient.mkₐ F J).comp ((sect hA).comp (blockLinSubst e A)) =
          Ideal.Quotient.mkₐ F J := algHom_ext fun q => by
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
        rw [Ideal.Quotient.eq, ← neg_sub, neg_mem_iff]
        exact Ideal.subset_span ⟨q, rfl⟩
      exact (AlgHom.congr_fun h g).symm
    have hg' : g = (g - sect hA (blockLinSubst e A g)) + sect hA (blockLinSubst e A g) := by ring
    rw [hg']
    exact Ideal.add_mem _ (Ideal.mem_sup_left hJ) (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hg))
  · refine sup_le (Ideal.span_le.mpr ?_) (Ideal.map_le_iff_le_comap.mpr fun v hv => ?_)
    · rintro _ ⟨q, rfl⟩
      simp [blockLinSubst_sect]
    · simp [Ideal.mem_comap, blockLinSubst_sect, hv]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.LinEmbed
