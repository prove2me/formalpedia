-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isMultiHomogIdeal_comap_a23a80c5c85c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:46:20.313214+00:00
-- url     : https://prove2.me/submissions/ea05202a-80af-4bd5-a932-81f26f50efed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialMultAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedAlg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isMultiHomog_sub_f296f6b42305
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isMultiHomog_blockLinSubst_X_c66491ee9fd3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isMultiHomog_sect_4940d65f27ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_comap_eq_34c4a652edd5
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_X


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
theorem _root_.solution {V : Ideal (MRingOver F ι)} (hV : IsMultiHomogIdeal V) :
    IsMultiHomogIdeal (V.comap (blockLinSubst e A).toRingHom) := by
  obtain ⟨S, hS, rfl⟩ := hV
  refine ⟨Set.range (fun q => (X q : MRingOver F ι') - sect hA (blockLinSubst e A (X q))) ∪
    sect hA '' S, ?_, ?_⟩
  · rintro f (⟨q, rfl⟩ | ⟨s, hs, rfl⟩)
    · refine ⟨Pi.single q.1 1, isMultiHomog_sub (isMultiHomog_X (F := F) q.1 q.2) ?_⟩
      have h2 := isMultiHomog_sect hA (isMultiHomog_blockLinSubst_X (A := A) q)
      have hd : ((Pi.single (e q.1) 1 : K → ℕ) ∘ e) = Pi.single q.1 1 := by
        funext k'
        simp only [Function.comp_apply, Pi.single_apply, e.apply_eq_iff_eq]
      rwa [hd] at h2
    · obtain ⟨a, ha⟩ := hS s hs
      exact ⟨a ∘ e, isMultiHomog_sect hA ha⟩
  · rw [comap_eq hA, Ideal.map_span, Ideal.span_union]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.LinEmbed
