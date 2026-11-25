-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_ptDeg_comap_42f6d6529974
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:16:19.347577+00:00
-- url     : https://prove2.me/submissions/dc370e0d-85dc-474d-8e6f-c3017b875927

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialMultAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedAlg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_injective_of_isField_020813170944
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isMultiHomog_blockLinSubst_X_c66491ee9fd3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isMultiHomog_sect_4940d65f27ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isProjVarF_comap_418cc18913ce
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_chart_finite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_chart_isField
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isUnit_mk_chartIdeal_form


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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.LinEmbed
theorem _root_.solution {V : Ideal (MRingOver F ι)} (hV : IsProjVarF V 0) {i : ∀ k, ι k}
    (hi : IsChart V i) {i' : ∀ k', ι' k'} (hi' : IsChart (V.comap (blockLinSubst e A).toRingHom) i') :
    ptDeg (V.comap (blockLinSubst e A).toRingHom) i' = ptDeg V i := by
  have hV' : IsProjVarF (V.comap (blockLinSubst e A).toRingHom) 0 := isProjVarF_comap hA hV
  let θ : MRingOver F ι' →ₐ[F] MRingOver F ι ⧸ chartIdeal V i :=
    (Ideal.Quotient.mkₐ F (chartIdeal V i)).comp (blockLinSubst e A)
  let θ' : MRingOver F ι →ₐ[F] MRingOver F ι' ⧸ chartIdeal (V.comap (blockLinSubst e A).toRingHom) i' :=
    (Ideal.Quotient.mkₐ F (chartIdeal (V.comap (blockLinSubst e A).toRingHom) i')).comp (sect hA)
  have hθ : ∀ g ∈ V.comap (blockLinSubst e A).toRingHom, θ g = 0 := fun g hg =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hg)
  have hθ' : ∀ g ∈ V, θ' g = 0 := fun g hg => by
    refine Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left ?_)
    rw [Ideal.mem_comap]
    simpa [blockLinSubst_sect] using hg
  have hu : ∀ k', IsUnit (θ (X ⟨k', i' k'⟩)) :=
    fun k' => isUnit_mk_chartIdeal_form hV i (isMultiHomog_blockLinSubst_X _) (hi' k')
  have hw : ∀ k, IsUnit (θ' (X ⟨k, i k⟩)) := fun k =>
    isUnit_mk_chartIdeal_form hV' i' (isMultiHomog_sect hA (isMultiHomog_X k (i k))) (by
      rw [Ideal.mem_comap]
      simpa [blockLinSubst_sect] using hi k)
  let α := linChartMap hV'.1.2.1 i' θ hθ hu
  let β := linChartMap hV.1.2.1 i θ' hθ' hw
  have hF := chart_isField hV hi
  have hF' := chart_isField hV' hi'
  have : Nontrivial (MRingOver F ι ⧸ chartIdeal V i) := ⟨hF.exists_pair_ne⟩
  have : Nontrivial (MRingOver F ι' ⧸ chartIdeal (V.comap (blockLinSubst e A).toRingHom) i') :=
    ⟨hF'.exists_pair_ne⟩
  have := chart_finite hV hi
  have := chart_finite hV' hi'
  exact le_antisymm
    (LinearMap.finrank_le_finrank_of_injective (f := α.toLinearMap)
      (injective_of_isField hF' α.toRingHom))
    (LinearMap.finrank_le_finrank_of_injective (f := β.toLinearMap)
      (injective_of_isField hF β.toRingHom))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.LinEmbed
