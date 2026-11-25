-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_multAt_comap_e694e82c2a93
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:43:16.238686+00:00
-- url     : https://prove2.me/submissions/5f87a376-4cd7-4845-ad74-c9a1161dd408

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialMultAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedAlg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_quotEquiv_mk_1949219bd9ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedModule_eq_of_surjective_2c49ffad9549


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
theorem _root_.solution (J W : Ideal (MRingOver F ι)) [hW : W.IsPrime] :
    multAt (J.comap (blockLinSubst e A).toRingHom) (W.comap (blockLinSubst e A).toRingHom) =
      multAt J W := by
  have hW' : (W.comap (blockLinSubst e A).toRingHom).IsPrime := Ideal.comap_isPrime _ _
  unfold multAt
  rw [dif_pos hW', dif_pos hW]
  congr 1
  refine GroundTheory.Heights₂.Heights.NumbersDVR.length_localizedModule_eq_of_surjective
    (blockLinSubst e A).toRingHom (surj hA) W _ rfl _ _ (quotEquiv hA J).toRingEquiv.toAddEquiv
    fun s x => ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  change quotEquiv hA J (Ideal.Quotient.mk _ (s * y)) =
    Ideal.Quotient.mk J (blockLinSubst e A s) * quotEquiv hA J (Ideal.Quotient.mk _ y)
  rw [quotEquiv_mk, quotEquiv_mk, map_mul, map_mul]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.LinEmbed
