-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_LinEmbed_isRelevant_comap_iff_212ad1af0fab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:08:56.991336+00:00
-- url     : https://prove2.me/submissions/161030d3-3cc1-439f-8991-375078af3736

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.LinEmbed
theorem _root_.solution (W : Ideal (MRingOver F ι)) :
    IsRelevant (W.comap (blockLinSubst e A).toRingHom) ↔ IsRelevant W := by
  constructor
  · intro h k
    obtain ⟨k', rfl⟩ := e.surjective k
    obtain ⟨q, hq⟩ := h k'
    by_contra hall
    push Not at hall
    apply hq
    rw [Ideal.mem_comap]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, blockLinSubst_X]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hall i)
  · intro h k'
    obtain ⟨i, hi⟩ := h (e k')
    by_contra hall
    push Not at hall
    obtain ⟨c, hc⟩ := exists_linear_preimage hA k' i
    apply hi
    rw [← hc, map_sum]
    exact Ideal.sum_mem _ fun q _ => by
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (hall q)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.LinEmbed
