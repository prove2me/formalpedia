-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_aeval_liftZ_4942534c525a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:44.363621+00:00
-- url     : https://prove2.me/submissions/289b35d2-1d16-4554-91e6-e16f93958fff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiProjPrimeImageZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LiftZComponent

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open GroundTheory.Heights₂.Heights.Inter.FibreMultiHomogeneous
variable {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
namespace GroundTheory.Heights₂.Heights.Inter.FibreMultiHomogeneous
theorem _root_.solution [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {W' : Ideal (MRing ι')} (G : GenFibre v W')
    (F : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι)) :
    aeval G.x' (liftZ κ v F) = aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩)
      (map (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom F) := by
  have h : (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ').toRingHom.comp (liftZ κ v) =
      (aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩)).toRingHom.comp
        (map (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun q => ?_)
    · have e : G.x' ∘ v = algebraMap G.Φ G.Φ' ∘ G.x := funext G.compat
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, liftZ, coe_eval₂Hom, eval₂_C,
        MvPolynomial.map_C, aeval_C]
      rw [aeval_rename, e, aeval_algebraMap_apply]
    · simp [liftZ]
  exact DFunLike.congr_fun h F
end GroundTheory.Heights₂.Heights.Inter.FibreMultiHomogeneous
