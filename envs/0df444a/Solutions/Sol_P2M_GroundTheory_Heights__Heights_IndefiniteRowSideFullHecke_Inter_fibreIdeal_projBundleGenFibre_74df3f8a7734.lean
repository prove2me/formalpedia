-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreIdeal_projBundleGenFibre_74df3f8a7734
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:14.404707+00:00
-- url     : https://prove2.me/submissions/521da0d1-8e99-40c9-8c0d-5e5ec9162480

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermOfIsPullHermInl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleFibre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projBundleMap_X_inr_7730eace2592

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution (P : Ideal (MRing ι)) [P.IsPrime] {N1 n : ℕ}
    (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    fibreIdeal Sum.inl (projBundleGenFibre P B) =
      RingHom.ker (linSubst fun q a => B a (fibreCoordEquiv ι N1 q)) := by
  have h : ∀ f, aeval (fun q : Σ k : FibreBlock (Sum.inl : K → K ⊕ Unit), fibreIdx (PBlk ι N1) Sum.inl k =>
      projBundlePt P B ⟨q.1.1, q.2⟩) f =
      algebraMap (MvPolynomial (Fin n) (FnField P)) (FractionRing (MvPolynomial (Fin n) (FnField P)))
        (linSubst (fun q a => B a (fibreCoordEquiv ι N1 q)) f) := by
    intro f
    have e : (aeval fun q : Σ k : FibreBlock (Sum.inl : K → K ⊕ Unit), fibreIdx (PBlk ι N1) Sum.inl k =>
        projBundlePt P B ⟨q.1.1, q.2⟩) =
        (IsScalarTower.toAlgHom (FnField P) (MvPolynomial (Fin n) (FnField P))
          (FractionRing (MvPolynomial (Fin n) (FnField P)))).comp
          (linSubst fun q a => B a (fibreCoordEquiv ι N1 q)) := by
      refine MvPolynomial.algHom_ext fun q => ?_
      rcases q with ⟨⟨k | u, hk⟩, j⟩
      · exact absurd ⟨k, rfl⟩ hk
      · simp only [aeval_X, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', linSubst, projBundlePt]
        exact congrArg _ (projBundleMap_X_inr P B u j)
    rw [e, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  ext f
  rw [fibreIdeal, RingHom.mem_ker]
  exact (Eq.congr_left (h f)).trans
    ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).trans RingHom.mem_ker.symm)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
