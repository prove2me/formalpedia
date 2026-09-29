-- Prove2me | solution 1 for WeierstrassProjModel.kw_pcmpin_chartIso_inv_cover_fst_over
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e95ed0ee-c560-5c9a-a7cf-61c23e9c2c53

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.Pullbacks
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_pcmpin_chartIso_inv_cover_fst_over

set_option autoImplicit false
set_option maxHeartbeats 25600000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

set_option quotPrecheck false in
local notation "coverE" => (projModelAffineOpenCoverCR R W.toProjective).openCover

theorem aux_chartIso_inv_fst (i j : Fin 3) :
    (kwProjPullbackChartIsoCR R W.toProjective i j).inv
        ≫ pullback.fst _ _
      = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := 𝒜 i) (B := 𝒜 j))) := by
  simp only [kwProjPullbackChartIsoCR, Iso.trans_inv, Category.assoc]
  rw [pullback.congrHom_inv]
  erw [pullback.lift_fst]
  rw [Category.comp_id]
  exact pullbackSpecIso_inv_fst R (𝒜 i) (𝒜 j)

theorem aux_liftAddMor_fst (i j : Fin 3) :
    (kwProjPullbackChartIsoCR R W.toProjective i j).inv
        ≫ (kwProjPullbackOpenCoverCR R W.toProjective).f (i, j)
        ≫ pullback.fst _ _
      = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := 𝒜 i) (B := 𝒜 j)))
          ≫ (coverE).f i := by
  simp only [kwProjPullbackOpenCoverCR, Scheme.Pullback.openCoverOfLeftRight_f]
  erw [pullback.lift_fst]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (coverE).f i) (aux_chartIso_inv_fst W i j))

theorem solution (ij : Fin 3 × Fin 3) :
    (kwProjPullbackChartIsoCR R W.toProjective ij.1 ij.2).inv
        ≫ (kwProjPullbackOpenCoverCR R W.toProjective).f ij
        ≫ pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        ≫ projModelStrCR W.toProjective
      = Spec.map (CommRingCat.ofHom (algebraMap R ((𝒜 ij.1) ⊗[R] (𝒜 ij.2)))) := by
  obtain ⟨i, j⟩ := ij

  have h1 := aux_liftAddMor_fst W i j

  have h2 : (coverE).f i ≫ projModelStrCR W.toProjective
      = Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 i))) :=
    kw_pbac_awayι_comp_projModelStrCR R W.toProjective i

  have h3 : (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := 𝒜 i) (B := 𝒜 j)).comp
        (algebraMap R (𝒜 i)) = algebraMap R ((𝒜 i) ⊗[R] (𝒜 j)) := by
    ext r
    show (algebraMap R (𝒜 i) r) ⊗ₜ[R] 1 = algebraMap R ((𝒜 i) ⊗[R] (𝒜 j)) r
    rw [Algebra.TensorProduct.algebraMap_apply]

  calc (kwProjPullbackChartIsoCR R W.toProjective i j).inv
        ≫ (kwProjPullbackOpenCoverCR R W.toProjective).f (i, j)
        ≫ pullback.fst _ _ ≫ projModelStrCR W.toProjective
      = ((kwProjPullbackChartIsoCR R W.toProjective i j).inv
        ≫ (kwProjPullbackOpenCoverCR R W.toProjective).f (i, j)
        ≫ pullback.fst _ _) ≫ projModelStrCR W.toProjective := by
        simp only [Category.assoc]
    _ = (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := 𝒜 i) (B := 𝒜 j)))
          ≫ (coverE).f i) ≫ projModelStrCR W.toProjective :=
        congrArg (· ≫ projModelStrCR W.toProjective) h1
    _ = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := 𝒜 i) (B := 𝒜 j)))
          ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 i))) :=
        (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h2)
    _ = Spec.map (CommRingCat.ofHom (algebraMap R ((𝒜 i) ⊗[R] (𝒜 j)))) := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h3]

end

end S_WeierstrassProjModel_kw_pcmpin_chartIso_inv_cover_fst_over
end P2MW
export P2MW.S_WeierstrassProjModel_kw_pcmpin_chartIso_inv_cover_fst_over (solution)
