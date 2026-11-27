-- Prove2me | solution 1 for P2M_GlobalTheory_AbLaw_cechLB_homology_equiv_trunc__da0132300080
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:51:23.500548+00:00
-- url     : https://prove2.me/submissions/cd2c4c02-f443-4f85-b64e-08ae500d74d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AcyclicSliceSecCubeOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineOpenBiInfOfLe
import Theorems.Thm_GlobalTheory_AbLaw_acyclic_comap_secCube
import Theorems.Thm_GlobalTheory_AbLaw_biInf_sumVertex
import Theorems.Thm_GlobalTheory_Cube_sliceSnd_lowerFace_lastTwoEmb
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
namespace GlobalTheory.AbLaw
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens) (κ₁ : Type) [LinearOrder κ₁] [Fintype κ₁] (U : κ₁ → Y.Opens) (κ₂ : Type) [LinearOrder κ₂] [Fintype κ₂] (W : κ₂ → Y.Opens), M.IsLB → IsSeparated f → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ⨆ i, U i = ⊤ → ⨆ j, W j = ⊤ → (∀ i V, IsAffineOpen V → IsAffineOpen (U i ⊓ V)) → (∀ j V, IsAffineOpen V → IsAffineOpen (W j ⊓ V)) → (∀ i j, IsAffineOpen (U i ⊓ W j)) → ∀ n, Nonempty ((cechLB f M D).homology n ≃ₗ[R] (cubeComplex (Cube.trunc₂ (secCube f M fun u : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex u)))).homology (n + 2)) := by
  intro R _ Y f M κ _ _ D κ₁ _ _ U κ₂ _ _ W hM hf hD cD cU cW hU hW hUW n
  have hY : Y.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let E : (κ₁ ⊕ₗ κ₂) ⊕ₗ κ → Y.Opens := fun u =>
    Sum.elim (fun v : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex v)) D (ofLex u)
  have hE : ∀ i V, IsAffineOpen V → IsAffineOpen (E i ⊓ V) := by
    rintro ((i | j) | k) V hV
    · exact hU i V hV
    · exact hW j V hV
    · exact (hD k).inf hV
  let A := secCube f M E
  let e₁ := trunc₃HomologyIsoDropLast A (fun s t ⟨i, hi⟩ ⟨j, hj⟩ =>
    acyclic_comap_secCube f hM E hE (Cube.inrEmb _ _) cD
      ((Cube.sumVertex s t).map (Cube.inlEmb _ _).toEmbedding) (hUW i j)
      (le_inf
        (iInf₂_le (toLex (Sum.inl (toLex (Sum.inl i))))
          (Finset.mem_map_of_mem _ (Cube.inl_mem_sumVertex.2 hi)))
        (iInf₂_le (toLex (Sum.inl (toLex (Sum.inr j))))
          (Finset.mem_map_of_mem _ (Cube.inr_mem_sumVertex.2 hj))))
      _ (fun _ _ h => Cube.sumVertex_mono (subset_refl _) h) fun _ => rfl) (n + 2)
  let e₂ := trunc₃HomologyIsoDropFirst A (fun t w _ ⟨k, hk⟩ =>
    acyclic_comap_secCube f hM E hE (Cube.firstEmb _ _ _) cU
      ((Cube.sumVertex t w).map (Cube.lastTwoEmb _ _ _).toEmbedding) (hD k)
      (iInf₂_le (toLex (Sum.inr k)) (Finset.mem_map_of_mem _ (Cube.inr_mem_sumVertex.2 hk)))
      (fun s => Cube.sumVertex (Cube.sumVertex s t) w)
      (fun _ _ h => Cube.sumVertex_mono (Cube.sumVertex_mono h (subset_refl _)) (subset_refl _))
      fun s => (Cube.map_lastTwoEmb_union s t w).symm) (n + 2)
  let e₃ := trunc₂HomologyIsoSnd (Cube.lowerFace (Cube.lastTwoEmb κ₁ κ₂ κ) A) (fun w ⟨k, hk⟩ =>
    acyclic_comap_secCube f hM E hE ((Cube.inlEmb κ₂ κ).trans (Cube.lastTwoEmb κ₁ κ₂ κ)) cW
      (w.map (Cube.inrEmb _ _).toEmbedding) (hD k)
      (iInf₂_le (toLex (Sum.inr k)) (Finset.mem_map_of_mem _ hk))
      (fun t => (Cube.sumVertex t w).map (Cube.lastTwoEmb κ₁ κ₂ κ).toEmbedding)
      (fun _ _ h => Finset.map_subset_map.2 (Cube.sumVertex_mono h (subset_refl _)))
      fun t => by
        rw [Cube.sumVertex, Finset.map_union, Finset.map_map, Finset.map_map, Finset.union_comm]
        rfl) n
  let e₄ : Cube.sliceFst A ∅ ≅ secCube f M fun u : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex u) :=
    comapSecCubeIso f M E _ _ (fun _ _ h => Cube.sumVertex_mono h (subset_refl _)) fun t => by
      rw [biInf_sumVertex]
      simp [E]
  let e₅ : Cube.sliceSnd A (Cube.sumVertex ∅ ∅) ≅ secCube f M D :=
    comapSecCubeIso f M E _ _ (fun _ _ h => Cube.sumVertex_mono (subset_refl _) h) fun t => by
      rw [biInf_sumVertex]
      simp [E, Cube.sumVertex]
  exact ⟨((cechHomologyMapIso
    (eqToIso (Cube.sliceSnd_lowerFace_lastTwoEmb A ∅) ≪≫ e₅) n).symm ≪≫ e₃.symm ≪≫ e₂.symm ≪≫ e₁ ≪≫
      cubeHomologyMapIso (Cube.trunc₂Iso e₄.hom fun _ _ _ _ =>
        ConcreteCategory.bijective_of_isIso (e₄.hom.app _)) (n + 2)).toLinearEquiv⟩
end GlobalTheory.AbLaw
