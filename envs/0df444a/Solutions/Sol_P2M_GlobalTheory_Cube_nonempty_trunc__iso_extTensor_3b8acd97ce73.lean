-- Prove2me | solution 1 for P2M_GlobalTheory_Cube_nonempty_trunc__iso_extTensor_3b8acd97ce73
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:02:39.9298+00:00
-- url     : https://prove2.me/submissions/a390ac40-f3cb-4e00-bfbe-d9b466c1ed5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
import Theorems.Thm_P2M_GlobalTheory_Cube_trunc_Incl_bijective_15000a487b45


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
open GlobalTheory.Cube
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {K : Type u} [CommRing K]
variable [Finite ι] [Finite κ] (A : Cube.{v} ι K) (B : Cube.{v} κ K)
omit [Finite ι] [Finite κ]
variable {A B}
variable (A B)
namespace GlobalTheory.Cube
theorem _root_.solution (C : Cube.{v} (ι ⊕ₗ κ) K)
    (μ : ∀ (s : Finset ι) (t : Finset κ), s.Nonempty → t.Nonempty →
      A.obj s ⊗[K] B.obj t →ₗ[K] C.obj (sumVertex s t))
    (hμ : ∀ s t hs ht, Function.Bijective (μ s t hs ht))
    (hnat : ∀ {s s' : Finset ι} {t t' : Finset κ} (hs : s.Nonempty) (ht : t.Nonempty)
      (h : s ⊆ s') (h' : t ⊆ t') (a : A.obj s) (b : B.obj t),
      μ s' t' (hs.mono h) (ht.mono h') (res A h a ⊗ₜ res B h' b) =
        res C (sumVertex_mono h h') (μ s t hs ht (a ⊗ₜ b))) :
    Nonempty (trunc₂ C ≅ trunc₂ (extTensor A B)) := by
  classical
  have hP := ordConnected_partsIn (inlEmb ι κ) (inrEmb ι κ) ordConnected_nonempty
    ordConnected_nonempty
  have hb : ∀ {w w' : Finset (ι ⊕ₗ κ)} (_ : w = w') (h : w ⊆ w'),
      Function.Bijective (res C h) := by
    rintro w _ rfl h
    have : ⇑(res C h) = id := funext (res_self C h)
    rw [this]
    exact Function.bijective_id
  let ν : ∀ w, w ∈ partsIn (inlEmb ι κ) (inrEmb ι κ) {s | s.Nonempty} {t | t.Nonempty} →
      (extTensor A B).obj w →ₗ[K] C.obj w := fun w hw =>
    res C (sumVertex_part w).le ∘ₗ μ _ _ hw.1 hw.2
  have hν : ∀ {w w'} (h : w ⊆ w') hw hw' (x : (extTensor A B).obj w),
      ν w' hw' (res (extTensor A B) h x) = res C h (ν w hw x) := fun {w w'} h hw hw' x => by
    have : ν w' hw' ∘ₗ res (extTensor A B) h = res C h ∘ₗ ν w hw :=
      TensorProduct.ext' fun a b => (congrArg (res C (sumVertex_part w').le)
        (hnat hw.1 hw.2 (monotone_part _ h) (monotone_part _ h) a b)).trans
        ((res_res C _ _ _).trans (res_res C _ _ _).symm)
    exact LinearMap.congr_fun this x
  let φ : supp (extTensor A B) _ hP ⟶ C :=
    homMk (fun w => if hw : _ then ν w hw ∘ₗ (suppEquiv _ hP hw).toLinearMap else 0)
      fun {w w'} h x => by
        by_cases hw : w ∈ partsIn (inlEmb ι κ) (inrEmb ι κ) {s | s.Nonempty} {t | t.Nonempty}
        · have hw' := isUpperSet_partsIn_nonempty _ _ h hw
          simp only [dif_pos hw, dif_pos hw', LinearMap.comp_apply, LinearEquiv.coe_coe]
          rw [suppEquiv_res h hw hw', hν h hw hw']
        · have := subsingleton_supp (extTensor A B) hP hw
          rw [Subsingleton.elim x 0]
          simp only [map_zero]
  refine ⟨(trunc₂Iso φ fun s t hs ht => ?_).symm ≪≫
    trunc₂Iso (trunc₂Incl (extTensor A B)) fun s t hs ht => trunc₂Incl_bijective _ hs ht⟩
  have hw : sumVertex s t ∈ partsIn (inlEmb ι κ) (inrEmb ι κ) {s | s.Nonempty} {t | t.Nonempty} := by
    simp [hs, ht]
  have : (φ.app (sumVertex s t)).hom = ν _ hw ∘ₗ (suppEquiv _ hP hw).toLinearMap := dif_pos hw
  rw [this]
  exact ((hb (sumVertex_part _) _).comp (hμ _ _ hw.1 hw.2)).comp (suppEquiv _ hP hw).bijective
end GlobalTheory.Cube
