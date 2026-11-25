-- Prove2me | solution 1 for P2M_GlobalTheory_AbCoh_pre__surjective_and_ker_5a1e5300be4a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:56:05.002271+00:00
-- url     : https://prove2.me/submissions/d52c9938-210d-4ac2-ab3f-cc4582af283a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullSurjectiveAndKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveDeformationAffineSections
import Theorems.Thm_GlobalTheory_AbCoh_mem_map_ann_iff
import Theorems.Thm_GlobalTheory_AbCoh_mem_map_span_singleton_iff
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CechDR_secPull_surjective_and_ker


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
theorem _root_.solution : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) [IsAffineHom φ] [IsAffineHom φ₀], SmallExt t σ σ₀ → Flat s → ∀ U : AffOp X, Function.Surjective (preα φ s s' U) ∧ (∀ b, preα φ s s' U b = 0 ↔ ∃ c, b = t • c) ∧ Function.Surjective (preα φ₀ s s₀ U) ∧ ∀ b : (OAff s).obj U, preα φ₀ s s₀ U b = 0 ↔ t • b = 0 := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ _ _ hE hF U
  obtain ⟨hσ, hk, hσ₀, hk₀⟩ := hE
  have A := secPull_surjective_and_ker R R' (Ideal.span {t}) σ hσ hk X' X s' s φ h (prePair φ U.unop) rfl
  have B := secPull_surjective_and_ker R R₀ (RingHom.ker σ₀) σ₀ hσ₀ rfl X₀ X s₀ s φ₀ h₀
    (prePair φ₀ U.unop) rfl
  haveI : Flat s := hF
  have hfl : (algebraMap R (Sec s U.unop.1)).Flat := by
    change ((s.appLE ⊤ U.unop.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).Flat
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv))
      (Flat.flat_appLE s (isAffineOpen_top _) U.unop.2 le_top)
  haveI : Module.Flat R (Sec s U.unop.1) := hfl
  exact ⟨A.1, fun b ↦ (A.2 b).trans (mem_map_span_singleton_iff t b), B.1,
    fun b ↦ (B.2 b).trans (mem_map_ann_iff t _ (fun a ↦ RingHom.mem_ker.trans (hk₀ a)) b)⟩
end GlobalTheory.AbCoh
