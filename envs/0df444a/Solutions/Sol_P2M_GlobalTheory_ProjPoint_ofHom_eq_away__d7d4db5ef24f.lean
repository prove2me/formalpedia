-- Prove2me | solution 1 for P2M_GlobalTheory_ProjPoint_ofHom_eq_away__d7d4db5ef24f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:31:36.831508+00:00
-- url     : https://prove2.me/submissions/1fa8ecfc-629e-4372-b042-447b045c5453

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_AwayLiftCompFromZeroRingHom
import Theorems.Thm_GlobalTheory_ProjPoint_ofHom_toSpecZero
import Theorems.Thm_P2M_GlobalTheory_ProjPoint_SpecMap_ofHom_eq_away__97605d53820a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc] GlobalTheory.ProjPoint.ofHom_toSpecZero
attribute [reassoc] GlobalTheory.ProjPoint.SpecMap_ofHom_eq_awayι

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.ProjPoint
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {B C : Type u} [CommRing B] [CommRing C]
namespace GlobalTheory.ProjPoint
theorem _root_.solution (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤)
    {f : A} {n : ℕ} (hn : 0 < n) (hf : f ∈ 𝒜 n) (hu : IsUnit (φ f)) :
    ofHom 𝒜 φ hφ = Spec.map (CommRingCat.ofHom (awayLift 𝒜 φ f hu)) ≫ Proj.awayι 𝒜 f hf hn := by
  simpa using SpecMap_ofHom_eq_awayι 𝒜 φ hφ (RingHom.id B) hn hf hu
end GlobalTheory.ProjPoint
