-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Ar_ProjCoord_pt_away__eq_854980b86607
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:58:40.292986+00:00
-- url     : https://prove2.me/submissions/a28ff6b1-92de-45ff-8780-e15d3bdeff7b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_ZarhinBundleKernelFirstCoordEquations
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_ProjCoord_awayEval_comp_awayMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.ProjCoord
open HomogeneousLocalization
variable {σ A Ω : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [Field Ω]
namespace GlobalTheory.CompanionTheory.Ar.ProjCoord
theorem _root_.solution (ψ : A →+* Ω) {f g : A} {d e : ℕ} (hd : f ∈ 𝒜 d) (he : g ∈ 𝒜 e)
    (d0 : 0 < d) (e0 : 0 < e) (hf : ψ f ≠ 0) (hg : ψ g ≠ 0) :
    CptModel.pt (awayEval 𝒜 ψ f hf) ≫ Proj.awayι 𝒜 f hd d0 =
      CptModel.pt (awayEval 𝒜 ψ g hg) ≫ Proj.awayι 𝒜 g he e0 := by
  have h0 : ψ (f * g) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero hf hg
  rw [← awayEval_comp_awayMap 𝒜 ψ hd he rfl hf h0,
    ← awayEval_comp_awayMap 𝒜 ψ he hd (mul_comm f g) hg h0]
  unfold CptModel.pt
  rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, Category.assoc,
    Category.assoc, Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]
  rfl
end GlobalTheory.CompanionTheory.Ar.ProjCoord
