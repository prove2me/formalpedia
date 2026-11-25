-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_smallSectionCount_eq_of_birational_d8b403abde42
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:05:46.614741+00:00
-- url     : https://prove2.me/submissions/17fb24c9-e6db-4f87-be90-21817e3e2da0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsBirationalCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PBirationalCoordinatesA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_mCoordIdeal_eq_83d8194d916d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_mem_chartLat_iff_b7234937320a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_exists_of_mem_chartLat_a77184435530
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_isSmallH_iff_342c06808d8c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
variable {κ : Type} [Fintype κ] {Ω Ω'' : Type} [Field Ω] [Field Ω'']
  (j : Ω'' →+* Ω) {μ : Ω} (hμ : μ ≠ 0) {x : Ix κ → Ω} {y : Ix κ → Ω''} (hx : ∀ p, x p = μ * j (y p))
include hμ hx
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
theorem _root_.solution {c : κ} (hc : x ⟨(), c⟩ ≠ 0) (A : HermLine (GlobalTheory κ)) (τ : ℕ) :
    smallSectionCount (IsSmallH (mCoordIdeal (ι := GlobalTheory κ) y) y A) (chartLat (ι := GlobalTheory κ) y A.a) τ =
      smallSectionCount (IsSmallH (mCoordIdeal (ι := GlobalTheory κ) x) x A) (chartLat (ι := GlobalTheory κ) x A.a) τ := by
  rw [mCoordIdeal_eq j hμ hx]
  set P := mCoordIdeal (ι := GlobalTheory κ) x
  unfold smallSectionCount
  congr 2
  let F : {s : chartLat (ι := GlobalTheory κ) y A.a τ // IsSmallH P y A τ (s : Ω'')} →
      {s : chartLat (ι := GlobalTheory κ) x A.a τ // IsSmallH P x A τ (s : Ω)} := fun s =>
    ⟨⟨μ ^ ((τ : ℤ) * A.a ()) * j s.1.1, (mem_chartLat_iff j hμ hx A.a τ _).2 s.1.2⟩,
      (isSmallH_iff j hμ hx P A τ _).2 s.2⟩
  refine Nat.card_congr (Equiv.ofBijective F ⟨fun s t hst => ?_, fun s => ?_⟩)
  · have h1 : μ ^ ((τ : ℤ) * A.a ()) * j s.1.1 = μ ^ ((τ : ℤ) * A.a ()) * j t.1.1 :=
      congrArg (fun u : {s : chartLat (ι := GlobalTheory κ) x A.a τ // IsSmallH P x A τ (s : Ω)} => (u.1 : Ω)) hst
    exact Subtype.ext (Subtype.ext (j.injective (mul_left_cancel₀ (zpow_ne_zero _ hμ) h1)))
  · obtain ⟨s', hs'⟩ := exists_of_mem_chartLat j hμ hx hc A.a τ s.1.2
    have hm : s' ∈ chartLat (ι := GlobalTheory κ) y A.a τ := (mem_chartLat_iff j hμ hx A.a τ s').1 (hs' ▸ s.1.2)
    have hsm : IsSmallH P y A τ s' := (isSmallH_iff j hμ hx P A τ s').1 (hs' ▸ s.2)
    exact ⟨⟨⟨s', hm⟩, hsm⟩, Subtype.ext (Subtype.ext hs')⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
