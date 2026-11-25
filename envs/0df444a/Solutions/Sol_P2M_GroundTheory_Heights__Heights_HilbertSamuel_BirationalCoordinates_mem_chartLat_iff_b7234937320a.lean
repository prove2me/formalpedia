-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_mem_chartLat_iff_b7234937320a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:54:09.391748+00:00
-- url     : https://prove2.me/submissions/85c11ade-d09f-41c0-809f-90c3a42f4ad3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsBirationalCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PBirationalCoordinatesA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_chartRingZ_eq_335699c6df6a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
variable {κ : Type} [Fintype κ] {Ω Ω'' : Type} [Field Ω] [Field Ω'']
  (j : Ω'' →+* Ω) {μ : Ω} (hμ : μ ≠ 0) {x : Ix κ → Ω} {y : Ix κ → Ω''} (hx : ∀ p, x p = μ * j (y p))
include hμ hx
omit [Fintype κ]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
theorem _root_.solution (a : Unit → ℤ) (τ : ℕ) (s' : Ω'') :
    μ ^ ((τ : ℤ) * a ()) * j s' ∈ chartLat (ι := GlobalTheory κ) x a τ ↔ s' ∈ chartLat (ι := GlobalTheory κ) y a τ := by
  have hne : ∀ c' : Unit → κ, (∀ k, x ⟨k, c' k⟩ ≠ 0) ↔ (∀ k, y ⟨k, c' k⟩ ≠ 0) := fun c' =>
    forall_congr' fun k => by rw [hx, mul_ne_zero_iff, map_ne_zero]; exact and_iff_right hμ
  have hval : ∀ c' : Unit → κ, μ ^ ((τ : ℤ) * a ()) * j s' * ∏ k, x ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k)) =
      j (s' * ∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k))) := by
    intro c'
    simp only [Fintype.prod_unique, hx, map_mul, map_zpow₀, mul_zpow]
    have h1 : μ ^ ((τ : ℤ) * a ()) * μ ^ (-((τ : ℤ) * a default)) = 1 := by
      rw [← zpow_add₀ hμ]
      simp
    linear_combination (j s' * j (y ⟨default, c' default⟩) ^ (-((τ : ℤ) * a default))) * h1
  change (∀ c' : Unit → κ, _ → _) ↔ (∀ c' : Unit → κ, _ → _)
  refine forall_congr' fun c' => ?_
  rw [hne c', hval c', chartRingZ_eq j hμ hx c', Subalgebra.mem_map]
  refine imp_congr_right fun _ => ⟨fun ⟨t, ht, he⟩ => ?_, fun h => ⟨_, h, rfl⟩⟩
  rw [RingHom.toIntAlgHom_apply] at he
  rwa [j.injective he] at ht
end GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
