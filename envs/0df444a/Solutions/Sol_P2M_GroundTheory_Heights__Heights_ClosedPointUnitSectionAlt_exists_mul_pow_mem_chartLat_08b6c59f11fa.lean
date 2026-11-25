-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_mul_pow_mem_chartLat_08b6c59f11fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:30:16.664062+00:00
-- url     : https://prove2.me/submissions/88b27211-6fc7-4208-a5c1-48f8c901fed3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_mem_chartLat_iff_f0ffc91e5040
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_coord_mem_e0cbe1c6e1f6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_chartLat_mul_mem_accbe6f6e583
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_chartLat_pow_mem_2f024e5dc2e9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
omit [Fintype T]
namespace GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
theorem _root_.solution (t : T) (ht : y ⟨(), t⟩ ≠ 0) {x : K'}
    (hx : x ∈ chartRingZ y (fun _ => t)) : ∃ k : ℕ, x * y ⟨(), t⟩ ^ k ∈ chartLat y 1 k := by
  have hpow : ∀ l : ℕ, y ⟨(), t⟩ ^ l ∈ chartLat y 1 l := fun l => by
    simpa only [one_mul] using chartLat_pow_mem y (coord_mem y t) l
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨⟨⟩, u⟩, rfl⟩ := hx
    refine ⟨1, ?_⟩
    show y ⟨(), u⟩ / y ⟨(), t⟩ * y ⟨(), t⟩ ^ 1 ∈ chartLat y 1 1
    rw [pow_one, div_mul_cancel₀ _ ht]
    exact coord_mem y u
  | algebraMap r =>
    refine ⟨0, ?_⟩
    rw [mem_chartLat_iff]
    intro s _
    simp
  | add x z _ _ hx hz =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨l, hl⟩ := hz
    refine ⟨k + l, ?_⟩
    have e : (x + z) * y ⟨(), t⟩ ^ (k + l) =
        x * y ⟨(), t⟩ ^ k * y ⟨(), t⟩ ^ l + z * y ⟨(), t⟩ ^ l * y ⟨(), t⟩ ^ k := by ring
    rw [e]
    have h2 := chartLat_mul_mem y hl (hpow k)
    rw [Nat.add_comm] at h2
    exact add_mem (chartLat_mul_mem y hk (hpow l)) h2
  | mul x z _ _ hx hz =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨l, hl⟩ := hz
    refine ⟨k + l, ?_⟩
    have e : x * z * y ⟨(), t⟩ ^ (k + l) = (x * y ⟨(), t⟩ ^ k) * (z * y ⟨(), t⟩ ^ l) := by ring
    rw [e]
    exact chartLat_mul_mem y hk hl
end GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
