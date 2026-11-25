-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_iff_of_loc_5644dbfd8277
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:09.931695+00:00
-- url     : https://prove2.me/submissions/db256256-19af-45c6-80d9-699377387927

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_inv_pow_smul_mem_89d3c1ffc87f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
variable {S : Type*} [SetLike S Ω] [SubringClass S Ω]
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (A : S) (X Y : AddSubgroup E) {u f : Ω} (j : ℕ)
    (hu0 : u ≠ 0) (huA : u ∈ A) (hg : u ^ j * f ∈ A) (hXA : ∀ a ∈ A, ∀ e ∈ X, a • e ∈ X)
    (hXY : X ≤ Y) (hYu : ∀ e ∈ Y, u⁻¹ • e ∈ Y) (hYX : ∀ e ∈ Y, ∃ k : ℕ, u ^ k • e ∈ X) (e : E) :
    (∃ n : ℕ, (u ^ (j + 1) * f) ^ n • e ∈ X) ↔ ∃ n : ℕ, f ^ n • e ∈ Y := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h1 : f ^ n • e = ((u⁻¹) ^ ((j + 1) * n)) • ((u ^ (j + 1) * f) ^ n • e) := by
      rw [smul_smul]
      congr 1
      rw [mul_pow, ← pow_mul, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hu0, one_pow, one_mul]
    rw [h1]
    exact inv_pow_smul_mem Y hYu _ _ (hXY hn)
  · rintro ⟨n, hn⟩
    obtain ⟨k, hk⟩ := hYX _ hn
    refine ⟨n + k, ?_⟩
    have h1 : (u ^ (j + 1) * f) ^ (n + k) • e =
        ((u ^ j * f) ^ k * u ^ ((j + 1) * n)) • (u ^ k • f ^ n • e) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [h1]
    exact hXA _ (mul_mem (pow_mem hg _) (pow_mem huA _)) _ hk
end GroundTheory.Heights₂.Heights.Model
