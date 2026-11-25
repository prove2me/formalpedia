-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_rep_of_mem_71352e8bebca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:52:48.478879+00:00
-- url     : https://prove2.me/submissions/64b8a8a8-5c22-4515-afe6-cd1a4b90fb54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_isMultiHomog_iff_c75df70a60fa


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
omit [Fintype K]
namespace GroundTheory.Heights₂.Heights.CoordinateConeArithVar
theorem _root_.solution [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {x : Ω} (hx : x ∈ ratioField y c) :
    ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧
      aeval (ratioPt y c) h ≠ 0 ∧ aeval (ratioPt y c) g = x * aeval (ratioPt y c) h := by
  classical
  suffices H : ∃ (d : K → ℕ) (g h : MRing ι),
      IsWeightedHomogeneous (NumbersDVR.blockWeight ι) g d ∧
      IsWeightedHomogeneous (NumbersDVR.blockWeight ι) h d ∧
      aeval (ratioPt y c) h ≠ 0 ∧ aeval (ratioPt y c) g = x * aeval (ratioPt y c) h by
    obtain ⟨d, g, h, hg, hh, h0, he⟩ := H
    exact ⟨d, g, h, (Bridge.isMultiHomog_iff g d).mp hg, (Bridge.isMultiHomog_iff h d).mp hh, h0, he⟩
  have hz : ∀ k, ratioPt y c ⟨k, c k⟩ = 1 := fun k ↦ div_self (hc k)
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    refine ⟨NumbersDVR.blockWeight ι p, X p, X ⟨p.1, c p.1⟩, isWeightedHomogeneous_X _ _ _,
      isWeightedHomogeneous_X _ _ _, ?_, ?_⟩
    · rw [aeval_X, hz]
      exact one_ne_zero
    · rw [aeval_X, aeval_X, hz, mul_one]
      rfl
  | algebraMap q =>
    refine ⟨0, C q.num, C (q.den : ℤ), isWeightedHomogeneous_C _ _, isWeightedHomogeneous_C _ _, ?_, ?_⟩
    · simp
    · have hd : ((q.den : ℤ) : Ω) ≠ 0 := by exact_mod_cast q.den_nz
      rw [aeval_C, aeval_C, algebraMap_int_eq, eq_intCast, eq_intCast, eq_ratCast, Rat.cast_def]
      push_cast at hd ⊢
      field_simp
  | add x₁ x₂ _ _ ih₁ ih₂ =>
    obtain ⟨d₁, g₁, h₁, hg₁, hh₁, n₁, e₁⟩ := ih₁
    obtain ⟨d₂, g₂, h₂, hg₂, hh₂, n₂, e₂⟩ := ih₂
    have hg₂₁ := hg₂.mul hh₁
    rw [add_comm d₂ d₁] at hg₂₁
    refine ⟨d₁ + d₂, g₁ * h₂ + g₂ * h₁, h₁ * h₂, (hg₁.mul hh₂).add hg₂₁, hh₁.mul hh₂, ?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero n₁ n₂
    · rw [map_add, map_mul, map_mul, map_mul, e₁, e₂]
      ring
  | inv x _ ih =>
    obtain ⟨d, g, h, hg, hh, n, e⟩ := ih
    by_cases hx0 : x = 0
    · refine ⟨d, 0, h, isWeightedHomogeneous_zero _ _ _, hh, n, ?_⟩
      simp [hx0]
    · have ng : aeval (ratioPt y c) g ≠ 0 := by
        rw [e]
        exact mul_ne_zero hx0 n
      refine ⟨d, h, g, hh, hg, ng, ?_⟩
      rw [e, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
  | mul x₁ x₂ _ _ ih₁ ih₂ =>
    obtain ⟨d₁, g₁, h₁, hg₁, hh₁, n₁, e₁⟩ := ih₁
    obtain ⟨d₂, g₂, h₂, hg₂, hh₂, n₂, e₂⟩ := ih₂
    refine ⟨d₁ + d₂, g₁ * g₂, h₁ * h₂, hg₁.mul hg₂, hh₁.mul hh₂, ?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero n₁ n₂
    · rw [map_mul, map_mul, e₁, e₂]
      ring
end GroundTheory.Heights₂.Heights.CoordinateConeArithVar
