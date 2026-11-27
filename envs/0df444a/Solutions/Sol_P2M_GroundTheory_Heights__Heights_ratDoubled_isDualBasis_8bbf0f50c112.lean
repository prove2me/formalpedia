-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ratDoubled_isDualBasis_8bbf0f50c112
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:11:38.928421+00:00
-- url     : https://prove2.me/submissions/de05c220-9e35-47b7-b18c-aff5257b3e85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_DualModel

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
open MvPolynomial NumberField Matrix
open scoped ComplexOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (r : ℕ) :
    IsDualBasis (ratDoubled r).lattice
      (fun j : Fin (r + 1) ↦ (Pi.single j (1 / 2 : ℚ) : Fin (r + 1) → ℚ)) := by
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrFun hg i
    simpa [Finset.sum_apply, Pi.single_apply] using this
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩ v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      refine ⟨if j = i then 1 else 0, ?_⟩
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb, dotProduct_add]⟩
    | smul c x _ hx =>
      obtain ⟨a, ha⟩ := hx
      exact ⟨c * a, by rw [map_mul, ha, dotProduct_smul, Algebra.smul_def]⟩
  · intro φ hφ
    have hj : ∀ j, ∃ a : ℤ, φ j = a / 2 := by
      intro j
      obtain ⟨a, ha⟩ := hφ (Pi.single j 2) (Submodule.subset_span ⟨j, rfl⟩)
      refine ⟨Rat.ringOfIntegersEquiv a, ?_⟩
      have h1 : φ ⬝ᵥ (Pi.single j 2 : Fin (r + 1) → ℚ) = φ j * 2 := by simp
      have h2 : algebraMap (𝓞 ℚ) ℚ a = (Rat.ringOfIntegersEquiv a : ℤ) := by
        have := Rat.ringOfIntegersEquiv.symm_apply_apply a
        conv_lhs => rw [← this]
        simp
      rw [h1, h2] at ha
      linarith
    choose a ha using hj
    have hsum : φ = ∑ j, a j • (Pi.single j (1 / 2 : ℚ) : Fin (r + 1) → ℚ) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply, ha, div_eq_mul_inv]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
end GroundTheory.Heights₂.Heights
