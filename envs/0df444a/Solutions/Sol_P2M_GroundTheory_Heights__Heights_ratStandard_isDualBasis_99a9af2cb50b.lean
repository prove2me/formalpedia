-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ratStandard_isDualBasis_99a9af2cb50b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:11:51.410532+00:00
-- url     : https://prove2.me/submissions/09794df9-d5ac-429a-b074-4e191ea37e5c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_DualModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linearIndependent_int_single_7c9470833efe

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
    IsDualBasis (HermLattice.standard ℚ (r + 1)).lattice
      (fun j : Fin (r + 1) ↦ (Pi.single j (1 : ℚ) : Fin (r + 1) → ℚ)) := by
  refine ⟨linearIndependent_int_single _, le_antisymm ?_ ?_⟩
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
    have hj : ∀ j, ∃ a : ℤ, φ j = a := by
      intro j
      obtain ⟨a, ha⟩ := hφ (Pi.single j 1) (Submodule.subset_span ⟨j, rfl⟩)
      refine ⟨Rat.ringOfIntegersEquiv a, ?_⟩
      have h1 : φ ⬝ᵥ (Pi.single j 1 : Fin (r + 1) → ℚ) = φ j := by simp
      rw [← h1, ← ha]
      have := (Rat.ringOfIntegersEquiv.symm_apply_apply a)
      conv_lhs => rw [← this]
      simp
    choose a ha using hj
    have hsum : φ = ∑ j, a j • (Pi.single j (1 : ℚ) : Fin (r + 1) → ℚ) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply, ha]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
end GroundTheory.Heights₂.Heights
