-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.sqrt_nsq_add_ncSum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:37:04.155253+00:00
-- url     : https://prove2.me/submissions/817b2193-06fe-45fe-9110-79ed1b83186e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_LayerSpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_WeightBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sqrt_nsq_add_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sqrt_nsq_sum_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {j : ℕ} {ω : Fin n → ℝ} (hω : IsNCSum ε j ω)
    (x : Fin n → ℝ) :
    √(nsq (x + ω)) ≤ √(nsq x) + √2 * j := by
  obtain ⟨γ, hγ, rfl⟩ := hω
  have hroot : ∀ a b : Fin n, a ≠ b → nsq (root a b) = 2 := by
    intro a b hne
    unfold nsq dot
    rw [Fintype.sum_eq_add a b hne]
    · norm_num [root, Pi.single_apply, hne, hne.symm]
    · intro c hc
      simp [root, Pi.single_apply, hc.1, hc.2]
  have hr : ∀ i, √(nsq (root (γ i).1 (γ i).2)) ≤ √2 := fun i => by
    have hne : (γ i).1 ≠ (γ i).2 := fun h => hγ i (congrArg ε h)
    exact le_of_eq (by rw [hroot _ _ hne])
  calc √(nsq (x + ∑ i, root (γ i).1 (γ i).2))
      ≤ √(nsq x) + √(nsq (∑ i, root (γ i).1 (γ i).2)) := sqrt_nsq_add_le _ _
    _ ≤ √(nsq x) + ∑ i, √(nsq (root (γ i).1 (γ i).2)) :=
        add_le_add le_rfl (sqrt_nsq_sum_le _ _)
    _ ≤ √(nsq x) + ∑ _i : Fin j, √2 := add_le_add le_rfl (Finset.sum_le_sum fun i _ => hr i)
    _ = √(nsq x) + √2 * j := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
end ReciprocityTheory.ChartRestriction.DS
