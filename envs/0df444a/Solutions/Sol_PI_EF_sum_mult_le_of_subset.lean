-- Prove2me | solution 1 for PI.EF.sum_mult_le_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:15.779701+00:00
-- url     : https://prove2.me/submissions/29e41df3-39cb-4823-a790-4ae36644fc56

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open DirichletCharacter
namespace PI.EF
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {t1 t2 : ℝ}
    (h1 : (ZerosNear χ t1).Finite) (h2 : (ZerosNear χ t2).Finite) (B : Finset ℂ)
    (hB : (B : Set ℂ) ⊆ ZerosNear χ t1 ∪ ZerosNear χ t2) :
    ∑ ρ ∈ B, (mult χ ρ : ℝ) ≤ wsum χ t1 + wsum χ t2 := by
  classical
  unfold wsum
  rw [finsum_mem_eq_finite_toFinset_sum _ h1, finsum_mem_eq_finite_toFinset_sum _ h2]
  have hsub : B ⊆ h1.toFinset ∪ h2.toFinset := by
    intro x hx
    have := hB (Finset.mem_coe.2 hx)
    simp only [Finset.mem_union, Set.Finite.mem_toFinset]
    exact this
  calc ∑ ρ ∈ B, (mult χ ρ : ℝ) ≤ ∑ ρ ∈ h1.toFinset ∪ h2.toFinset, (mult χ ρ : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ _ := by
      rw [← Finset.sum_union_inter]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
end PI.EF
