-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:38:42.654663+00:00
-- url     : https://prove2.me/submissions/3bd25bae-4c38-4635-8c47-4151d1d75426

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
namespace PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
theorem _root_.solution {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℕ → ℕ → M)
    (hg : ∀ i j, N < i + j → g i j = 0) :
    ∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (n + 1), g m (n - m) =
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), g i j := by
  have key := Finset.sum_Ico_Ico_comm 0 (N + 1) (fun m n => g m (n - m))
  simp only [Finset.range_eq_Ico]
  rw [← key]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_Ico] at hi
  have e : ∑ j ∈ Finset.Ico i (N + 1), g i (j - i) = ∑ j ∈ Finset.range (N + 1 - i), g i j := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
  rw [e, ← Finset.range_eq_Ico]
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  · intro j hj hj'
    simp only [Finset.mem_range] at hj hj'
    exact hg i j (by omega)
end PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
