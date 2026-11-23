-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.perm_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:45.168408+00:00
-- url     : https://prove2.me/submissions/00129f67-332a-43f5-9526-6acbcdf52d78

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Lemmata_PeriodicFunctions_PeriodicApplyMulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumScaling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {K : Type} [Field K]
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution (M : ℕ) (f : ℕ → ℕ) (hf : ∀ i < M, f i < M)
    (hinj : ∀ i < M, ∀ j < M, f i = f j → i = j) (g : ℕ → K) :
    ∑ i ∈ Finset.range M, g (f i) = ∑ i ∈ Finset.range M, g i := by
  have hI : Set.InjOn f (Finset.range M : Set ℕ) := fun i hi j hj h =>
    hinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) h
  rw [← Finset.sum_image (g := f) hI]
  congr 1
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (hf i (Finset.mem_range.1 hi))
  · rw [Finset.card_image_of_injOn hI]
end PI.TwistedEisensteinNonvanishing.W
