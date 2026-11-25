-- Prove2me | solution 1 for PIW.AdelicOrbitU.local_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:21:58.277716+00:00
-- url     : https://prove2.me/submissions/cf4a178f-2635-4e0f-8966-32ffe4167e8d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_LocalSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped RestrictedProduct
namespace PIW.AdelicOrbitU
theorem _root_.solution {A : Type} [CommRing A] [IsLocalRing A] {k : ℕ} (a f : Fin k → A)
    (h : ∑ i, a i * f i = 1) : ∃ i, IsUnit (f i) := by
  by_contra hne
  push_neg at hne
  have hmem : ∀ i, a i * f i ∈ IsLocalRing.maximalIdeal A := fun i =>
    Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).mpr (hne i))
  have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← h]
    exact Ideal.sum_mem _ fun i _ => hmem i
  exact (IsLocalRing.mem_maximalIdeal _).mp h1 isUnit_one
end PIW.AdelicOrbitU
