-- Prove2me | solution 1 for PIW.AdelicOrbitU.glue_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:19:43.912993+00:00
-- url     : https://prove2.me/submissions/ce07206f-6c02-45d6-9127-be6ffcd64757

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_StLamOf

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
open scoped TensorProduct
namespace PIW.AdelicOrbitU
theorem _root_.solution {S : Type} [CommRing S] {k : ℕ} (e : Fin k → S) (hid : ∀ i, e i * e i = e i)
    (hor : ∀ i j, i ≠ j → e i * e j = 0) (X Y : Fin k → S) :
    (∑ i, e i * X i) * (∑ j, e j * Y j) = ∑ i, e i * (X i * Y i) := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · calc e i * X i * (e i * Y i) = (e i * e i) * (X i * Y i) := by ring
      _ = e i * (X i * Y i) := by rw [hid i]
  · intro j _ hji
    calc e i * X i * (e j * Y j) = (e i * e j) * (X i * Y j) := by ring
      _ = 0 := by rw [hor i j (Ne.symm hji), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h
end PIW.AdelicOrbitU
