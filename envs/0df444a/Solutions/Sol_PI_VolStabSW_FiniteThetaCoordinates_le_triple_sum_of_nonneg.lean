-- Prove2me | solution 1 for PI.VolStabSW.FiniteThetaCoordinates.le_triple_sum_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:00:48.577143+00:00
-- url     : https://prove2.me/submissions/38ae3b4b-85e8-4c3e-a0d0-926e825fecc5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
namespace PI.VolStabSW.FiniteThetaCoordinates
theorem _root_.solution {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν] (f : ι → κ → ν → ℝ)
    (hf : ∀ i j k, 0 ≤ f i j k) (i : ι) (j : κ) (k : ν) : f i j k ≤ ∑ i, ∑ j, ∑ k, f i j k := by
  calc f i j k ≤ ∑ k, f i j k :=
        Finset.single_le_sum (f := fun k => f i j k) (fun _ _ => hf _ _ _) (Finset.mem_univ k)
    _ ≤ ∑ j, ∑ k, f i j k :=
        Finset.single_le_sum (f := fun j => ∑ k, f i j k)
          (fun _ _ => Finset.sum_nonneg fun _ _ => hf _ _ _) (Finset.mem_univ j)
    _ ≤ _ :=
        Finset.single_le_sum (f := fun i => ∑ j, ∑ k, f i j k)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hf _ _ _)
          (Finset.mem_univ i)
end PI.VolStabSW.FiniteThetaCoordinates
