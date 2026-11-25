-- Prove2me | solution 1 for PI.VolStabW.hform_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:07:24.353811+00:00
-- url     : https://prove2.me/submissions/f6b65b14-0001-48c1-8d77-2edc12b43af3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVDx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  Matrix
variable {A : Type} [CommRing A] (s : A →+* A)
namespace PI.VolStabW
theorem _root_.solution {M a : ℕ} (Jm : Matrix (Fin M) (Fin M) A) (Y : Fin a → Fin M → A)
    (C : Matrix (Fin a) (Fin a) A) (i j : Fin a) :
    Formalism.UG.hform s Jm (fun l => ∑ k, C i k * Y k l) (Y j) =
      ∑ k, s (C i k) * Formalism.UG.hform s Jm (Y k) (Y j) := by
  calc Formalism.UG.hform s Jm (fun l => ∑ k, C i k * Y k l) (Y j)
      = ∑ p, ∑ q, ∑ k, s (C i k) * s (Y k p) * Jm p q * Y j q := by
        simp only [Formalism.UG.hform, map_sum, map_mul, Finset.sum_mul]
    _ = ∑ p, ∑ k, ∑ q, s (C i k) * s (Y k p) * Jm p q * Y j q :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ k, ∑ p, ∑ q, s (C i k) * s (Y k p) * Jm p q * Y j q := Finset.sum_comm
    _ = ∑ k, s (C i k) * Formalism.UG.hform s Jm (Y k) (Y j) := by
        simp only [Formalism.UG.hform, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ =>
          Finset.sum_congr rfl fun q _ => by ring
end PI.VolStabW
