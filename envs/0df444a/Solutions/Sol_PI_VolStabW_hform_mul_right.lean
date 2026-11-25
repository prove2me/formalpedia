-- Prove2me | solution 1 for PI.VolStabW.hform_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:03:15.931216+00:00
-- url     : https://prove2.me/submissions/ba4aada6-49b6-41af-b5e0-b6bf5a9e9722

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
    Formalism.UG.hform s Jm (Y i) (fun l => ∑ k, C j k * Y k l) =
      ∑ k, Formalism.UG.hform s Jm (Y i) (Y k) * C j k := by
  calc Formalism.UG.hform s Jm (Y i) (fun l => ∑ k, C j k * Y k l)
      = ∑ p, ∑ q, ∑ k, s (Y i p) * Jm p q * (C j k * Y k q) := by
        simp only [Formalism.UG.hform, Finset.mul_sum]
    _ = ∑ p, ∑ k, ∑ q, s (Y i p) * Jm p q * (C j k * Y k q) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ k, ∑ p, ∑ q, s (Y i p) * Jm p q * (C j k * Y k q) := Finset.sum_comm
    _ = ∑ k, Formalism.UG.hform s Jm (Y i) (Y k) * C j k := by
        simp only [Formalism.UG.hform, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ =>
          Finset.sum_congr rfl fun q _ => by ring
end PI.VolStabW
