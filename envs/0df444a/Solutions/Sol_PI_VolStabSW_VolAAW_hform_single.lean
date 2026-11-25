-- Prove2me | solution 1 for PI.VolStabSW.VolAAW.hform_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:08.175629+00:00
-- url     : https://prove2.me/submissions/66a9370f-35c4-44ce-bc1b-41a1cac74a69

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E)
namespace PI.VolStabSW.VolAAW
theorem _root_.solution {A : Type} [CommRing A] {M : ℕ} (s : A →+* A) (Am : Matrix (Fin M) (Fin M) A)
    (i j : Fin M) (x y : A) :
    Formalism.UG.hform s Am (Pi.single i x) (Pi.single j y) = s x * Am i j * y := by
  unfold Formalism.UG.hform
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      simp [hj']
    · simp
  · intro i' _ hi'
    simp [hi']
  · simp
end PI.VolStabSW.VolAAW
