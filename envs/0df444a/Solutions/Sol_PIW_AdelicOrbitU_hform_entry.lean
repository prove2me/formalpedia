-- Prove2me | solution 1 for PIW.AdelicOrbitU.hform_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:26:42.576727+00:00
-- url     : https://prove2.me/submissions/a8a64ce0-384a-4875-ad17-203c86472d7a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry

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
open Matrix Formalism.UG
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)
namespace PIW.AdelicOrbitU
theorem _root_.solution (T : Matrix (Fin n) (Fin n) S) (i j : Fin n) :
    (cT s T * J * T) i j = hform s J (T *ᵥ Pi.single i 1) (T *ᵥ Pi.single j 1) := by
  have hv : ∀ m, T *ᵥ Pi.single m (1 : S) = fun k => T k m := fun m => by
    ext k
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  unfold cT hform
  simp only [hv, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm
end PIW.AdelicOrbitU
