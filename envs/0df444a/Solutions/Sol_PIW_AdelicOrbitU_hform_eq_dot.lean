-- Prove2me | solution 1 for PIW.AdelicOrbitU.hform_eq_dot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:22.396652+00:00
-- url     : https://prove2.me/submissions/b7aa2b47-9389-435f-ab02-425451d319c2

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
theorem _root_.solution (x y : Fin n → S) :
    hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  unfold hform
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
end PIW.AdelicOrbitU
