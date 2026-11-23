-- Prove2me | solution 1 for PIW.AdelicOrbitU.hform_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:08:47.590269+00:00
-- url     : https://prove2.me/submissions/b8e39a3f-b2d7-4505-b8a9-9553cca3057c

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
theorem _root_.solution (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (x y : Fin n → S) :
    s (hform s J x y) = hform s J y x := by
  have hJ' : ∀ i j, s (J i j) = J j i := fun i j => by
    have h1 := congrFun (congrFun hJ j) i
    unfold cT at h1
    simpa [Matrix.transpose_apply, Matrix.map_apply] using h1
  unfold hform
  simp only [map_sum, map_mul, hs, hJ']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end PIW.AdelicOrbitU
