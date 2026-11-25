-- Prove2me | solution 1 for PI.VolStabSW.hSes_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:56:02.291469+00:00
-- url     : https://prove2.me/submissions/e8940787-28a8-478a-9236-c2f0e15a4280

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_HformSmulRight
import Theorems.Thm_PI_VolStabSW_hSes_apply

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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
variable {E : Type} [Field E] {M : ℕ}
variable [StarRing E]
namespace PI.VolStabSW
theorem _root_.solution (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, starRingEnd E (J j i) = J i j)
    (x y : Fin M → E) : star (hSes J x y) = hSes J y x := by
  rw [hSes_apply, hSes_apply]
  show starRingEnd E _ = _
  simp only [Formalism.UG.hform, map_sum, map_mul, starRingEnd_self_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring
end PI.VolStabSW
