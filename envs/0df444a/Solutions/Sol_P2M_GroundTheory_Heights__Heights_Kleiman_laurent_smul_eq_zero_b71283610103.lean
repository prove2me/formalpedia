-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_laurent_smul_eq_zero_b71283610103
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:36.636118+00:00
-- url     : https://prove2.me/submissions/c5789e54-50d8-440f-afce-cf203ae5f6ef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltGraded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
variable (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E]
variable {x E}
variable [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {p : Poly S N} (hp : p ∈ primeOf (S := S) x) (m : LaurentSpace x E) :
    p • m = 0 := by
  rw [primeOf_eq, RingHom.mem_ker] at hp
  rw [laurent_smul_def, laurentAct, RingHom.comp_apply]
  change (Polynomial.aeval (laurentShift x E)) (cone x p) m = 0
  rw [hp, map_zero, LinearMap.zero_apply]
end GroundTheory.Heights₂.Heights.Kleiman
