-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_toSubSystem_update_f5a458ca714d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:32:03.4159+00:00
-- url     : https://prove2.me/submissions/2a75034c-8cef-4403-b6a2-aa8116f7418f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefProductNonneg

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
open MvPolynomial Filter
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {n : ℕ} (L : Fin n → LineBundle k x) (i : Fin n) (Y : LineBundle k x) :
    (fun j => (Function.update L i Y j).toSubSystem) =
      Function.update (fun j => (L j).toSubSystem) i Y.toSubSystem := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]
end GroundTheory.Heights₂.Heights.Kleiman
