-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_mem_sub_of_isVeryAmpleBy_4e23af4f9328
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:58:24.470006+00:00
-- url     : https://prove2.me/submissions/70fad887-243e-424e-88cf-a4b3c4b88087

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionSystems
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle

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
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
  (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
  {Nb : LineBundle k x} {r : ℕ} {h : Fin (r + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hV : IsVeryAmpleBy Nb.toSubSystem h) (l : Fin (r + 1)) (I : Chart x) :
    h l ∈ Nb.sub I :=
  (Submodule.mem_iInf _).mp (hV.mem_secs l) I
end GroundTheory.Heights₂.Heights.Kleiman
