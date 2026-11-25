-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwM_val_mk_6383b3b12662
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:19:48.642451+00:00
-- url     : https://prove2.me/submissions/4a8367b5-a044-4442-93ae-aac7fac10d13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitObj

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
open MvPolynomial Pointwise AddMonoidAlgebra
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (x : Fin (N + 1) → Ω) {r : ℕ} (η : Fin (r + 1) → Ω)
variable {x}
variable {η}
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace TwM
theorem _root_.solution {M₀ : FinGradedSub (S := S) (x := x) Ω} (v : LaurUT Ω) (hv : IsTw η M₀ v) :
    (TwM.mk v hv).val = v := rfl
end TwM
end GroundTheory.Heights₂.Heights.Kleiman
