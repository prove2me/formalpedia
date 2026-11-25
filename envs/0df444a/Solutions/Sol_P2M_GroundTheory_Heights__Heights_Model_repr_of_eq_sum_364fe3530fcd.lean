-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_repr_of_eq_sum_364fe3530fcd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:58.176825+00:00
-- url     : https://prove2.me/submissions/27c880c3-3139-4173-bd3d-c03fbabdef36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrame
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrameP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}
    {b : Fin r → E} (hli : LinearIndependent Ω b)
    (hsp : Submodule.span Ω (Set.range b) = ⊤) {e : E} {a : Fin r → Ω} (hae : e = ∑ q, a q • b q)
    (q : Fin r) : (Module.Basis.mk hli hsp.ge).repr e q = a q := by
  have : e = ∑ q, a q • (Module.Basis.mk hli hsp.ge) q := by simpa [Module.Basis.coe_mk] using hae
  rw [this, (Module.Basis.mk hli hsp.ge).repr_sum_self a]
end GroundTheory.Heights₂.Heights.Model
