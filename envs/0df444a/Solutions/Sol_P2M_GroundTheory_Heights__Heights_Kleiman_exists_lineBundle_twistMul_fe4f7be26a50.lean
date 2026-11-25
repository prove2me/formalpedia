-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_lineBundle_twistMul_fe4f7be26a50
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:35:13.087237+00:00
-- url     : https://prove2.me/submissions/615cef6b-5927-479a-9e0c-6b496eb388be

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_powBundle_toSubSystem_418f6a814041

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (M : LineBundle S x) (p : ℕ) (m : ℤ) :
    ∃ L : LineBundle S x, L.toSubSystem = twistMul M.toSubSystem p m :=
  ⟨(M.powBundle p).tensorProd (twistBundle S x m), by
    change (M.powBundle p).toSubSystem.twist (twistSys S x m) = _
    rw [LineBundle.powBundle_toSubSystem]
    rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman
