-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_chart_smul_e2cb3280eb9c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:13:00.631075+00:00
-- url     : https://prove2.me/submissions/f7fc1869-4587-4624-be03-e5df37550245

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZColumnsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZColumns

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
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  {r : ℕ}
omit [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
theorem _root_.solution {I : Chart x} (a : chartRing S x I) (e : E) : a • e = (a : Ω) • e := rfl
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
