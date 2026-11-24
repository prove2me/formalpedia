-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_b_inj_4cf57cb8133b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:12:10.342831+00:00
-- url     : https://prove2.me/submissions/7b011d21-4d1c-4436-98fb-0374edb5b120

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZRowA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) {n : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V)
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution : Function.Injective b := by
  have := b.toBasis.injective
  rwa [b.coe_toBasis] at this
end Formalism.BasicNotions.Examples₂.NZ
