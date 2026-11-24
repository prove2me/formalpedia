-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_stdH_frames_91564ebb4ca5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:12:11.175225+00:00
-- url     : https://prove2.me/submissions/cc385c97-06ef-4641-a191-df6680fce545

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
variable (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (v : InfinitePlace K) : IsUnit ((stdH K n).X v).det := by
  rw [show (stdH K n).X v = 1 from rfl, Matrix.det_one]
  exact isUnit_one
end Formalism.BasicNotions.Examples₂.NZ
