-- Prove2me | solution 1 for P2M_Formalism_L2_DIV_isCMSub_cmMax__3b92c5b81347
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:15:42.330645+00:00
-- url     : https://prove2.me/submissions/a0ba02ae-3af2-4868-8969-fb96a6100cb7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.DIV
theorem _root_.solution : IsCMSub (cmMax K) := fun σ _ ha => ha σ
end Formalism.L2.DIV
