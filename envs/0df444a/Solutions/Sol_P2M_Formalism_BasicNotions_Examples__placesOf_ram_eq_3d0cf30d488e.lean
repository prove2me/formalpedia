-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__placesOf_ram_eq_3d0cf30d488e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:58.283472+00:00
-- url     : https://prove2.me/submissions/e044ad32-3c17-4d04-8d5b-eb60bed368bd

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Places

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
variable (K : Type) [Field K] [NumberField K] [StarRing K]
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution (w : (placesOf K).Pl) :
    (placesOf K).ramIdx w = eWL K ((Equiv.refl _ : (placesOf K).Pl ≃ HeightOneSpectrum (𝓞 K)) w) :=
  rfl
end Formalism.BasicNotions.Examples₂
