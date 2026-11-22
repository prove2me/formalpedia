-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__placesOf_val_eq_3e0aa8fce33c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:26:54.964676+00:00
-- url     : https://prove2.me/submissions/1fd9709d-f3c5-42b9-a8ec-54ed0fd3a05a

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
theorem _root_.solution (w : (placesOf K).Pl) (x : K) (hx : x ≠ 0) :
    (placesOf K).val w x = ((vAdd ((Equiv.refl _ : (placesOf K).Pl ≃ HeightOneSpectrum (𝓞 K)) w) x : ℤ) :
      WithTop ℤ) :=
  PlacesToy.valW_of_ne w hx
end Formalism.BasicNotions.Examples₂
