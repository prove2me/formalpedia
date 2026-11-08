-- Prove2me | solution 1 for QEC.Coding.FiberBundle.HHO20DistanceBalancing.distanceCoefficient_le_two_pow_two_hundred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:28:56.451664+00:00
-- url     : https://prove2.me/submissions/94251679-196b-4921-89f8-71d5e86694c3

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialLocality
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Asymptotics

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding
universe u
namespace QEC.Coding.FiberBundle.HHO20DistanceBalancing
theorem _root_.solution :
    distanceCoefficient ≤ 2 ^ 200 := by
  norm_num [distanceCoefficient, degreeCoefficient]
end QEC.Coding.FiberBundle.HHO20DistanceBalancing
