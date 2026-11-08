-- Prove2me | solution 1 for QEC.Coding.FiberBundle.HHO20DistanceBalancing.balancedLocalityComplex_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:24:49.222393+00:00
-- url     : https://prove2.me/submissions/4ba48449-50df-4e01-ae9b-40e9f04fe53f

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancing
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding
namespace QEC.Coding.FiberBundle.HHO20DistanceBalancing
theorem _root_.solution
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) :
    balancedLocalityComplex baseSample twistSample balanceSample =
      DistanceBalancing.chainComplex
        (balancedData baseSample twistSample balanceSample) := by
  classical
  rfl
end QEC.Coding.FiberBundle.HHO20DistanceBalancing
