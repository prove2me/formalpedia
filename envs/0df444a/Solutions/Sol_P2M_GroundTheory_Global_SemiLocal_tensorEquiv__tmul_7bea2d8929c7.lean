-- Prove2me | solution 1 for P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:15:16.833276+00:00
-- url     : https://prove2.me/submissions/dffc15cd-4d5a-4e4f-bf74-92ef7eeede6b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Approximation
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module
noncomputable section
open GroundTheory.Global.SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (L) (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution (x : L) (a : v.adicCompletion K) :
    tensorEquiv' L v (x ⊗ₜ a) =
      algebraMap L (CompletionsOver L v) x * algebraMap (v.adicCompletion K) _ a :=
  tensorMap'_tmul L v x a
end GroundTheory.Global.SemiLocal
