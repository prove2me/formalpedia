-- Prove2me | solution 1 for P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_mul_aee82e1fd007
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:53:40.987257+00:00
-- url     : https://prove2.me/submissions/491755c0-3e09-4186-a73e-897b05f2c9e5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Approximation
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.SemiLocal.tensorEquiv'_tmul

set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module
noncomputable section
open GroundTheory.Global.SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (L) (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution (a : v.adicCompletion K) (y : L ⊗[K] v.adicCompletion K) :
    tensorEquiv' L v ((1 ⊗ₜ a) * y) =
      algebraMap (v.adicCompletion K) (CompletionsOver L v) a * tensorEquiv' L v y := by
  rw [map_mul, tensorEquiv'_tmul, map_one, one_mul]
end GroundTheory.Global.SemiLocal
