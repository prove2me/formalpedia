-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_translateBundleWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:53:34.899334+00:00
-- url     : https://prove2.me/submissions/0f533cb8-11df-4888-a853-ca6dadef0040

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_reindexWord


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {baseZero baseOne : Type u}
    [Fintype baseZero] [Fintype baseOne]
    (n : Nat) [NeZero n] (t : ZMod n)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne (ZMod n) (ZMod n))) :
    HammingWeight (translateBundleWord n t z) = HammingWeight z := by
  exact hammingWeight_reindexWord
    (bundleFiberTranslationEquiv n t) z
end QEC.Coding.FiberBundle
