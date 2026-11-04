-- Prove2me | solution 1 for ThreeSum.TernaryActualSeedEnumeration.index_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:42:03.160871+00:00
-- url     : https://prove2.me/submissions/a2c25b7d-ddfd-47f5-9cb6-a9dfc8b9d44e

import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedMatrix
import Definitions.Def_Submission_ThreeSum_TernaryActualSeedEnumeration

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryActualSeedEnumeration
open TernaryExtensionEncoding Polynomial
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime] {f : (ZMod p)[X]}
variable [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryActualSeedEnumeration
theorem _root_.solution (hf : f.Monic) (x y : AdjoinRoot f) :
    (equiv hf (x,y)).val=encode hf y+p^f.natDegree*encode hf x := rfl
end ThreeSum.TernaryActualSeedEnumeration
