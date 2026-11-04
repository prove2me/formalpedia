-- Prove2me | solution 1 for ThreeSum.TernaryActualSeedEnumeration.sum_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:09:47.492813+00:00
-- url     : https://prove2.me/submissions/334dbd69-3449-4b64-a395-b54a44004cb9

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
theorem _root_.solution (hf : f.Monic) (score : Fin ((p^f.natDegree)*(p^f.natDegree))→ℕ) :
    (∑ i, score i)=∑ seed : AdjoinRoot f×AdjoinRoot f, score (equiv hf seed) :=
  (Equiv.sum_comp (equiv hf) score).symm
end ThreeSum.TernaryActualSeedEnumeration
