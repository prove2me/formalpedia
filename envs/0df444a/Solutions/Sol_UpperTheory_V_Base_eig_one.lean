-- Prove2me | solution 1 for UpperTheory.V.Base.eig_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:34:39.912415+00:00
-- url     : https://prove2.me/submissions/7f3054e0-b5df-4537-9e2a-0b0018832597

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_RestrictionMemInvariantH1
import Theorems.Thm_UpperTheory_V_Base_mem_eig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.Gal
open UpperTheory UpperTheory.V UpperTheory.V.Base
variable {R Q N : Type} [CommRing R] [Group Q] [AddCommGroup N] [Module R N]
namespace UpperTheory.V.Base
theorem _root_.solution (π : Representation R Q N) : eig π 1 = π.invariants := by
  ext x
  rw [mem_eig, Representation.mem_invariants]
  simp
end UpperTheory.V.Base
