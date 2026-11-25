-- Prove2me | solution 1 for P2M_Formalism_FrobeniusOrbits_OrdUnimod_mem_one_iff__37eb220bc84c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:15.232617+00:00
-- url     : https://prove2.me/submissions/ff2b1dde-89c0-43e7-854d-66ed11ae2860

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrdUnimod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.OrdUnimod
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.OrdUnimod
theorem _root_.solution (t : hostE ζ a b) :
    t ∈ (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ↔ IsIntegral ℤ t := by
  rw [FractionalIdeal.mem_one_iff, IsIntegralClosure.isIntegral_iff (A := 𝓞 (hostE ζ a b))]
end Formalism.FrobeniusOrbits.OrdUnimod
