-- Prove2me | solution 1 for ReciprocityTheory.Gal.continuous_cycZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:26.713478+00:00
-- url     : https://prove2.me/submissions/1e9581b3-d802-4b18-a191-9f743ce65175

import Definitions.Def_Formalism_ConjugateSelfDual_Statement
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable (F Ω)
namespace ReciprocityTheory.Gal
theorem _root_.solution (l : ℕ) [Fact l.Prime] : Continuous (cycZ F Ω l) :=
  cyclotomicCharacter.continuous l F Ω
end ReciprocityTheory.Gal
