-- Prove2me | solution 1 for ReciprocityTheory.Gal.Ine_le_Dec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:26.688255+00:00
-- url     : https://prove2.me/submissions/36171c7f-0807-4ba3-a5f5-0134bf3920cb

import Definitions.Def_Formalism_ConjugateSelfDual_Statement
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Theorems.Thm_ReciprocityTheory_Gal_mem_Ine

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
namespace ReciprocityTheory.Gal
theorem _root_.solution (A : ValuationSubring (Ω)) : Ine (F := F) A ≤ Dec (F := F) A := fun _ h => (mem_Ine.mp h).1
end ReciprocityTheory.Gal
