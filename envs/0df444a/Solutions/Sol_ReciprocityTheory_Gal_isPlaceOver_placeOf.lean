-- Prove2me | solution 1 for ReciprocityTheory.Gal.isPlaceOver_placeOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:30.998732+00:00
-- url     : https://prove2.me/submissions/a7754d96-cb25-44bb-bd75-af8d76ac2978

import Definitions.Def_Formalism_ConjugateSelfDual_Statement
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Theorems.Thm_ReciprocityTheory_Gal_exists_isPlaceOver

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
variable (Ω)
namespace ReciprocityTheory.Gal
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) : IsPlaceOver (placeOf Ω v) v := Classical.epsilon_spec (exists_isPlaceOver Ω v)
end ReciprocityTheory.Gal
