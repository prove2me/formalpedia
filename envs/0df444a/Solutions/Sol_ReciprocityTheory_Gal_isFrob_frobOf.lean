-- Prove2me | solution 1 for ReciprocityTheory.Gal.isFrob_frobOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:48:48.532803+00:00
-- url     : https://prove2.me/submissions/e8aa2259-c879-4e77-86d3-56537b17685d

import Definitions.Def_Formalism_ConjugateSelfDual_Statement
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Theorems.Thm_ReciprocityTheory_Gal_isPlaceOver_placeOf
import Theorems.Thm_ReciprocityTheory_Gal_exists_isFrob

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
theorem _root_.solution [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) :
    IsFrob (placeOf Ω v) (normV v) (frobOf Ω v) := Classical.epsilon_spec (exists_isFrob (isPlaceOver_placeOf Ω v))
end ReciprocityTheory.Gal
