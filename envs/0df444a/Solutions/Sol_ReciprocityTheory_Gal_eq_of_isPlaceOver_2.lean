-- Prove2me | solution 2 for ReciprocityTheory.Gal.eq_of_isPlaceOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:28:16.484425+00:00
-- url     : https://prove2.me/submissions/fe33bbb2-8ffd-4a48-8a78-d0e43744192e

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
namespace ReciprocityTheory.Gal
theorem _root_.solution {A : ValuationSubring (Ω)} {v v' : HeightOneSpectrum (𝓞 F)}
    (h : IsPlaceOver A v) (h' : IsPlaceOver A v') : v = v' := by
  unfold Formalism.ConjugateSelfDual.IsPlaceOver at h h'
  have e : v.asIdeal = v'.asIdeal := by
    ext x
    rw [← h x, ← h' x]
  exact IsDedekindDomain.HeightOneSpectrum.ext e
end ReciprocityTheory.Gal
