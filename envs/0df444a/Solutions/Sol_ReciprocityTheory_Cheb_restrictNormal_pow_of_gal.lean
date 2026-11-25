-- Prove2me | solution 1 for ReciprocityTheory.Cheb.restrictNormal_pow_of_gal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:45:05.212671+00:00
-- url     : https://prove2.me/submissions/fe2fcb2a-af99-444a-a20c-ae927448786f

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossFix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open ReciprocityTheory ReciprocityTheory.Cheb
variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois ℚ K] [IsGalois ℚ M]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (g : Gal(M/ℚ)) (m : ℕ) :
    AlgEquiv.restrictNormal (g ^ m) K = (AlgEquiv.restrictNormal g K) ^ m :=
  map_pow (AlgEquiv.restrictNormalHom K) g m
end ReciprocityTheory.Cheb
