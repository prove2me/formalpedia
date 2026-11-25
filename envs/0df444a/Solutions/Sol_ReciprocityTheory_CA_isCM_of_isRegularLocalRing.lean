-- Prove2me | solution 1 for ReciprocityTheory.CA.isCM_of_isRegularLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:39.378992+00:00
-- url     : https://prove2.me/submissions/c01e8550-1caf-41c7-910e-52fbdaef9d8c

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RegGens
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_IsCMOfIsRegularLocalRing
import Theorems.Thm_ReciprocityTheory_CA_RegGens_exists_regular_gens


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
namespace ReciprocityTheory.CA
theorem _root_.solution (R : Type*) [CommRing R] [IsRegularLocalRing R] : IsCM R := by
  have hd : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  refine ⟨inferInstance, (maximalIdeal R).spanFinrank, hd, ?_⟩
  obtain ⟨rs, hlen, reg, hm⟩ := ReciprocityTheory.CA.RegGens.exists_regular_gens R _ hd
  refine ⟨rs, hlen, fun r hr => ?_, reg⟩
  rw [← hm]
  exact Ideal.subset_span hr
end ReciprocityTheory.CA
