-- Prove2me | solution 1 for ReciprocityTheory.Cheb.finite_norm_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:41:56.217238+00:00
-- url     : https://prove2.me/submissions/cd57e654-c907-4bf5-bf05-646e1c04b270

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_CycTail

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (T : Finset ℕ) : {q : Prm E | Nrm q ∈ T}.Finite := by
  have h : {I : Ideal (𝓞 E) | Ideal.absNorm I ∈ T}.Finite := by
    have : {I : Ideal (𝓞 E) | Ideal.absNorm I ∈ T} = ⋃ n ∈ T, {I : Ideal (𝓞 E) | Ideal.absNorm I = n} := by
      ext; simp
    rw [this]
    exact Set.Finite.biUnion T.finite_toSet fun n _ => Ideal.finite_setOfPred_absNorm_eq n
  exact h.preimage (f := fun q : Prm E => q.asIdeal) (fun x _ y _ hxy => HeightOneSpectrum.ext hxy)
end ReciprocityTheory.Cheb
