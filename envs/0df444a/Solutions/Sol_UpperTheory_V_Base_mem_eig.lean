-- Prove2me | solution 1 for UpperTheory.V.Base.mem_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:10:07.066803+00:00
-- url     : https://prove2.me/submissions/07e44a6f-660c-4961-93ea-b093cf24f0df

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_RestrictionMemInvariantH1

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
theorem _root_.solution {π : Representation R Q N} {ψ : Q →* Rˣ} {x : N} :
    x ∈ eig π ψ ↔ ∀ g, π g x = ((ψ g : Rˣ) : R) • x := by
  simp only [eig, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
end UpperTheory.V.Base
