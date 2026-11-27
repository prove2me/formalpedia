-- Prove2me | solution 1 for P2M_GlobalTheory_lengthCommensurable_finset_sup__4a639e261a53
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:54:23.852986+00:00
-- url     : https://prove2.me/submissions/4f699832-fafc-40fa-a84f-ffa0bc6c9ecc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
import Theorems.Thm_GlobalTheory_LengthCommensurable_sup_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
variable {A A' B B' C : Submodule R V}
namespace GlobalTheory
theorem _root_.solution {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → Submodule R V} (h : ∀ i ∈ s, LengthCommensurable A (f i)) :
    LengthCommensurable A (s.sup' hs f) :=
  Finset.sup'_induction hs f (p := LengthCommensurable A) (fun _ h₁ _ h₂ => h₁.sup_right h₂) h
end GlobalTheory
