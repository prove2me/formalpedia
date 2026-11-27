-- Prove2me | solution 1 for P2M_GlobalTheory_lengthCommensurable_finset_inf__80856a12ef97
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:54:21.645695+00:00
-- url     : https://prove2.me/submissions/99ee0b8d-b6ac-473f-9e67-76aff0bbf803

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
import Theorems.Thm_GlobalTheory_LengthCommensurable_inf_right

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
    LengthCommensurable A (s.inf' hs f) :=
  Finset.inf'_induction hs f (p := LengthCommensurable A) (fun _ h₁ _ h₂ => h₁.inf_right h₂) h
end GlobalTheory
