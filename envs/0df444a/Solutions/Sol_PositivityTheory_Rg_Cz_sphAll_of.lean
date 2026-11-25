-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.sphAll_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:37:51.946744+00:00
-- url     : https://prove2.me/submissions/8bd6264c-ea30-4d6b-b477-bdac028c7de6

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_StepFormula
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
namespace PositivityTheory.Rg.Cz
theorem _root_.solution (h1 : SWStart) (h2 : Contract) (h3 : SemiZero) : SphAll := by
  intro n hn M _ _ ι _ _ Γ _ _ _ _ _ bar κ E ρ hK hG s φ h0 hφ
  obtain ⟨m, hm⟩ := h1 n M ι Γ bar κ E ρ hK hG φ h0
  refine h3 n hn M ι Γ bar κ E ρ hK hG s φ hφ ?_
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hp
    · exact hm
    · obtain ⟨m', h, h'⟩ := h2 n hn M ι Γ bar κ E ρ hK hG s φ hφ m hp hm
      exact ih m' h h'
end PositivityTheory.Rg.Cz
