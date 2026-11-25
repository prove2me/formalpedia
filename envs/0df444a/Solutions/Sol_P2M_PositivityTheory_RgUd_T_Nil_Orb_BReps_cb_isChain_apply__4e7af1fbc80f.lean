-- Prove2me | solution 1 for P2M_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_isChain_apply__4e7af1fbc80f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:54:32.741836+00:00
-- url     : https://prove2.me/submissions/57bc3e8f-a341-4d6d-8c35-7b59daeb38eb

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_CbIsChainApply
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_isChain_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
open Module Submodule
variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]
namespace PositivityTheory.RgUd.T.Nil.Orb.BReps
theorem _root_.solution (N : W →ₗ[E] W) {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (a : ι) (h0 : 0 < l a) (i : Fin (l a)) :
    B ⟨a, i⟩ = (N ^ (i : ℕ)) (B ⟨a, ⟨0, h0⟩⟩) := by
  obtain ⟨i, hi⟩ := i
  exact cb_isChain_apply N hB a h0 i hi
end PositivityTheory.RgUd.T.Nil.Orb.BReps
