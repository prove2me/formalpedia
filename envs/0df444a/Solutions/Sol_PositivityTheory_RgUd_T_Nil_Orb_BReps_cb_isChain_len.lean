-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.cb_isChain_len
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:56:55.837855+00:00
-- url     : https://prove2.me/submissions/67de1657-1e67-448f-a619-6f28ec5b606b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_CbIsChainApply
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_pow_succ
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
    (hB : IsChain N l B) (a : ι) (h0 : 0 < l a) : (N ^ l a) (B ⟨a, ⟨0, h0⟩⟩) = 0 := by
  have h1 := hB a ⟨l a - 1, by omega⟩
  rw [dif_neg (show ¬ (((⟨l a - 1, by omega⟩ : Fin (l a)) : ℕ) + 1 < l a) by simp; omega)] at h1
  rw [cb_isChain_apply N hB a h0 (l a - 1) (by omega), cb_pow_succ] at h1
  rwa [show l a - 1 + 1 = l a by omega] at h1
end PositivityTheory.RgUd.T.Nil.Orb.BReps
