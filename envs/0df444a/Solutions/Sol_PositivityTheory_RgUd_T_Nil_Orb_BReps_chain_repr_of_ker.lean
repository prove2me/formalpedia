-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.chain_repr_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:13:45.911487+00:00
-- url     : https://prove2.me/submissions/83c5de8e-2595-471a-8605-9a723380c841

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_ChainA
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_chain_repr_Npow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]
namespace PositivityTheory.RgUd.T.Nil.Orb.BReps
theorem _root_.solution {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (m : ℕ) (z : W) (hz : (N ^ m) z = 0) (a : ι) (i : Fin (l a))
    (hi : (i : ℕ) + m < l a) : B.repr z ⟨a, i⟩ = 0 := by
  have h := chain_repr_Npow hB m z a ⟨i + m, hi⟩
  rw [hz, map_zero, dif_pos (by simp)] at h
  rw [Finsupp.zero_apply] at h
  rw [h]
  congr 2
  ext
  simp
end PositivityTheory.RgUd.T.Nil.Orb.BReps
