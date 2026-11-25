-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.chain_repr_Npow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:07:06.048191+00:00
-- url     : https://prove2.me/submissions/d7b24eec-1b5a-4cbd-952e-0dcf232c540d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_ChainA
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_chain_repr_N

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
    (hB : IsChain N l B) (m : ℕ) (z : W) (a : ι) (i : Fin (l a)) :
    B.repr ((N ^ m) z) ⟨a, i⟩ = if h : m ≤ (i : ℕ) then B.repr z ⟨a, ⟨i - m, by omega⟩⟩ else 0 := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    by_cases h1 : m + 1 ≤ (i : ℕ)
    · rw [dif_pos (by omega), dif_pos h1, chain_repr_N hB, dif_pos (by simp; omega)]
      congr 2
    · rw [dif_neg h1]
      split_ifs with h2
      · rw [chain_repr_N hB, dif_neg]
        simp
        omega
      · rfl
end PositivityTheory.RgUd.T.Nil.Orb.BReps
