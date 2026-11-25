-- Prove2me | solution 1 for P2M_Formalism_GM_ProjS_mix_w__f4375b1a0220
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:38:12.666462+00:00
-- url     : https://prove2.me/submissions/4f7a777f-ec5e-41e6-b317-c6fa41fc84a4

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
namespace Formalism.GM.ProjS
theorem _root_.solution (hv : M.TieVars w e zv sv) :
    ∀ c, ((∃ d, (Fin.cons zv w : Fin (r + 1) → σ) d = w c) ∧ ∀ d, (Fin.cons zv w : Fin (r + 1) → σ) d ≠ e c) ∨
      ((∀ d, (Fin.cons zv w : Fin (r + 1) → σ) d ≠ w c) ∧ ∃ d, (Fin.cons zv w : Fin (r + 1) → σ) d = e c) := by
  obtain ⟨hw, he, hwe, hz, hzs⟩ := hv
  intro c
  refine Or.inl ⟨⟨c.succ, by simp⟩, fun d => ?_⟩
  induction d using Fin.cases with
  | zero => simpa using (hz c).2.2.1.symm
  | succ d => simpa using hwe d c
end Formalism.GM.ProjS
