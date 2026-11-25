-- Prove2me | solution 1 for P2M_Formalism_GM_ProjS_mix_e__3cb99070d549
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:38:11.820795+00:00
-- url     : https://prove2.me/submissions/c95f89da-e16d-43d1-b379-97fdc3884f51

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
    ∀ c, ((∃ d, (Fin.cons sv e : Fin (r + 1) → σ) d = w c) ∧ ∀ d, (Fin.cons sv e : Fin (r + 1) → σ) d ≠ e c) ∨
      ((∀ d, (Fin.cons sv e : Fin (r + 1) → σ) d ≠ w c) ∧ ∃ d, (Fin.cons sv e : Fin (r + 1) → σ) d = e c) := by
  obtain ⟨hw, he, hwe, hz, hzs⟩ := hv
  intro c
  refine Or.inr ⟨fun d => ?_, ⟨c.succ, by simp⟩⟩
  induction d using Fin.cases with
  | zero => simpa using (hz c).2.1.symm
  | succ d => simpa using (hwe c d).symm
end Formalism.GM.ProjS
