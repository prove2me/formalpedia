-- Prove2me | solution 1 for ThreeSum.LightTernaryCell.program_inverse_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:18:06.933407+00:00
-- url     : https://prove2.me/submissions/29d64a3d-a7f3-4df0-bdb0-dca4a4e093a0

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_LightTernaryCell
import Theorems.Thm_ThreeSum_LightTernaryCell_inverse_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCell
open Light ThreeSum.TernaryQuery
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryCell
theorem _root_.solution {μ : ℕ → ℤ} {a0 a1 a2 U : ℕ}
    (q : Fin 3) (f : Fin 3 → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (h0 : a0 < lim.space) (h1 : a1 < lim.space) (h2 : a2 < lim.space)
    (hr0 : μ a0 = f 0) (hr1 : μ a1 = f 1) (hr2 : μ a2 = f 2)
    (hf : ∀ e, |f e| ≤ U) (hword : 4 * (U : ℤ) + 3 ≤ lim.word) :
    Meets lim program 1 d [q.val,a0,a1,a2] μ time
      (fun r μ' => r = inverseDigit f q ∧ μ' = μ) :=
  inverse_meets rfl q f hw h0 h1 h2 hr0 hr1 hr2 hf hword
end ThreeSum.LightTernaryCell
