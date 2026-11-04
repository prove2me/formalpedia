-- Prove2me | solution 1 for ThreeSum.LightTernaryCell.program_zeta_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:18:05.687677+00:00
-- url     : https://prove2.me/submissions/cfa7904a-ed87-4bfd-9c8a-ea9000860d8a

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_LightTernaryCell
import Theorems.Thm_ThreeSum_LightTernaryCell_zeta_meets

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
    Meets lim program 0 d [q.val,a0,a1,a2] μ time
      (fun r μ' => r = zetaDigit f q ∧ μ' = μ) :=
  zeta_meets rfl q f hw h0 h1 h2 hr0 hr1 hr2 hf hword
end ThreeSum.LightTernaryCell
