-- Prove2me | solution 1 for ThreeSum.LightSignedFiniteTable.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:47:46.311949+00:00
-- url     : https://prove2.me/submissions/97d8c605-0ead-487d-8a91-e9f8297c5bec

import Definitions.Def_Submission_ThreeSum_LightFiniteTable
import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_meets


set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedFiniteTable
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSignedFiniteTable
theorem _root_.solution (xs : List ℤ) (base : ℕ) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : base+xs.length ≤ lim.space)
    (hvalues : ∀ x ∈ xs, |x| ≤ lim.word) :
    Meets lim (program xs) 0 d [base] μ (7*xs.length+2)
      (fun r ν => r=(xs.length : ℤ) ∧ Seg ν base xs ∧ SameOutside μ ν base xs.length) :=
  meets rfl base μ hw hspace hvalues
end ThreeSum.LightSignedFiniteTable
