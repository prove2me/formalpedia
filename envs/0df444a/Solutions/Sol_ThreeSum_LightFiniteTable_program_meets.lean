-- Prove2me | solution 1 for ThreeSum.LightFiniteTable.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:40:00.520279+00:00
-- url     : https://prove2.me/submissions/12899398-c519-44c8-bdfc-23bbd2549b27

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightFiniteTable
import Theorems.Thm_ThreeSum_LightFiniteTable_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightFiniteTable
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightFiniteTable
theorem _root_.solution (xs : List ℕ) (base : ℕ) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : base+xs.length ≤ lim.space)
    (hvalues : ∀ x ∈ xs, (x : ℤ) ≤ lim.word) :
    Meets lim (program xs) 0 d [base] μ (5*xs.length+2)
      (fun r ν => r=(xs.length : ℤ) ∧
        Seg ν base (xs.map (fun (x : ℕ) => (x : ℤ))) ∧
        SameOutside μ ν base xs.length) :=
  meets rfl base μ hw hspace hvalues
end ThreeSum.LightFiniteTable
