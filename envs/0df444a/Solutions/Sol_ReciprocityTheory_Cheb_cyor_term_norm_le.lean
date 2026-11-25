-- Prove2me | solution 1 for ReciprocityTheory.Cheb.cyor_term_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:06:11.30091+00:00
-- url     : https://prove2.me/submissions/b4150f93-9b15-4299-9b4c-ec1c8e6130ab

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_CycOrth
import Theorems.Thm_ReciprocityTheory_Cheb_cyor_norm_cpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {l : ℕ} (χ : DirichletCharacter ℂ l) (q : Prm E) (s : ℝ) :
    ‖χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := by
  rw [norm_mul, cyor_norm_cpow]
  have h1 := DirichletCharacter.norm_le_one χ ((Nrm q : ℕ) : ZMod l)
  have h2 : 0 ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  nlinarith [norm_nonneg (χ ((Nrm q : ℕ) : ZMod l))]
end ReciprocityTheory.Cheb
