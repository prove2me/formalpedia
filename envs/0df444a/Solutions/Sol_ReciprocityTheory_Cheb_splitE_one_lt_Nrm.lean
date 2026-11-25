-- Prove2me | solution 1 for ReciprocityTheory.Cheb.splitE_one_lt_Nrm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:44:46.726366+00:00
-- url     : https://prove2.me/submissions/c2073a0b-f278-4e04-889e-a67adacaed34

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitD
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitEA

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
noncomputable section
variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (q : Prm E) : 1 < Nrm q := by
  unfold Nrm
  have h0 : Ideal.absNorm q.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact q.ne_bot
  have h1 : Ideal.absNorm q.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact q.isPrime.ne_top
  omega
end ReciprocityTheory.Cheb
