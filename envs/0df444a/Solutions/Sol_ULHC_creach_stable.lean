-- Prove2me | solution 1 for ULHC.creach_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:52:46.925803+00:00
-- url     : https://prove2.me/submissions/3db19fd0-a5dc-4642-95ce-b9e3e940fb0b

import Definitions.Def_ULHC_TwoFactor
import Definitions.Def_ULHC_Comp
import Theorems.Thm_ULHC_creach_succ
import Theorems.Thm_ULHC_Conn_refl


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge}
namespace ULHC
theorem _root_.solution {x : Pt} {k : ℕ} (h : creach F x (k + 1) = creach F x k) :
    ∀ j, k ≤ j → creach F x j = creach F x k := by
  intro j hj
  induction hj with
  | refl => rfl
  | step _ ih => rw [creach_succ, ih, ← creach_succ, h]
end ULHC
