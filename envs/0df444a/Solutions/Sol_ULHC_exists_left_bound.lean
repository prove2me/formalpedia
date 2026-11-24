-- Prove2me | solution 1 for ULHC.exists_left_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:59:40.007804+00:00
-- url     : https://prove2.me/submissions/eeedc04b-51f2-4e38-9b44-46f2dbb22b49

import Definitions.Def_ULHC_Grid
import Definitions.Def_ULHC_Potential

set_option autoImplicit true
open ULHC
open Finset
variable {E : Finset Edge} {w : Edge → ℤ}
namespace ULHC
theorem _root_.solution (E : Finset Edge) : ∃ B : ℤ, ∀ e ∈ E, B < e.p.1 := by
  refine ⟨-(∑ e ∈ E, |e.p.1|) - 1, fun e he => ?_⟩
  have h1 : |e.p.1| ≤ ∑ e ∈ E, |e.p.1| :=
    Finset.single_le_sum (f := fun e : Edge => |e.p.1|) (fun _ _ => abs_nonneg _) he
  have h2 := neg_abs_le e.p.1
  linarith
end ULHC
