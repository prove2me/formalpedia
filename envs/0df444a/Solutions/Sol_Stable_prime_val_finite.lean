-- Prove2me | solution 1 for Stable.prime_val_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:02:07.213305+00:00
-- url     : https://prove2.me/submissions/40e394c4-72b6-4c86-8311-ea05533a9852

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
import Theorems.Thm_Stable_hist_finite
import Theorems.Thm_Stable_Prime_top_mem
import Theorems.Thm_Stable_Prime_eq_hist_top

set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
namespace Stable
theorem _root_.solution (G : GES L) (hF : Stable G.toFamily) (p : Prime G.toFamily) :
    p.val.Finite :=
  (Prime.eq_hist_top p) ▸ hist_finite G hF p.config (Prime.top_mem p)
end Stable
