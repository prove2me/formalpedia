-- Prove2me | solution 1 for Stable.label_histPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:15:36.883285+00:00
-- url     : https://prove2.me/submissions/6da20e11-389c-4484-8863-e6c64e05fcaa

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
import Theorems.Thm_Stable_Prime_eq_top
import Theorems.Thm_ConfFamily_Indep_symm
import Theorems.Thm_Stable_hist_mem


set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
namespace Stable
theorem _root_.solution (hF : Stable F) (hcf : CoincidenceFree F) {c : Set F.Event}
    (hc : F.Config c) {x : F.Event} (hx : x ∈ c) :
    (toPES F).label (histPrime hF hc hx) = F.label x := by
  exact congrArg F.label
    (Prime.eq_top hcf (histPrime hF hc hx) hist_mem (hist_hist hF hc hx)).symm
end Stable
