-- Prove2me | solution 1 for Stable.histPrime_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:02:26.263001+00:00
-- url     : https://prove2.me/submissions/111592d8-2f8f-4f56-961b-2fcfc985bc71

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
import Theorems.Thm_Stable_Prime_eq_top
import Theorems.Thm_ConfFamily_Indep_symm
import Theorems.Thm_Stable_hist_subset


set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
namespace Stable
theorem _root_.solution (hF : Stable F) (hcf : CoincidenceFree F) (p : Prime F)
    {t : F.Event} (ht : t ∈ p.val) (hne : t ≠ Prime.top p) :
    histPrime hF p.config ht < p := by
  refine lt_of_le_of_ne (hist_subset p.config ht) fun heq => ?_
  exact hne (Prime.eq_top hcf p ht (congrArg Subtype.val heq).symm)
end Stable
