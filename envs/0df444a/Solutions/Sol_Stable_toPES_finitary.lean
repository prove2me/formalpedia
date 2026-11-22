-- Prove2me | solution 1 for Stable.toPES_finitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:15:18.008093+00:00
-- url     : https://prove2.me/submissions/e3ac4cc1-8bd0-4ac6-ba41-b1466f9dc2a5

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
import Theorems.Thm_Stable_Prime_le_iff
import Theorems.Thm_Stable_Prime_top_mem
import Theorems.Thm_Stable_prime_val_finite
import Theorems.Thm_Stable_eq_hist_of_subset
import Theorems.Thm_ConfFamily_Indep_symm
import Theorems.Thm_GES_toFamily_Config
import Theorems.Thm_GES_toFamily_Event
import Theorems.Thm_PES_enables_iff
import Theorems.Thm_PES_toFamily_Config
import Theorems.Thm_PES_toFamily_Event
import Theorems.Thm_SES_toFamily_Config
attribute [local simp] GES.toFamily_Config
attribute [local simp] GES.toFamily_Event
attribute [local simp] PES.enables_iff
attribute [local simp] PES.toFamily_Config
attribute [local simp] PES.toFamily_Event
attribute [local simp] SES.toFamily_Config


attribute [local simp] Stable.Prime.le_iff

set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
namespace Stable
theorem _root_.solution (G : GES L) (hF : Stable G.toFamily) (p : (toPES G.toFamily).Event) :
    Set.Finite ((toPES G.toFamily).past p) := by
  refine Set.Finite.of_finite_image (f := Prime.top) ?_ ?_
  · refine (prime_val_finite G hF p).subset ?_
    rintro t ⟨q, hq, rfl⟩
    have hle : q.val ⊆ p.val := le_of_lt (α := (toPES G.toFamily).Event) hq
    exact hle (Prime.top_mem q)
  · rintro q hq q' hq' heq
    have hle : q.val ⊆ p.val := le_of_lt (α := (toPES G.toFamily).Event) hq
    have hle' : q'.val ⊆ p.val := le_of_lt (α := (toPES G.toFamily).Event) hq'
    have h1 : q.val = hist G.toFamily p.val (Prime.top q) :=
      eq_hist_of_subset hF p.config hle
    have h2 : q'.val = hist G.toFamily p.val (Prime.top q') :=
      eq_hist_of_subset hF p.config hle'
    exact Subtype.ext (h1.trans (heq ▸ h2.symm))
end Stable
