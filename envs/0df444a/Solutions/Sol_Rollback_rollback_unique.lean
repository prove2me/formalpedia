-- Prove2me | solution 1 for Rollback.rollback_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:06:02.125879+00:00
-- url     : https://prove2.me/submissions/ac4378b2-69fd-4ff9-a4f5-081b0116ac6a

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Family_Rollback
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card
import Definitions.Def_EventStructures_Prime_Rollback
import Theorems.Thm_Rollback_rollbackFuture_val
import Theorems.Thm_Rollback_rollbackFuture_mem
import Theorems.Thm_Rollback_rollback_eq_future
import Theorems.Thm_PES_enables_iff
import Theorems.Thm_PES_toFamily_Config
import Theorems.Thm_PES_toFamily_Event
import Theorems.Thm_Rollback_rollback_not_mem
import Theorems.Thm_Rollback_rollback_subset
attribute [local simp] PES.enables_iff
attribute [local simp] PES.toFamily_Config
attribute [local simp] PES.toFamily_Event
attribute [local simp] Rollback.rollback_not_mem
attribute [local simp] Rollback.rollback_subset


attribute [local simp] Rollback.rollbackFuture_val
attribute [local simp] Rollback.rollbackFuture_mem
attribute [local simp] Rollback.rollback_eq_future

set_option autoImplicit true
variable {L : Type*} (es : PES L)
open Rollback
open Configuration ConfFamily
local infix:50 " ⊢ " => enables es
namespace Rollback
theorem _root_.solution {c : Conf es} {e : es.Event}
    {m₁ m₂ : Conf es} (h₁ : isRollback es.toFamily c e m₁) (h₂ : isRollback es.toFamily c e m₂) :
    m₁ = m₂ := by
  apply Subtype.ext
  rw [rollback_eq_future (es := es) h₁, rollback_eq_future (es := es) h₂]
end Rollback
