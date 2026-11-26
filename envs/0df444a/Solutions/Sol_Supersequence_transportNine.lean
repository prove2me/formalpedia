-- Prove2me | solution 1 for Supersequence.transportNine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:59:16.920605+00:00
-- url     : https://prove2.me/submissions/beac9c52-063a-4b02-b1cb-98b969c7e1e8

import Std
import Definitions.Def_Frequency
import Theorems.Thm_Supersequence_project_append
import Theorems.Thm_Supersequence_project_cons_self
import Theorems.Thm_Supersequence_universal_iff_covers
attribute [local simp] Supersequence.project_append
attribute [local simp] Supersequence.project_cons_self
section
namespace Supersequence
open List
variable {α : Type}
variable [DecidableEq α]
private theorem close_skip : ∀ x a, close x (skip x a) = a := by decide
private theorem skip_ne : ∀ x a, skip x a ≠ x := by decide
end Supersequence
end

set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
variable [DecidableEq α]
namespace Supersequence
theorem _root_.solution (nine : ∀ v : List (Fin 9), Universal v → 66 ≤ v.length)
    (x : Fin 10) : LowerOnOthers x 66 := by
  intro v _ hv
  have cov : Covers (fun _ => True) (v.map (close x)) := by
    intro q hn _
    have nd : (q.map (skip x)).Nodup := pairwise_map.mpr (hn.imp (by
      intro a b hab e; exact hab (by simpa only [close_skip] using congrArg (close x) e)))
    have h := (hv _ nd (by simpa using fun a (_ : a ∈ q) => skip_ne x a)).map (close x)
    have eq : (q.map (skip x)).map (close x) = q := by
      simp [map_map, Function.comp_def, close_skip]
    exact eq ▸ h
  simpa using nine _ (universal_iff_covers.mpr cov)
end Supersequence
