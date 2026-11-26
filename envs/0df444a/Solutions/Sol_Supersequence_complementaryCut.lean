-- Prove2me | solution 1 for Supersequence.complementaryCut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:50.495883+00:00
-- url     : https://prove2.me/submissions/c243ab15-0841-4f39-949d-43932a388b18

import Std
import Definitions.Def_Frequency
import Theorems.Thm_Supersequence_cut

set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
namespace Supersequence
theorem _root_.solution {x : α} {l g r : List α} (hx : x ∉ g)
    (univ : Covers (fun _ => True) (l ++ (g ++ r))) (S : α → Prop) :
    Covers (fun a => a ≠ x ∧ S a) l ∨ Covers (fun a => a ≠ x ∧ ¬ S a) r := by
  classical
  apply Classical.or_iff_not_imp_left.mpr
  intro fail v hv av
  simp only [Covers, Classical.not_forall] at fail
  obtain ⟨u, hu, au, missing⟩ := fail
  have distinct : (u ++ x :: v).Nodup := by
    simp only [nodup_append, nodup_cons, mem_cons]
    grind
  exact (cut hx (univ _ distinct (by simp))).resolve_left missing
end Supersequence
