-- Prove2me | solution 1 for Psi.len_filter_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:55:15.989802+00:00
-- url     : https://prove2.me/submissions/8480289b-18f9-488a-b460-1059716ab493

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w : List Bool) :
    (w.filter (· = false)).length + (w.filter id).length = w.length := by
  induction w with
  | nil => simp
  | cons a t ih => cases a <;> (simp_all; omega)
end Psi
