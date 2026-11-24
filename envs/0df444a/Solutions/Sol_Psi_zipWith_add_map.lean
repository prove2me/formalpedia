-- Prove2me | solution 1 for Psi.zipWith_add_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:34:15.878115+00:00
-- url     : https://prove2.me/submissions/e1159824-4803-449d-8733-621f9ae40c03

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (X Y : List ℕ) (c : ℕ) :
    List.zipWith (· + ·) (X.map (· + c)) Y = (List.zipWith (· + ·) X Y).map (· + c) := by
  induction X generalizing Y with
  | nil => simp
  | cons x xs ih => cases Y with
    | nil => simp
    | cons y ys => simp only [List.map_cons, List.zipWith_cons_cons, ih]; ring_nf
end Psi
