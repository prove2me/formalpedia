-- Prove2me | solution 1 for ULHC.ncomp_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:44.758111+00:00
-- url     : https://prove2.me/submissions/d83aa573-0e34-4571-8802-bb234988ebcc

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F F' : Finset Edge}
    (h : ∀ x ∈ V, ∀ y ∈ V, Conn F x y ↔ Conn F' x y) : ncomp V F = ncomp V F' := by
  unfold ncomp
  congr 1
  apply Finset.image_congr
  intro x hx
  unfold cls
  apply Finset.filter_congr
  intro y hy
  exact h x hx y hy
end ULHC
