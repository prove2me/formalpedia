-- Prove2me | solution 1 for P2M_Auto_aux_add_inf__657294d4941d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:45:21.936462+00:00
-- url     : https://prove2.me/submissions/c1c03951-e3f9-4620-a0cc-20539f53fe66

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace Auto
theorem _root_.solution {ι : Type*} (q : Finset ι) (hq : q.Nonempty)
    (f : ι → ℝ) (a : ℝ) :
    a + q.inf' hq f = q.inf' hq (fun i ↦ a + f i) :=
  map_finset_inf' (OrderIso.addLeft a) hq f
end Auto
