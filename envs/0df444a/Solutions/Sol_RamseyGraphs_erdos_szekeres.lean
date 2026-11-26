-- Prove2me | solution 1 for RamseyGraphs.erdos_szekeres
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:18:42.839511+00:00
-- url     : https://prove2.me/submissions/faf597ae-4bef-4642-93fe-1fb7b5caafa4

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds
public import Definitions.Def_RamseyGraphs_Solution
public import Theorems.Thm_RamseyLib_erdos_szekeres


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyGraphs
namespace RamseyGraphs
theorem _root_.solution {V : Type*} [Fintype V] (G : SimpleGraph V) (s t : ℕ) (hs : 1 ≤ s)
    (ht : 1 ≤ t) (hV : (s + t - 2).choose (s - 1) ≤ Fintype.card V) :
    ¬ G.CliqueFree s ∨ ¬ Gᶜ.CliqueFree t :=
  RamseyLib.erdos_szekeres G s t hs ht hV
end RamseyGraphs
