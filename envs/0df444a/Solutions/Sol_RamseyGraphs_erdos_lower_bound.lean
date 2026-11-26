-- Prove2me | solution 1 for RamseyGraphs.erdos_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:20:30.775865+00:00
-- url     : https://prove2.me/submissions/cc657d24-488d-45e1-8fa3-d53a44c57e3a

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds
public import Definitions.Def_RamseyGraphs_Solution
public import Theorems.Thm_RamseyLib_erdos_lower_bound


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyGraphs
namespace RamseyGraphs
theorem _root_.solution (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (hn : (n : ℝ) ≤ 2 ^ ((k : ℝ) / 2)) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k :=
  RamseyLib.erdos_lower_bound k hk n hn
end RamseyGraphs
