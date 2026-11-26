-- Prove2me | solution 1 for P2M_Erdos266__A_succ_le_342abca4b5cd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:49:06.528547+00:00
-- url     : https://prove2.me/submissions/9ec37bb8-d103-434b-aba6-2e1df730a625

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution (d : ℕ) : εA (d + 1) ≤ εA d := min_le_left _ _
end Erdos266
