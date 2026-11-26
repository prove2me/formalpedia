-- Prove2me | solution 1 for P2M_Erdos266__A_le__L_9d33a2dc6fc9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:48:48.048014+00:00
-- url     : https://prove2.me/submissions/4fd3c17a-e687-430c-9942-e3ee1aebcd45

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
theorem _root_.solution (d : ℕ) : εA d ≤ εL d := by
  cases d with
  | zero => exact le_rfl
  | succ d => exact min_le_right _ _
end Erdos266
