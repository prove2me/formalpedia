-- Prove2me | solution 1 for P010.P010_h_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:53:03.556293+00:00
-- url     : https://prove2.me/submissions/783a45ff-d0d7-438a-bf01-c2f16b94c036

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_le_h_of_lower_bound
public import Theorems.Thm_P010_P010_universal_lower_bound

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) (hn : 4 ≤ n) :
    target n ≤ h n := by
  exact le_h_of_lower_bound n (target n)
    (fun a ha => P010_universal_lower_bound n hn a ha)
end P010
