-- Prove2me | solution 1 for P010.le_h_of_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:44:03.731184+00:00
-- url     : https://prove2.me/submissions/d097396d-3742-47fd-9104-642a1a94b05b

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_h_attained

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n k : ℕ)
    (hlower : ∀ a : List ℕ, IsPermutation n a → k ≤ adjacentCount a) :
    k ≤ h n := by
  obtain ⟨a, ha, hc⟩ := h_attained n
  rw [← hc]
  exact hlower a ha
end P010
