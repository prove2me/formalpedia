-- Prove2me | solution 1 for PascalExtremesPalomar.targetA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:10.035466+00:00
-- url     : https://prove2.me/submissions/bb7f9d1e-6596-45d0-b912-4eb93ce7f7e4

module
public import Definitions.Def_PascalExtremes
public import Definitions.Def_PascalExtremes_Solution
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
public import Theorems.Thm_PascalExtremes_targetA
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff



set_option autoImplicit true
@[expose] public section
public section
open PascalExtremesPalomar
namespace PascalExtremesPalomar
theorem _root_.solution
    {p m : ℕ} (hp : p.Prime) (hm2 : 2 ≤ m) (hpm : ¬ p ∣ m) :
    IsGreatest
      {v : ℕ | ∃ N, AdmissibleRow m N ∧
        padicValNat p (G N m) = v}
      (rP p m) := by
  simpa only [AdmissibleRow, G, admissibleIndices, rP,
    PascalExtremes.AdmissibleRow, PascalExtremes.G,
    PascalExtremes.admissibleIndices, PascalExtremes.rP] using
    (PascalExtremes.targetA hp hm2 hpm)
end PascalExtremesPalomar
