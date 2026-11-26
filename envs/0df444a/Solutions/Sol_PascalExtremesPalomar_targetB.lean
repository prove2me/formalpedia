-- Prove2me | solution 1 for PascalExtremesPalomar.targetB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:12:58.818649+00:00
-- url     : https://prove2.me/submissions/bc2bcc97-a666-4dc9-bd3b-9b023ed8ba78

module
public import Definitions.Def_PascalExtremes
public import Definitions.Def_PascalExtremes_Solution
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
public import Theorems.Thm_PascalExtremes_targetB
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff



set_option autoImplicit true
@[expose] public section
public section
open PascalExtremesPalomar
namespace PascalExtremesPalomar
theorem _root_.solution
    {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    T p (p ^ a + 1) = p ^ (3 * a) + 1 := by
  simpa only [T, extremalRows, AdmissibleRow, G, admissibleIndices, rP,
    PascalExtremes.T, PascalExtremes.extremalRows,
    PascalExtremes.AdmissibleRow, PascalExtremes.G,
    PascalExtremes.admissibleIndices, PascalExtremes.rP] using
    (PascalExtremes.targetB hp ha)
end PascalExtremesPalomar
