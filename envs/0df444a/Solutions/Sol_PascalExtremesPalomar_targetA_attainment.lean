-- Prove2me | solution 1 for PascalExtremesPalomar.targetA_attainment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:09.455244+00:00
-- url     : https://prove2.me/submissions/1034928c-cade-404d-8631-f77e047b84db

module
public import Definitions.Def_PascalExtremes
public import Definitions.Def_PascalExtremes_Solution
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
public import Theorems.Thm_PascalExtremes_targetA_attainment
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff



set_option autoImplicit true
@[expose] public section
public section
open PascalExtremesPalomar
namespace PascalExtremesPalomar
theorem _root_.solution
    {p m : ℕ} (hp : p.Prime) (hm2 : 2 ≤ m) (hpm : ¬ p ∣ m) :
    ∃ N, AdmissibleRow m N ∧
      padicValNat p (G N m) = rP p m := by
  simpa only [AdmissibleRow, G, admissibleIndices, rP,
    PascalExtremes.AdmissibleRow, PascalExtremes.G,
    PascalExtremes.admissibleIndices, PascalExtremes.rP] using
    (PascalExtremes.targetA_attainment hp hm2 hpm)
end PascalExtremesPalomar
