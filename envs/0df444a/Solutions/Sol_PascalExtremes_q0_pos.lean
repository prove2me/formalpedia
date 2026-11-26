-- Prove2me | solution 1 for PascalExtremes.q0_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:00:35.207271+00:00
-- url     : https://prove2.me/submissions/7c48faf4-17de-4065-97b7-c05d2e9ed0c4

module
public import Definitions.Def_PascalExtremes_TargetAAttainment
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetB
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff



set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    0 < q0 p a := by
  simp only [q0]
  omega
end PascalExtremes
