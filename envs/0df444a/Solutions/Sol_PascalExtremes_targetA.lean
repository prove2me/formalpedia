-- Prove2me | solution 1 for PascalExtremes.targetA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:00:47.832975+00:00
-- url     : https://prove2.me/submissions/7b43e47c-2569-4816-ac87-5c641abe93ae

module
public import Definitions.Def_PascalExtremes_TargetA
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetAAttainment
public import Theorems.Thm_PascalExtremes_targetA_attainment
public import Theorems.Thm_PascalExtremes_targetA_upper


set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution
    {p m : ℕ} (hp : p.Prime) (hm2 : 2 ≤ m) (hpm : ¬ p ∣ m) :
    IsGreatest
      {v : ℕ | ∃ N, AdmissibleRow m N ∧
        padicValNat p (G N m) = v}
      (rP p m) := by
  obtain ⟨N, hrow, hval⟩ := targetA_attainment hp hm2 hpm
  refine ⟨⟨N, hrow, hval⟩, ?_⟩
  intro v hv
  rcases hv with ⟨M, hMrow, rfl⟩
  exact targetA_upper hp hm2 hpm hMrow
end PascalExtremes
