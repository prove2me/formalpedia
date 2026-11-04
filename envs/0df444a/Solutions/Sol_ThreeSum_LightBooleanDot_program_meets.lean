-- Prove2me | solution 1 for ThreeSum.LightBooleanDot.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:19:01.485995+00:00
-- url     : https://prove2.me/submissions/5b271718-9df8-4cfe-9e0b-235808c434d3

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f

set_option autoImplicit false
open ThreeSum ThreeSum.LightBooleanDot
open Light Finset
open scoped BigOperators
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightBooleanDot
theorem _root_.solution
    {μ : ℕ → ℤ} {srcA srcB n : ℕ} (f g : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hA : srcA+n ≤ lim.space) (hB : srcB+n ≤ lim.space)
    (hreadA : ∀ i < n, μ (srcA+i) = (f i : ℤ))
    (hreadB : ∀ i < n, μ (srcB+i) = (g i : ℤ))
    (hf : ∀ i < n, f i ≤ 1) (hg : ∀ i < n, g i ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim program 0 d [srcA,srcB,n] μ (time n)
      (fun r μ' => r = (dot f g n : ℤ) ∧ μ' = μ) :=
  meets rfl f g hw hA hB hreadA hreadB hf hg hword
end ThreeSum.LightBooleanDot
