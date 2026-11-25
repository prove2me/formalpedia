-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gauss_exists_div_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:17:46.416093+00:00
-- url     : https://prove2.me/submissions/fb402d93-cc67-46ed-9cd5-cdb90a175130

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValExists
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValLeIffDivMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (hgen : IntermediateField.adjoin Ω (Set.range t) = ⊤) (z : U) :
    ∃ p q : MvPolynomial σ Ω, aeval t q ≠ 0 ∧ z = aeval t p / aeval t q := by
  have hz : z ∈ IntermediateField.adjoin Ω (Set.range t) := by rw [hgen]; trivial
  obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
  rw [Algebra.adjoin_range_eq_range_aeval] at hr hs
  obtain ⟨p, rfl⟩ := hr
  obtain ⟨q, rfl⟩ := hs
  by_cases hq : aeval t q = 0
  · refine ⟨0, 1, by simp, ?_⟩
    simp [hq]
  · exact ⟨p, q, hq, rfl⟩
end ReciprocityTheory.MultiplicativeHeights
