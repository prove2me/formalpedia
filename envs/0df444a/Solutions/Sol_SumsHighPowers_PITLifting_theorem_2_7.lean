-- Prove2me | solution 1 for SumsHighPowers.PITLifting.theorem_2_7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T21:15:23.916065+00:00
-- url     : https://prove2.me/submissions/6fc65451-a3b4-4bf0-8776-dbfbb415f700
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SumsHighPowers_PITLifting_numDistinctRoots
import Theorems.Thm_SumsHighPowers_PITLifting_theorem_2_7_of_linearIndependent
import Theorems.Thm_SumsHighPowers_PITLifting_theorem_2_7_of_not_linearIndependent

section
namespace SumsHighPowers.PITLifting

theorem chk_theorem_2_7 {F : Type*} [Field F] (D r : ℕ) (hr : 2 ≤ r)
    (hchar : ringChar F = 0 ∨ (r - 1) * D < ringChar F)
    (h₁ : Polynomial F) (h : Fin (r - 1) → Polynomial F)
    (hsum : ∑ i, h i = h₁)
    (hgcd : ∀ q : Polynomial F, (∀ i, q ∣ h i) → IsUnit q)
    (hdeg₁ : h₁.natDegree ≤ D) (hdeg : ∀ i, (h i).natDegree ≤ D)
    (hnonconst : 0 < h₁.natDegree ∨ ∃ i, 0 < (h i).natDegree)
    (hsubsum : ∀ T : Finset (Fin (r - 1)), T.Nonempty → ∑ i ∈ T, h i ≠ 0) :
    h₁.natDegree < (r - 2) * (numDistinctRoots h₁ + ∑ i, numDistinctRoots (h i)) := by
  by_cases hli : LinearIndependent F h
  · exact theorem_2_7_of_linearIndependent D r hr hchar h₁ h hsum hgcd hdeg₁ hdeg hnonconst
      hsubsum hli
  · exact theorem_2_7_of_not_linearIndependent D r hr hchar h₁ h hsum hgcd hdeg₁ hdeg hnonconst
      hsubsum hli

end SumsHighPowers.PITLifting
end

theorem solution : type_of% @SumsHighPowers.PITLifting.chk_theorem_2_7 := @SumsHighPowers.PITLifting.chk_theorem_2_7
