-- Prove2me | solution 1 for PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.divT_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:00:22.614477+00:00
-- url     : https://prove2.me/submissions/0b16c7ed-d1c4-4a10-ad81-3beaeafee8da

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_IsWeightedHomogeneousPairingLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
theorem _root_.solution (d : ℕ) (hd : 1 ≤ d) (f : Pol K 1) (hf : f ∈ Bihom K 1 d) : tt K 1 ∣ f := by
  have hf' : f ∈ weightedHomogeneousSubmodule K (wx 1) d ⊓ weightedHomogeneousSubmodule K (wxi 1) d := hf
  have hx := (Submodule.mem_inf.1 hf').1
  have hxi := (Submodule.mem_inf.1 hf').2
  rw [mem_weightedHomogeneousSubmodule] at hx hxi
  obtain ⟨s, hs⟩ : ∃ s : Fin 1 ⊕ Fin 1 →₀ ℕ,
      s = Finsupp.single (Sum.inl 0) 1 + Finsupp.single (Sum.inr 0) 1 := ⟨_, rfl⟩
  rw [f.as_sum]
  refine Finset.dvd_sum fun m hm => ?_
  have h1 := hx (mem_support_iff.1 hm)
  have h2 := hxi (mem_support_iff.1 hm)
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, wx, wxi, Fintype.sum_sum_type] at h1 h2
  have hsm : s ≤ m := by
    rw [hs, Finsupp.le_def]
    intro v
    rcases v with i | i <;> obtain rfl := Subsingleton.elim i 0 <;> simp <;> omega
  have key : monomial m (coeff m f) = tt K 1 * monomial (m - s) (coeff m f) := by
    simp only [tt, Fin.sum_univ_one, X, monomial_mul, one_mul]
    rw [← hs, add_tsub_cancel_of_le hsm]
  rw [key]
  exact dvd_mul_right _ _
end PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
