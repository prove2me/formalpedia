-- Prove2me | solution 1 for PI.OpWords.bihom_zero_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:01:05.47004+00:00
-- url     : https://prove2.me/submissions/08293357-e5bb-4152-b19e-8dbb401f83d6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PolarizationBihomogeneous
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PairingPowMemSymbolRange
import Theorems.Thm_PI_OpWords_wtXSum
import Theorems.Thm_PI_OpWords_wtXiSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finsupp
noncomputable section
open PI PI.OpWords
variable (K : Type) [Field K] [CharZero K] (k d : ℕ)
namespace PI.OpWords
theorem _root_.solution (g : Pol K k) (hg : g ∈ Bihom K k 0) : ∃ r : K, g = C r := by
  have hg' : g ∈ weightedHomogeneousSubmodule K (wx k) 0 ⊓ weightedHomogeneousSubmodule K (wxi k) 0 := hg
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hg'
  rw [mem_weightedHomogeneousSubmodule] at h1 h2
  refine ⟨coeff 0 g, ?_⟩
  ext m
  rw [coeff_C]
  split_ifs with hm
  · rw [← hm]
  · by_contra hne
    apply hm
    have e1 := h1 hne
    have e2 := h2 hne
    rw [wtXSum] at e1
    rw [wtXiSum] at e2
    ext v
    rcases v with i | i
    · have h3 := (Finset.sum_eq_zero_iff.1 e1) i (Finset.mem_univ i)
      simp [h3]
    · have h3 := (Finset.sum_eq_zero_iff.1 e2) i (Finset.mem_univ i)
      simp [h3]
end PI.OpWords
