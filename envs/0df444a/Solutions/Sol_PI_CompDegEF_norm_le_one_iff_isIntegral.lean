-- Prove2me | solution 1 for PI.CompDegEF.norm_le_one_iff_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:35:10.889815+00:00
-- url     : https://prove2.me/submissions/682b2bc4-2225-414e-bab4-1fd97c001e98

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_DenseSurj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_MemIntegralClosureIffMemBall
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
namespace PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
variable {l : ℕ} [hl : Fact l.Prime]
private theorem spectralValue_le_one_iff_norm_coeff_le_one (P : ℚ_[l][X]) (hP : P.Monic) :
    spectralValue P ≤ 1 ↔ ∀ n, ‖P.coeff n‖ ≤ 1 := by
  constructor
  · intro h n
    by_cases hn : n < P.natDegree
    · have ht : spectralValueTerms P n ≤ 1 :=
        (le_ciSup (spectralValueTerms_bddAbove P) n).trans h
      rw [spectralValueTerms, if_pos hn] at ht
      have hexp : (0 : ℝ) < 1 / ((P.natDegree : ℝ) - n) := by
        have : (n : ℝ) < P.natDegree := by exact_mod_cast hn
        apply div_pos one_pos; linarith
      by_contra hc
      push_neg at hc
      exact absurd ht (not_le.mpr (Real.one_lt_rpow hc hexp))
    · rcases eq_or_lt_of_le (not_lt.mp hn) with h' | h'
      · rw [← h', hP.coeff_natDegree, norm_one]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h', norm_zero]; exact zero_le_one
  · intro h
    unfold spectralValue
    apply ciSup_le
    intro n
    simp only [spectralValueTerms]
    split_ifs with hn
    · have : (n : ℝ) < P.natDegree := by exact_mod_cast hn
      exact Real.rpow_le_one (norm_nonneg _) (h n) (div_nonneg zero_le_one (by linarith))
    · exact zero_le_one
end PI.CompDegEF
end

set_option autoImplicit false
open PI PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
variable {l : ℕ} [hl : Fact l.Prime]
namespace PI.CompDegEF
theorem _root_.solution (z : Om l) : ‖z‖ ≤ 1 ↔ IsIntegral ℤ_[l] z := by
  have hzQ : IsIntegral ℚ_[l] z := by
    first
      | exact Algebra.IsIntegral.isIntegral z
      | exact (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  have hnorm : ‖z‖ = spectralValue (minpoly ℚ_[l] z) := rfl
  rw [hnorm, spectralValue_le_one_iff_norm_coeff_le_one _ (minpoly.monic hzQ)]
  constructor
  · intro h
    have hlift : minpoly ℚ_[l] z ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hqmap, -, hqm⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic hlift (minpoly.monic hzQ)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hqmap, minpoly.aeval]
  · intro hz n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hz, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
end PI.CompDegEF
