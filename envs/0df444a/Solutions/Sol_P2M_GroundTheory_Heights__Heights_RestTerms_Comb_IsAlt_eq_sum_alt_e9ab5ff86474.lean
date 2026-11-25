-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_eq_sum_alt_e9ab5ff86474
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:33:57.195163+00:00
-- url     : https://prove2.me/submissions/814fd97e-656c-4246-9248-5aa8a3c331aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_alt_isAlt_9f813e5016fd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_alt_of_strictAnti_30339c9c8742
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_sub_e9512e82a813
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_smul_d8ece51c2123
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_sum_a5fe0c99cdcf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_eq_zero_of_cf_ddde2895fcf8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
variable {m : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.Comb
namespace IsAlt
theorem _root_.solution {P : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) :
    P = ∑ d ∈ P.support.filter (fun d : Fin m →₀ ℕ => StrictAnti (⇑d)), coeff d P • alt (⇑d) := by
  rw [← sub_eq_zero]
  refine (hP.sub (IsAlt.sum _ fun d _ => (alt_isAlt _).smul _)).eq_zero_of_cf fun l hl => ?_
  unfold cf
  rw [coeff_sub, coeff_sum, sub_eq_zero]
  have hterm : ∀ d ∈ P.support.filter (fun d : Fin m →₀ ℕ => StrictAnti (⇑d)),
      coeff (ex l) (coeff d P • alt (⇑d)) = if d = ex l then coeff d P else 0 := by
    intro d hd
    rw [Finset.mem_filter] at hd
    have := cf_alt_of_strictAnti hl hd.2
    unfold cf at this
    rw [coeff_smul, this, smul_eq_mul]
    by_cases hdl : d = ex l
    · subst hdl; simp
    · rw [if_neg, if_neg hdl, mul_zero]
      intro h; apply hdl; ext i; simp [h]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  split_ifs with hmem
  · rfl
  · rw [Finset.mem_filter, not_and] at hmem
    by_contra hne
    exact hmem (mem_support_iff.mpr hne) (by simpa using hl)
end IsAlt
end GroundTheory.Heights₂.Heights.RestTerms.Comb
