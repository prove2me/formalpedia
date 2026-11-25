-- Prove2me | solution 1 for PI.WHw.bC_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:06:21.927307+00:00
-- url     : https://prove2.me/submissions/11df7c5c-6a81-4bdf-ad97-c6e3fc183b29

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ClosedEqNablaC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ClosedEqNabla
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_BCRowGenMonomial
import Theorems.Thm_PI_WHw_bC_coeff_euler
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL
noncomputable section
open PI PI.WHw
namespace PI.WHw
theorem _root_.solution {r n : ℕ} (M : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ)) (hM : RowDivClosed M)
    (a : Fin r) (V : Finset ℕ) :
    ∀ f ∈ M, (∀ m ∈ f.support, Finsupp.weight (lgraded_wa a) m ∈ V) →
      ∀ t, weightedHomogeneousComponent (lgraded_wa a) t f ∈ M := by
  classical
  induction V using Finset.induction_on
  next =>
    intro f _ hV t
    have hf0 : f = 0 := by
      ext m
      by_contra hm
      have h1 := hV m (MvPolynomial.mem_support_iff.mpr (by simpa using hm))
      simp at h1
    rw [hf0, map_zero]
    exact M.zero_mem
  next s V hs ih =>
    intro f hf hV t
    set g := rowDiv ℂ a a 1 f - (s : ℂ) • f with hg
    have hgM : g ∈ M := M.sub_mem (hM a a 1 f hf) (M.smul_mem _ hf)
    have hcg : ∀ m, MvPolynomial.coeff m g =
        ((Finsupp.weight (lgraded_wa a) m : ℂ) - s) * MvPolynomial.coeff m f := by
      intro m
      rw [hg, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, bC_coeff_euler, smul_eq_mul]
      ring
    have hgV : ∀ m ∈ g.support, Finsupp.weight (lgraded_wa a) m ∈ V := by
      intro m hm
      rw [MvPolynomial.mem_support_iff, hcg] at hm
      have hfm : MvPolynomial.coeff m f ≠ 0 := right_ne_zero_of_mul hm
      have hws : (Finsupp.weight (lgraded_wa a) m : ℂ) - s ≠ 0 := left_ne_zero_of_mul hm
      rcases Finset.mem_insert.mp (hV m (MvPolynomial.mem_support_iff.mpr hfm)) with h | h
      · exact (hws (by rw [h, sub_self])).elim
      · exact h
    have hIH := ih g hgM hgV
    have hcomp : ∀ t', t' ≠ s → weightedHomogeneousComponent (lgraded_wa a) t' f ∈ M := by
      intro t' ht'
      have e : weightedHomogeneousComponent (lgraded_wa a) t' f =
          ((t' : ℂ) - s)⁻¹ • weightedHomogeneousComponent (lgraded_wa a) t' g := by
        ext m
        rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_weightedHomogeneousComponent,
          MvPolynomial.coeff_weightedHomogeneousComponent, hcg]
        split_ifs with hm
        · rw [hm, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀, one_mul]
          exact sub_ne_zero.mpr (by exact_mod_cast ht')
        · simp
      rw [e]
      exact M.smul_mem _ (hIH t')
    by_cases hts : t = s
    · rw [hts]
      have hsum : weightedHomogeneousComponent (lgraded_wa a) s f =
          f - ∑ t' ∈ V, weightedHomogeneousComponent (lgraded_wa a) t' f := by
        ext m
        rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sum]
        simp only [MvPolynomial.coeff_weightedHomogeneousComponent]
        rw [Finset.sum_ite_eq]
        by_cases hm : MvPolynomial.coeff m f = 0
        · simp [hm]
        · rcases Finset.mem_insert.mp (hV m (MvPolynomial.mem_support_iff.mpr hm)) with h | h
          · simp [h, hs]
          · have hne : Finsupp.weight (lgraded_wa a) m ≠ s := fun e => hs (e ▸ h)
            simp [h, hne]
      rw [hsum]
      exact M.sub_mem hf (M.sum_mem fun t' ht' => hcomp t' (fun e => hs (e ▸ ht')))
    · exact hcomp t hts
end PI.WHw
