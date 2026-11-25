-- Prove2me | solution 1 for PI.SlopeSteps.nabla_gram_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:38:46.859239+00:00
-- url     : https://prove2.me/submissions/15d934fa-29f3-43ae-a84d-46104b5737a7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_MonomialFactorizationLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_StdSlopeLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_GramMatrixDuality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaGram
import Theorems.Thm_PI_SlopeSteps_factorial_mul_det_sq
import Theorems.Thm_PI_SlopeSteps_fockQ_eq_sum
import Theorems.Thm_Formalism_GradedWeylDivisibility_colSums
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_L2_DIV_we_intQ_apply
import Theorems.Thm_PI_SlopeSteps_hwNormPos
import Theorems.Thm_PI_SlopeSteps_linIndep_Q
import Theorems.Thm_PI_SlopeSteps_monomial_factorization_lower
import Theorems.Thm_PI_SlopeSteps_natPowPos
import Theorems.Thm_PI_SlopeSteps_sumNuZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open PI PI.SlopeSteps
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV Matrix
namespace PI.SlopeSteps
theorem _root_.solution : NablaGramLow := by
  intro N ν r e hν
  classical
  have hpos := hwNormPos ν
  set h := fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) with hh
  have hNpow := natPowPos N (∑ s, ν s) (sumNuZero ν)
  set A : ℚ := ((∏ s, (ν s).factorial : ℕ) : ℚ) / ((N : ℚ) ^ (∑ s, ν s) * h) with hA
  have hA0 : 0 ≤ A := div_nonneg (Nat.cast_nonneg _) (mul_pos hNpow hpos).le
  set S : Finset (Fin N × Fin N →₀ ℕ) :=
    Finset.univ.biUnion fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ).support with hS
  set Vz : Matrix S (Fin r) ℤ := Matrix.of fun m i => (e i : MvPolynomial (Fin N × Fin N) ℤ).coeff m.1 with hVz
  set V : Matrix S (Fin r) ℚ := Vz.map (Int.castRingHom ℚ) with hV
  set q : S → ℚ := fun m => ((∏ k ∈ m.1.support, (m.1 k).factorial : ℕ) : ℚ) / h with hq

  have hG : gramOf ν (fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ)) = Vᵀ * diagonal q * V := by
    ext i j
    have hsub : (map (Int.castRingHom ℚ) (e i : MvPolynomial (Fin N × Fin N) ℤ)).support ⊆ S :=
      (MvPolynomial.support_map_subset _ _).trans (by
        rw [hS]
        exact Finset.subset_biUnion_of_mem (fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ).support)
          (Finset.mem_univ i))
    simp only [gramOf, Matrix.of_apply]
    rw [fockQ_eq_sum _ _ S hsub, Finset.sum_div, ← Finset.sum_coe_sort S]
    rw [mul_apply]
    simp only [mul_diagonal, transpose_apply, hV, hVz, map_apply, of_apply, hq, coeff_map, eq_intCast]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← hh]
    ring

  have hqA : ∀ m : S, A ≤ q m := by
    intro m
    obtain ⟨i, -, hm⟩ := Finset.mem_biUnion.mp m.2
    have hcol := colSums ℤ N N ν _ (e i).2 m.1 hm
    have hT1 := monomial_factorization_lower N ν m.1 hcol
    have hT1q : ((∏ s, (ν s).factorial : ℕ) : ℚ) ≤
        (N : ℚ) ^ (∑ s, ν s) * ((∏ k ∈ m.1.support, (m.1 k).factorial : ℕ) : ℚ) := by
      exact_mod_cast hT1
    rw [hA, hq]
    rw [div_le_div_iff₀ (mul_pos hNpow hpos) hpos]
    calc ((∏ s, (ν s).factorial : ℕ) : ℚ) * h
        ≤ (N : ℚ) ^ (∑ s, ν s) * ((∏ k ∈ m.1.support, (m.1 k).factorial : ℕ) : ℚ) * h :=
          mul_le_mul_of_nonneg_right hT1q hpos.le
      _ = ((∏ k ∈ m.1.support, (m.1 k).factorial : ℕ) : ℚ) * ((N : ℚ) ^ (∑ s, ν s) * h) := by ring

  have hid1 := factorial_mul_det_sq r (fun _ => (1 : ℚ)) V
  rw [diagonal_one, Matrix.mul_one] at hid1
  simp only [Finset.prod_const_one, one_mul] at hid1
  have hfac : (0 : ℚ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hVVnn : 0 ≤ (Vᵀ * V).det := by
    have h0 : 0 ≤ (r.factorial : ℚ) * (Vᵀ * V).det := by
      rw [hid1]; exact Finset.sum_nonneg fun f _ => mul_self_nonneg _
    exact nonneg_of_mul_nonneg_right (by linarith) hfac
  have hind := linIndep_Q e
  have hVVne : (Vᵀ * V).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.mpr h0
    have h1 : dotProduct (V *ᵥ v) (V *ᵥ v) = 0 := by
      have h1' := congrArg (fun x => dotProduct v x) hv
      simp only [dotProduct_zero] at h1'
      rwa [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose] at h1'
    have h2 : V *ᵥ v = 0 := by
      funext m
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => mul_self_nonneg ((V *ᵥ v) m))).mp h1 m
        (Finset.mem_univ _)
      exact mul_self_eq_zero.mp h3
    have h3 : ∑ i, v i • intQ N N (e i : MvPolynomial (Fin N × Fin N) ℤ) = 0 := by
      ext m
      rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero]
      simp only [MvPolynomial.coeff_smul, smul_eq_mul, we_intQ_apply, MvPolynomial.coeff_map, eq_intCast]
      by_cases hm : m ∈ S
      · have h4 := congrFun h2 ⟨m, hm⟩
        simp only [mulVec, dotProduct, hV, hVz, map_apply, of_apply, Pi.zero_apply, eq_intCast] at h4
        rw [← h4]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      · refine Finset.sum_eq_zero fun i _ => ?_
        have h5 : (e i : MvPolynomial (Fin N × Fin N) ℤ).coeff m = 0 := by
          by_contra hc
          exact hm (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, MvPolynomial.mem_support_iff.mpr hc⟩)
        rw [h5, Int.cast_zero, mul_zero]
    exact hv0 (funext (Fintype.linearIndependent_iff.mp hind v h3))
  have hVVint : (Vᵀ * V).det = (((Vzᵀ * Vz).det : ℤ) : ℚ) := by
    have h6 := RingHom.map_det (Int.castRingHom ℚ) (Vzᵀ * Vz)
    rw [eq_intCast] at h6
    rw [h6, RingHom.mapMatrix_apply, Matrix.map_mul, transpose_map]
  have hVV1 : 1 ≤ (Vᵀ * V).det := by
    rw [hVVint] at hVVnn hVVne ⊢
    have hz : 0 < (Vzᵀ * Vz).det := by
      have := lt_of_le_of_ne hVVnn (Ne.symm hVVne)
      exact_mod_cast this
    exact_mod_cast hz

  have hid := factorial_mul_det_sq r q V
  have hprod : ∀ f : Fin r → S, A ^ r ≤ ∏ i, q (f i) := by
    intro f
    calc A ^ r = ∏ _i : Fin r, A := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ i, q (f i) := Finset.prod_le_prod (fun _ _ => hA0) (fun i _ => hqA (f i))
  have hmain : A ^ r * ((r.factorial : ℚ) * (Vᵀ * V).det) ≤
      (r.factorial : ℚ) * (Vᵀ * diagonal q * V).det := by
    rw [hid1, hid, Finset.mul_sum]
    exact Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_right (hprod f) (mul_self_nonneg _)
  rw [hG]
  have hAr : 0 ≤ A ^ r := pow_nonneg hA0 r
  nlinarith [mul_le_mul_of_nonneg_left hVV1 (mul_nonneg hAr hfac.le)]
end PI.SlopeSteps
