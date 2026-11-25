-- Prove2me | solution 1 for PI.PolynomialProperness.isoCore
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:47:44.19957+00:00
-- url     : https://prove2.me/submissions/f627ca33-17e2-4465-bfe4-66d251682052

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_IsoRightInv
import Theorems.Thm_PI_PolynomialProperness_CoreW_psd_image
import Theorems.Thm_PI_PolynomialProperness_CoreW_gram_image
import Theorems.Thm_PI_PolynomialProperness_CoreW_orth_bound
import Theorems.Thm_PI_PolynomialProperness_CoreW_final_alg
import Theorems.Thm_PI_PolynomialProperness_CoreW_eN_add
import Theorems.Thm_PI_PolynomialProperness_CoreW_eN_nonneg
import Theorems.Thm_PI_PolynomialProperness_CoreW_eN_smul
import Theorems.Thm_PI_PolynomialProperness_CoreW_eN_sq
import Theorems.Thm_PI_PolynomialProperness_CoreW_eN_sub
import Theorems.Thm_PI_PolynomialProperness_CoreW_eN_sum
import Theorems.Thm_PI_PolynomialProperness_CoreW_herm_iso
import Theorems.Thm_PI_PolynomialProperness_CoreW_herm_le
import Theorems.Thm_PI_PolynomialProperness_CoreW_proj_bound
import Theorems.Thm_PI_PolynomialProperness_CoreW_proj_orth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness
open CoreW
namespace PI.PolynomialProperness
theorem _root_.solution : IsoCore := by
  intro n H ι _ _ m hH hHH hdet hpsd
  obtain ⟨Γi, hΓi⟩ : ∃ Γi, Γi = (gramOf H m)⁻¹ := ⟨_, rfl⟩
  have hG : gramOf H m * Γi = 1 := by
    rw [hΓi]
    exact Matrix.mul_nonsing_inv _ hdet
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ j, ∑ k, ‖Γi j k‖ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => norm_nonneg _
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (Fintype.card ι : ℝ) * A := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by
    rw [hD]
    exact mul_nonneg (Nat.cast_nonneg _) hA0
  have hAD : A ≤ D := by
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h0
    · haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp h0
      have hA' : A = 0 := by
        rw [hA]
        simp
      rw [hA']
      exact hD0
    · have h1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast h0
      rw [hD]
      nlinarith
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℝ, R0 = ∑ k, eN (m k) := ⟨_, rfl⟩
  have hR00 : 0 ≤ R0 := by
    rw [hR0]
    exact Finset.sum_nonneg fun k _ => eN_nonneg _
  have hmR : ∀ k, eN (m k) ≤ R0 := fun k => by
    rw [hR0]
    exact Finset.single_le_sum (f := fun k => eN (m k)) (fun k _ => eN_nonneg _) (Finset.mem_univ k)
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = 1 + (Fintype.card ι : ℝ) * A * (R0 * R0) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by
    have := mul_nonneg (mul_nonneg (Nat.cast_nonneg (Fintype.card ι)) hA0) (mul_self_nonneg R0)
    rw [hE]
    linarith
  refine ⟨2 * D ^ 2 * R0 ^ 2 + 2 * (1 + D) * E ^ 2, fun s hs K hK hsm x => ?_⟩
  obtain ⟨p, hp⟩ : ∃ p, p = proj H Γi m x := ⟨_, rfl⟩
  obtain ⟨xo, hxo⟩ : ∃ xo, xo = x - p := ⟨_, rfl⟩
  have hxo_orth : ∀ j, herm H xo (m j) = 0 := fun j => by
    rw [hxo, hp]
    exact proj_orth H Γi m hG x j
  have hsx : s *ᵥ x = s *ᵥ p + s *ᵥ xo := by
    rw [hxo, Matrix.mulVec_sub]
    abel
  have hX : 0 ≤ nsq x := by
    rw [← eN_sq]
    positivity

  have hcoef : ∑ i, ‖coef H Γi m x i‖ ≤ A * (eN x * R0) := by
    calc ∑ i, ‖coef H Γi m x i‖ ≤ ∑ i, ∑ k, ‖Γi i k‖ * (eN x * R0) :=
          Finset.sum_le_sum fun i _ => by
            show ‖∑ k, Γi i k * herm H x (m k)‖ ≤ _
            calc ‖∑ k, Γi i k * herm H x (m k)‖ ≤ ∑ k, ‖Γi i k * herm H x (m k)‖ :=
                  norm_sum_le _ _
              _ ≤ ∑ k, ‖Γi i k‖ * (eN x * R0) := Finset.sum_le_sum fun k _ => by
                  rw [norm_mul]
                  exact mul_le_mul_of_nonneg_left ((herm_le H hH hHH x (m k)).trans
                    (mul_le_mul_of_nonneg_left (hmR k) (eN_nonneg x))) (norm_nonneg _)
      _ = A * (eN x * R0) := by
          rw [hA, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
  have hsK : ∀ k, eN (s *ᵥ m k) ≤ Real.sqrt K := fun k =>
    (le_abs_self _).trans (Real.abs_le_sqrt (by rw [eN_sq]; exact hsm k))
  have hsp : eN (s *ᵥ p) ≤ A * (eN x * R0) * Real.sqrt K := by
    have e : s *ᵥ p = ∑ i, coef H Γi m x i • (s *ᵥ m i) := by
      rw [hp, proj, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul]
    rw [e]
    calc eN (∑ i, coef H Γi m x i • (s *ᵥ m i)) ≤ ∑ i, eN (coef H Γi m x i • (s *ᵥ m i)) :=
          eN_sum _ _
      _ ≤ ∑ i, ‖coef H Γi m x i‖ * Real.sqrt K := Finset.sum_le_sum fun i _ => by
          rw [eN_smul]
          exact mul_le_mul_of_nonneg_left (hsK i) (norm_nonneg _)
      _ = (∑ i, ‖coef H Γi m x i‖) * Real.sqrt K := (Finset.sum_mul _ _ _).symm
      _ ≤ A * (eN x * R0) * Real.sqrt K := mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)
  have ha : nsq (s *ᵥ p) ≤ D ^ 2 * R0 ^ 2 * K * nsq x := by
    rw [← eN_sq, ← eN_sq x]
    have h1 : eN (s *ᵥ p) ^ 2 ≤ (A * (eN x * R0) * Real.sqrt K) ^ 2 :=
      pow_le_pow_left₀ (eN_nonneg _) hsp 2
    have h2 : (A * (eN x * R0) * Real.sqrt K) ^ 2 = A ^ 2 * R0 ^ 2 * K * eN x ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hK]
      ring
    have h3 : A ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hA0 hAD 2
    have h4 : 0 ≤ R0 ^ 2 * K * eN x ^ 2 := mul_nonneg (mul_nonneg (sq_nonneg _) hK) (sq_nonneg _)
    nlinarith

  have hGs : gramOf H (fun i => s *ᵥ m i) * Γi = 1 := by
    rw [gram_image H s hs m]
    exact hG
  have hpsd' : ∀ w, (∀ i, herm H w ((fun i => s *ᵥ m i) i) = 0) → 0 ≤ (herm H w w).re :=
    fun w hw => psd_image H s hHH hs m hpsd w hw
  have hv : ∀ j, herm H (s *ᵥ xo) ((fun i => s *ᵥ m i) j) = 0 := fun j => by
    show herm H (s *ᵥ xo) (s *ᵥ m j) = 0
    rw [herm_iso H s hs]
    exact hxo_orth j
  have hob := orth_bound H hH hHH Γi (fun i => s *ᵥ m i) hGs (Real.sqrt K) (Real.sqrt_nonneg _)
    hsK hpsd' (s *ᵥ xo) hv
  rw [Real.mul_self_sqrt hK, herm_iso H s hs, ← hA, ← hD] at hob
  have hpb := proj_bound H hH hHH Γi m R0 hR00 hmR x
  rw [← hA, ← hp] at hpb
  have hxoN : eN xo ≤ E * eN x := by
    calc eN xo ≤ eN x + eN p := by
          rw [hxo]
          exact eN_sub _ _
      _ ≤ eN x + (Fintype.card ι : ℝ) * (A * (eN x * R0)) * R0 := by linarith
      _ = E * eN x := by
          rw [hE]
          ring
  have hre : (herm H xo xo).re ≤ E ^ 2 * nsq x := by
    calc (herm H xo xo).re ≤ ‖herm H xo xo‖ := Complex.re_le_norm _
      _ ≤ eN xo * eN xo := herm_le H hH hHH xo xo
      _ ≤ (E * eN x) * (E * eN x) :=
          mul_le_mul hxoN hxoN (eN_nonneg _) (mul_nonneg hE0 (eN_nonneg _))
      _ = E ^ 2 * nsq x := by
          rw [← eN_sq x]
          ring
  have hb : nsq (s *ᵥ xo) ≤ (1 + D * K) * (E ^ 2 * nsq x) := by
    have hc0 : 0 ≤ 1 + D * K := by
      have := mul_nonneg hD0 hK
      linarith
    exact hob.trans (mul_le_mul_of_nonneg_left hre hc0)
  have hsum : nsq (s *ᵥ x) ≤ 2 * nsq (s *ᵥ p) + 2 * nsq (s *ᵥ xo) := by
    rw [hsx, ← eN_sq, ← eN_sq (s *ᵥ p), ← eN_sq (s *ᵥ xo)]
    have h1 := eN_add (s *ᵥ p) (s *ᵥ xo)
    have h2 := eN_nonneg (s *ᵥ p + s *ᵥ xo)
    nlinarith [sq_nonneg (eN (s *ᵥ p) - eN (s *ᵥ xo)), eN_nonneg (s *ᵥ p), eN_nonneg (s *ᵥ xo)]
  have hfin := final_alg D R0 E K (1 + D * K) (nsq x) (nsq (s *ᵥ p)) (nsq (s *ᵥ xo)) hD0 hK hX
    rfl ha hb
  linarith
end PI.PolynomialProperness
