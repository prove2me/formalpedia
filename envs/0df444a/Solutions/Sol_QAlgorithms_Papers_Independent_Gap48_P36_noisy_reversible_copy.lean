-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P36.noisy_reversible_copy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:51:09.547935+00:00
-- url     : https://prove2.me/submissions/24a5a9ca-e058-4061-9a32-3c76c3f3f313

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D E K L A2 B2 C2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype A2] [DecidableEq A2]

variable [Fintype B2] [DecidableEq B2] [Fintype C2] [DecidableEq C2]

open Matrix

theorem x8_complete [Nonempty A] (T : UnitaryBasis A K) (i j l m : A) :
    ∑ k, T.matrix k i j * star (T.matrix k l m) =
      if (i, j) = (l, m) then (Fintype.card A : ℂ) else 0 := by
  have hcard : Fintype.card K = Fintype.card (A × A) := by
    rw [T.cardinality, Fintype.card_prod, sq]
  let e : K ≃ A × A := Fintype.equivOfCardEq hcard
  obtain ⟨W, hW⟩ : ∃ W : Matrix (A × A) (A × A) ℂ, ∀ p q, W p q = T.matrix (e.symm q) p.1 p.2 :=
    ⟨Matrix.of fun p q => T.matrix (e.symm q) p.1 p.2, fun _ _ => rfl⟩
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hWW : Wᴴ * W = (Fintype.card A : ℂ) • 1 := by
    ext q q'
    have := T.orthogonal (e.symm q) (e.symm q')
    simp only [trace, diag, mul_apply, conjTranspose_apply] at this
    rw [mul_apply, Matrix.smul_apply, one_apply]
    simp only [conjTranspose_apply, hW, Fintype.sum_prod_type]
    rw [Finset.sum_comm] at this
    rw [this]
    by_cases h : q = q' <;> simp [h, e.symm.injective.eq_iff]
  have h1 : ((Fintype.card A : ℂ)⁻¹ • Wᴴ) * W = 1 := by
    rw [smul_mul_assoc, hWW, smul_smul, inv_mul_cancel₀ hd, one_smul]
  have h2 := mul_eq_one_comm.1 h1
  rw [mul_smul_comm] at h2
  have h3 : W * Wᴴ = (Fintype.card A : ℂ) • 1 := by
    have := congrArg (fun M => (Fintype.card A : ℂ) • M) h2
    simp only [smul_smul, mul_inv_cancel₀ hd, one_smul] at this
    exact this
  have := congrFun (congrFun h3 (i, j)) (l, m)
  rw [mul_apply, Matrix.smul_apply, one_apply] at this
  simp only [conjTranspose_apply, hW] at this
  rw [← e.symm.sum_comp (fun k => T.matrix k i j * star (T.matrix k l m))]
  rw [this]
  split_ifs <;> simp


theorem x8_main [Nonempty A] [Nonempty K] (T : UnitaryBasis A K) :
    ∃ U : Matrix K (A × A) ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      ∀ rho : Matrix A A ℂ, IsDensityMatrix rho →
        noisyComplement T.matrix rho =
          U * (((Fintype.card A : ℂ)⁻¹ • (1 : Matrix A A ℂ)) ⊗ₖ rho) * Uᴴ := by
  set d : ℂ := (Fintype.card A : ℂ) with hd_def
  have hd : d ≠ 0 := by rw [hd_def]; exact_mod_cast Fintype.card_ne_zero
  set s : ℂ := (Real.sqrt (Fintype.card A : ℝ) : ℂ) with hs_def
  have hs2 : s * s = d := by
    rw [hs_def, hd_def, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp
  have hs0 : s ≠ 0 := by intro h; rw [h, zero_mul] at hs2; exact hd hs2.symm
  have hss : star s = s := by rw [hs_def]; simp
  refine ⟨Matrix.of fun k (ba : A × A) => s⁻¹ * T.matrix k ba.1 ba.2, ?_, ?_, ?_⟩
  · ext p q
    rw [mul_apply, one_apply]
    simp only [conjTranspose_apply, of_apply, star_mul', star_inv₀, hss]
    have := x8_complete T q.1 q.2 p.1 p.2
    have e : ∑ k, s⁻¹ * star (T.matrix k p.1 p.2) * (s⁻¹ * T.matrix k q.1 q.2) =
        (s * s)⁻¹ * ∑ k, T.matrix k q.1 q.2 * star (T.matrix k p.1 p.2) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; field_simp
    rw [e, this, hs2]
    by_cases h : p = q
    · subst h; simp only [↓reduceIte]; rw [← hd_def]; exact inv_mul_cancel₀ hd
    · have h' : (q.1, q.2) ≠ (p.1, p.2) := fun h2 => h (by ext <;> simp_all)
      simp [h', h]
  · ext k k'
    rw [mul_apply, one_apply]
    simp only [conjTranspose_apply, of_apply, star_mul', star_inv₀, hss]
    have := T.orthogonal k' k
    simp only [trace, diag, mul_apply, conjTranspose_apply] at this
    have e : ∑ ba : A × A, s⁻¹ * T.matrix k ba.1 ba.2 * (s⁻¹ * star (T.matrix k' ba.1 ba.2)) =
        (s * s)⁻¹ * ∑ a, ∑ b, star (T.matrix k' b a) * T.matrix k b a := by
      rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_; field_simp
    rw [e, this, hs2]
    by_cases h : k = k'
    · subst h; simp only [↓reduceIte]; rw [← hd_def]; exact inv_mul_cancel₀ hd
    · simp [Ne.symm h, h]
  · intro rho _
    ext k k'
    simp only [noisyComplement, complementaryChannel, traceLeft, Matrix.of_apply, mul_apply,
      conjTranspose_apply, indexedKrausDilation, Matrix.smul_apply, smul_eq_mul, kroneckerMap_apply,
      one_apply, Fintype.sum_prod_type, star_mul', star_inv₀, hss]
    have hinv : s⁻¹ * s⁻¹ = d⁻¹ := by rw [← mul_inv, hs2]
    have hin : ∀ b a', ∑ x2, ∑ x3, s⁻¹ * T.matrix k x2 x3 * ((d⁻¹ * if x2 = b then 1 else 0) *
        rho x3 a') = s⁻¹ * d⁻¹ * ∑ j, T.matrix k b j * rho j a' := by
      intro b a'
      rw [Finset.sum_eq_single b]
      · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; simp; ring
      · intro x2 _ h; simp [h]
      · simp
    simp only [hin]
    have hc : (star (Fintype.card A : ℂ))⁻¹ = d⁻¹ := by rw [hd_def]; simp
    rw [hc, ← hd_def]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a' _ => ?_
    have : ∑ j, d⁻¹ * T.matrix k b j * rho j a' = d⁻¹ * ∑ j, T.matrix k b j * rho j a' := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
    rw [this]
    linear_combination -(d⁻¹ * (∑ j, T.matrix k b j * rho j a') * star (T.matrix k' b a')) * hinv

end QAlgorithms.Papers.Independent.Gap48.P36

open scoped Matrix Kronecker in
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P36 in
theorem solution {A K : Type*} [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K]
    [Nonempty A] [Nonempty K] (T : UnitaryBasis A K) :
    ∃ U : Matrix K (A × A) ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      ∀ rho : Matrix A A ℂ, IsDensityMatrix rho →
        noisyComplement T.matrix rho = U * (((Fintype.card A : ℂ)⁻¹ • (1 : Matrix A A ℂ)) ⊗ₖ rho) * Uᴴ :=
  x8_main T
