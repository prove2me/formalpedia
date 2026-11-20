-- Prove2me | solution 1 for RelatedSchedFPTAS796.Main.lemma_6_10
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-19T15:42:12.063385+00:00
-- url     : https://prove2.me/submissions/4c02db81-243f-47e5-ad21-b118550b29a3

import Mathlib

set_option maxHeartbeats 3200000
set_option autoImplicit false

open Finset
open scoped BigOperators Matrix

theorem solution {d : ℕ} (N : Fin d → ℝ) (hN : ∀ i, 0 < N i) (b : Fin d → Fin d → ℝ)
    (hbox : ∀ j i, |b j i| ≤ N i) (hli : LinearIndependent ℝ b) (x : Fin d → ℝ)
    (hx : ∀ i, |x i| ≤ N i * |(Matrix.of b).det| / ((d : ℝ) ^ d * ∏ i, N i)) :
    ∃ t : Fin d → ℝ, (∀ j, |t j| ≤ 1) ∧ x = ∑ j, t j • b j := by
  classical
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    refine ⟨fun j => 0, ?_, ?_⟩
    · intro j; exact j.elim0
    · funext i; exact i.elim0
  set B : Matrix (Fin d) (Fin d) ℝ := Matrix.of b with hB
  have hliB : LinearIndependent ℝ B.row := by
    simpa [hB] using hli
  have hdetB : B.det ≠ 0 := by
    have h1 : IsUnit B := Matrix.linearIndependent_rows_iff_isUnit.mp hliB
    have h2 : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp h1
    exact h2.ne_zero
  set A : Matrix (Fin d) (Fin d) ℝ := Bᵀ with hA
  have hdetA : A.det ≠ 0 := by
    rw [hA, Matrix.det_transpose]
    exact hdetB
  have hdet_eq : (Matrix.of b).det = A.det := by
    rw [hA, Matrix.det_transpose, ← hB]
  set t : Fin d → ℝ := A.det⁻¹ • Matrix.cramer A x with ht
  refine ⟨t, ?_, ?_⟩
  · -- bound on each coordinate
    intro j
    have hPpos : 0 < ∏ i, N i := Finset.prod_pos (fun i _ => hN i)
    have hPne : (∏ i, N i) ≠ 0 := ne_of_gt hPpos
    have hdre : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
    have hpowpos : (0 : ℝ) < (d : ℝ) ^ d := pow_pos hdre d
    set c : ℝ := |A.det| / ((d : ℝ) ^ d * ∏ i, N i) with hc
    have hc_nonneg : 0 ≤ c := by
      rw [hc]
      exact div_nonneg (abs_nonneg _) (le_of_lt (mul_pos hpowpos hPpos))
    have hentry : ∀ (σ : Equiv.Perm (Fin d)) (i : Fin d),
        |(A.updateCol j x) (σ i) i| ≤ (if i = j then c else 1) * N (σ i) := by
      intro σ i
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, Matrix.updateCol_self]
        have h1 := hx (σ i)
        rw [hdet_eq] at h1
        have hcN : c * N (σ i) = N (σ i) * |A.det| / ((d : ℝ) ^ d * ∏ i, N i) := by
          rw [hc]
          field_simp
        rw [hcN]
        exact h1
      · rw [if_neg hij, Matrix.updateCol_ne hij, one_mul]
        have hAij : A (σ i) i = b i (σ i) := by
          simp [hA, hB]
        rw [hAij]
        exact hbox i (σ i)
    have hprod_le : ∀ σ : Equiv.Perm (Fin d),
        ∏ i, |(A.updateCol j x) (σ i) i| ≤ c * ∏ i, N i := by
      intro σ
      calc ∏ i, |(A.updateCol j x) (σ i) i|
          ≤ ∏ i, ((if i = j then c else 1) * N (σ i)) := by
            apply Finset.prod_le_prod
            · intro i _; exact abs_nonneg _
            · intro i _
              apply le_trans (hentry σ i)
              apply mul_le_mul_of_nonneg_right _ (le_of_lt (hN (σ i)))
              by_cases h : i = j
              · simp [h, hc_nonneg]
              · simp [h]
        _ = (∏ i, (if i = j then c else 1)) * ∏ i, N (σ i) := Finset.prod_mul_distrib
        _ = c * ∏ i, N (σ i) := by rw [Fintype.prod_ite_eq' j (fun _ => c)]
        _ = c * ∏ i, N i := by rw [Equiv.prod_comp σ N]
    have hdetM_le : |(A.updateCol j x).det| ≤ (Nat.factorial d : ℝ) * (|A.det| / (d : ℝ) ^ d) := by
      have hleib : |(A.updateCol j x).det| ≤
          ∑ σ : Equiv.Perm (Fin d), ∏ i, |(A.updateCol j x) (σ i) i| := by
        rw [Matrix.det_apply']
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        apply Finset.sum_le_sum
        intro σ _
        rw [abs_mul, ← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one, one_mul,
          Finset.abs_prod]
      have hc_mul : c * ∏ i, N i = |A.det| / (d : ℝ) ^ d := by
        rw [hc]
        field_simp
      calc |(A.updateCol j x).det|
          ≤ ∑ σ : Equiv.Perm (Fin d), ∏ i, |(A.updateCol j x) (σ i) i| := hleib
        _ ≤ ∑ _σ : Equiv.Perm (Fin d), c * ∏ i, N i := by
            apply Finset.sum_le_sum
            intro σ _
            exact hprod_le σ
        _ = (Nat.factorial d : ℝ) * (c * ∏ i, N i) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
            simp [nsmul_eq_mul]
        _ = (Nat.factorial d : ℝ) * (|A.det| / (d : ℝ) ^ d) := by rw [hc_mul]
    have hfac : (Nat.factorial d : ℝ) ≤ (d : ℝ) ^ d := by
      have h := Nat.factorial_le_pow d
      exact_mod_cast h
    have hfrac : (Nat.factorial d : ℝ) / (d : ℝ) ^ d ≤ 1 := by
      rw [div_le_one hpowpos]
      exact hfac
    have hfin : (Nat.factorial d : ℝ) * (|A.det| / (d : ℝ) ^ d) ≤ |A.det| := by
      have hrew : (Nat.factorial d : ℝ) * (|A.det| / (d : ℝ) ^ d) =
          ((Nat.factorial d : ℝ) / (d : ℝ) ^ d) * |A.det| := by
        field_simp
      rw [hrew]
      exact mul_le_of_le_one_left (abs_nonneg _) hfrac
    have hdetM : |(A.updateCol j x).det| ≤ |A.det| := hdetM_le.trans hfin
    have htj : |t j| = |A.det|⁻¹ * |(A.updateCol j x).det| := by
      have htj' : t j = A.det⁻¹ * (A.updateCol j x).det := by
        rw [ht]
        simp [Matrix.cramer_apply]
      rw [htj', abs_mul, abs_inv]
    rw [htj]
    calc |A.det|⁻¹ * |(A.updateCol j x).det|
        ≤ |A.det|⁻¹ * |A.det| := by
          exact mul_le_mul_of_nonneg_left hdetM (by positivity)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt (abs_pos.mpr hdetA))
  · -- representation
    have hmul : A *ᵥ t = x := by
      rw [ht, Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul,
        inv_mul_cancel₀ hdetA, one_smul]
    funext i
    have h1 := congrFun hmul i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Finset.sum_apply, smul_eq_mul] at h1
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [← h1]
    apply Finset.sum_congr rfl
    intro j _
    have hAij : A i j = b j i := by
      simp [hA, hB]
    rw [hAij]
    ring
