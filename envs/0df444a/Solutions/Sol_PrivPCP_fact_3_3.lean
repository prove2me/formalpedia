-- Prove2me | solution 1 for PrivPCP.fact_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:44:37.530914+00:00
-- url     : https://prove2.me/submissions/8c6d4b95-c80a-4cc9-b1d9-1bbbf9a3e8d9

import Mathlib
import Definitions.Def_PrivPCP_gridQ

namespace PrivPCP.Fact33Aux

open MvPolynomial

variable {F : Type} [Field F] {k : ℕ}

lemma degreeOf_monomial_le' (s : Fin k →₀ ℕ) (c : F) (j : Fin k) :
    (monomial s c : MvPolynomial (Fin k) F).degreeOf j ≤ s j := by
  rw [degreeOf_le_iff]
  intro m hm
  have := support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  rw [this]

lemma degreeOf_aeval_X_le (i j : Fin k) (p : Polynomial F) :
    (Polynomial.aeval (X i : MvPolynomial (Fin k) F) p).degreeOf j ≤
      if j = i then p.natDegree else 0 := by
  rw [Polynomial.aeval_eq_sum_range]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun n hn => ?_)
  rw [MvPolynomial.smul_eq_C_mul]
  refine (degreeOf_C_mul_le _ _ _).trans ?_
  split_ifs with h
  · subst h
    rw [degreeOf_X_self_pow]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  · rw [degreeOf_X_pow_of_ne _ h]

lemma le_degreeOf_of_mem {R : MvPolynomial (Fin k) F} {e : Fin k →₀ ℕ} (he : e ∈ R.support)
    (j : Fin k) : e j ≤ R.degreeOf j :=
  (degreeOf_le_iff.mp le_rfl) e he

/-- quotient of division by `Z(X_i)` -/
noncomputable def divQ (i : Fin k) (Z : Polynomial F) (R : MvPolynomial (Fin k) F) :
    MvPolynomial (Fin k) F :=
  ∑ e ∈ R.support, monomial (Finsupp.update e i 0) (R.coeff e) *
    Polynomial.aeval (X i) (Polynomial.X ^ (e i) /ₘ Z)

/-- remainder of division by `Z(X_i)` -/
noncomputable def divR (i : Fin k) (Z : Polynomial F) (R : MvPolynomial (Fin k) F) :
    MvPolynomial (Fin k) F :=
  ∑ e ∈ R.support, monomial (Finsupp.update e i 0) (R.coeff e) *
    Polynomial.aeval (X i) (Polynomial.X ^ (e i) %ₘ Z)

lemma div_eq (i : Fin k) (Z : Polynomial F) (R : MvPolynomial (Fin k) F) :
    R = Polynomial.aeval (X i) Z * divQ i Z R + divR i Z R := by
  conv_lhs => rw [as_sum R]
  unfold divQ divR
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have h1 : (monomial e (R.coeff e) : MvPolynomial (Fin k) F) =
      monomial (Finsupp.update e i 0) (R.coeff e) * X i ^ (e i) := by
    have hs : Finsupp.update e i 0 + Finsupp.single i (e i) = e := by
      ext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Finsupp.update_apply, hj, Finsupp.single_apply, Ne.symm hj]
    rw [X_pow_eq_monomial, monomial_mul, mul_one, hs]
  have h2 : (X i : MvPolynomial (Fin k) F) ^ (e i) =
      Polynomial.aeval (X i) (Polynomial.X ^ (e i) %ₘ Z + Z * (Polynomial.X ^ (e i) /ₘ Z)) := by
    rw [Polynomial.modByMonic_add_div]; simp
  rw [h1, h2, map_add, map_mul]
  ring

lemma divQ_degreeOf (i : Fin k) (Z : Polynomial F) (hZ : Z.Monic) (R : MvPolynomial (Fin k) F)
    (j : Fin k) :
    (divQ i Z R).degreeOf j ≤ if j = i then R.degreeOf i - Z.natDegree else R.degreeOf j := by
  unfold divQ
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun e he => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  refine (add_le_add (degreeOf_monomial_le' _ _ _) (degreeOf_aeval_X_le _ _ _)).trans ?_
  split_ifs with h
  · subst h
    have h0 : (Finsupp.update e j 0) j = 0 := by simp
    rw [h0, zero_add]
    rw [Polynomial.natDegree_divByMonic _ hZ, Polynomial.natDegree_X_pow]
    exact Nat.sub_le_sub_right (le_degreeOf_of_mem he j) _
  · simp only [Finsupp.update_apply, h, if_false, add_zero]
    exact le_degreeOf_of_mem he j

lemma divR_degreeOf_ne (i : Fin k) (Z : Polynomial F) (R : MvPolynomial (Fin k) F)
    (j : Fin k) (hj : j ≠ i) : (divR i Z R).degreeOf j ≤ R.degreeOf j := by
  unfold divR
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun e he => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  refine (add_le_add (degreeOf_monomial_le' _ _ _) (degreeOf_aeval_X_le _ _ _)).trans ?_
  simp only [Finsupp.update_apply, hj, if_false, add_zero]
  exact le_degreeOf_of_mem he j

lemma divR_degreeOf_self (i : Fin k) (Z : Polynomial F) (hZ : Z.Monic) (hZ1 : Z ≠ 1)
    (R : MvPolynomial (Fin k) F) : (divR i Z R).degreeOf i < Z.natDegree := by
  have hpos : 0 < Z.natDegree := by
    rcases Nat.eq_zero_or_pos Z.natDegree with h | h
    · exact absurd (Polynomial.eq_one_of_monic_natDegree_zero hZ h) hZ1
    · exact h
  have : (divR i Z R).degreeOf i ≤ Z.natDegree - 1 := by
    unfold divR
    refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun e he => ?_)
    refine (degreeOf_mul_le _ _ _).trans ?_
    refine (add_le_add (degreeOf_monomial_le' _ _ _) (degreeOf_aeval_X_le _ _ _)).trans ?_
    have h0 : (Finsupp.update e i 0) i = 0 := by simp
    simp only [h0, if_true, zero_add]
    have := Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ (e i)) hZ hZ1
    omega
  omega

end PrivPCP.Fact33Aux

open PrivPCP MvPolynomial PrivPCP.Fact33Aux

theorem solution {F : Type} [Field F] [Fintype F] {k : ℕ} (H : Fin k → Finset F) (a : Fin k → ℕ)
    (ha : ∀ i, (H i).card ≤ a i) (R : MvPolynomial (Fin k) F) (hR : ∀ i, R.degreeOf i ≤ a i) :
    (∀ x : Fin k → F, (∀ i, x i ∈ H i) → MvPolynomial.eval x R = 0) ↔
      ∃ Q : Fin k → MvPolynomial (Fin k) F, (∀ i, Q i ∈ gridQ H a i) ∧
        R = ∑ i, gridZ H i * Q i := by
  classical
  constructor
  swap
  · rintro ⟨Q, -, rfl⟩ x hx
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul, gridZ, map_prod]
    rw [Finset.prod_eq_zero (hx i) (by simp), zero_mul]
  intro hvan
  -- the univariate vanishing polynomials
  let Zp : Fin k → Polynomial F := fun i => ∏ c ∈ H i, (Polynomial.X - Polynomial.C c)
  have hZmon : ∀ i, (Zp i).Monic := fun i => Polynomial.monic_prod_of_monic _ _
    (fun c _ => Polynomial.monic_X_sub_C c)
  have hZdeg : ∀ i, (Zp i).natDegree = (H i).card := by
    intro i
    simp only [Zp]
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C c)]
    simp
  have hZev : ∀ i, Polynomial.aeval (X i : MvPolynomial (Fin k) F) (Zp i) = gridZ H i := by
    intro i
    simp only [Zp, gridZ, map_prod, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      MvPolynomial.algebraMap_eq]
  -- the empty case
  by_cases hemp : ∃ i, H i = ∅
  · obtain ⟨i₀, hi₀⟩ := hemp
    refine ⟨Pi.single i₀ R, ?_, ?_⟩
    · intro i
      by_cases hi : i = i₀
      · subst hi
        refine ⟨?_, ?_⟩
        · simp [hi₀, hR]
        · intro j _; simpa using hR j
      · refine ⟨?_, ?_⟩ <;> simp [Pi.single_apply, hi]
    · rw [Finset.sum_eq_single i₀]
      · simp [gridZ, hi₀]
      · intro b _ hb; simp [Pi.single_apply, hb]
      · simp
  push Not at hemp
  have hne : ∀ i, (H i).Nonempty := hemp
  have hZ1 : ∀ i, Zp i ≠ 1 := by
    intro i h
    have := hZdeg i
    rw [h, Polynomial.natDegree_one] at this
    exact (Finset.card_pos.mpr (hne i)).ne' this.symm
  -- invariant: after processing variables `< j`
  have key : ∀ j : ℕ, j ≤ k → ∃ Q : Fin k → MvPolynomial (Fin k) F,
      (∀ i, Q i ∈ gridQ H a i) ∧
      (∀ i : Fin k, (R - ∑ i, gridZ H i * Q i).degreeOf i ≤
        if i.val < j then (H i).card - 1 else a i) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨0, fun i => ⟨by simp, fun j _ => by simp⟩, fun i => ?_⟩
      simpa using hR i
    | succ j ih =>
      intro hj
      obtain ⟨Q, hQ, hRem⟩ := ih (Nat.le_of_succ_le hj)
      set i₀ : Fin k := ⟨j, hj⟩
      set Rem := R - ∑ i, gridZ H i * Q i
      refine ⟨Q + Pi.single i₀ (divQ i₀ (Zp i₀) Rem), ?_, ?_⟩
      · intro i
        have hdq := divQ_degreeOf i₀ (Zp i₀) (hZmon i₀) Rem
        by_cases hi : i = i₀
        · subst hi
          have hr := hRem i₀
          simp only [i₀, lt_irrefl, if_false] at hr
          refine ⟨?_, ?_⟩
          · simp only [Pi.add_apply, Pi.single_eq_same]
            refine (degreeOf_add_le _ _ _).trans (max_le (hQ _).1 ?_)
            refine (hdq _).trans ?_
            simp only [if_true, hZdeg]
            exact Nat.sub_le_sub_right hr _
          · intro j' hj'
            simp only [Pi.add_apply, Pi.single_eq_same]
            refine (degreeOf_add_le _ _ _).trans (max_le ((hQ _).2 j' hj') ?_)
            refine (hdq j').trans ?_
            simp only [hj', if_false]
            refine (hRem j').trans ?_
            split_ifs
            · have := ha j'; omega
            · exact le_rfl
        · simp only [Pi.add_apply, Pi.single_eq_of_ne hi, add_zero]
          exact hQ i
      · intro i
        have hsplit : R - ∑ i, gridZ H i * ((Q + Pi.single i₀ (divQ i₀ (Zp i₀) Rem) : Fin k → MvPolynomial (Fin k) F) i) =
            divR i₀ (Zp i₀) Rem := by
          have hd := div_eq i₀ (Zp i₀) Rem
          rw [hZev] at hd
          simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
          have hs : ∑ x, gridZ H x *
              (Pi.single i₀ (divQ i₀ (Zp i₀) Rem) : Fin k → MvPolynomial (Fin k) F) x =
              gridZ H i₀ * divQ i₀ (Zp i₀) Rem := by
            rw [Finset.sum_eq_single i₀ (fun b _ hb => by simp [Pi.single_apply, hb])
              (by simp), Pi.single_eq_same]
          rw [hs]
          have : Rem = R - ∑ i, gridZ H i * Q i := rfl
          rw [← sub_sub, ← this]
          rw [sub_eq_iff_eq_add]; rw [add_comm]; exact hd
        rw [hsplit]
        by_cases hi : i = i₀
        · subst hi
          have := divR_degreeOf_self i₀ (Zp i₀) (hZmon i₀) (hZ1 i₀) Rem
          rw [hZdeg] at this
          have hlt : (i₀ : Fin k).val < j + 1 := Nat.lt_succ_self j
          rw [if_pos hlt]
          omega
        · refine (divR_degreeOf_ne i₀ (Zp i₀) Rem i hi).trans ?_
          refine (hRem i).trans ?_
          have hiv : i.val ≠ j := fun h => hi (Fin.ext h)
          by_cases hlt : i.val < j
          · simp [hlt, Nat.lt_succ_of_lt hlt]
          · have : ¬ i.val < j + 1 := by omega
            simp [hlt, this]
  obtain ⟨Q, hQ, hRem⟩ := key k le_rfl
  refine ⟨Q, hQ, ?_⟩
  have h0 : R - ∑ i, gridZ H i * Q i = 0 := by
    apply eq_zero_of_eval_zero_at_prod_finset _ H
    · intro i
      have := hRem i
      simp only [i.isLt, if_true] at this
      have := Finset.card_pos.mpr (hne i)
      omega
    · intro x hx
      rw [map_sub, hvan x hx, map_sum, zero_sub, neg_eq_zero]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_mul, gridZ, map_prod, Finset.prod_eq_zero (hx i) (by simp), zero_mul]
  exact sub_eq_zero.mp h0

