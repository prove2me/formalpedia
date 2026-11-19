-- Prove2me | solution 1 for QAOAE3Lin2.General.eq_41
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T04:28:18.819961+00:00
-- url     : https://prove2.me/submissions/97965e5e-4f1b-4100-89fc-bbfc9b069ee7

import Mathlib
import Definitions.Def_QAOAE3Lin2_General_Setting

open QAOAE3Lin2.General Polynomial

private lemma chebyshev_T_coeff01 (n : ℕ) :
    (Chebyshev.T ℝ (n : ℤ)).coeff 0 = (if Even n then (-1 : ℝ) ^ (n / 2) else 0) ∧
    (Chebyshev.T ℝ (n : ℤ)).coeff 1 = (if Even n then 0 else (-1 : ℝ) ^ (n / 2) * (n : ℝ)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simp [Chebyshev.T_zero, coeff_one]
    · simp [Chebyshev.T_one]
    · have heq : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
      have hrec := Chebyshev.T_add_two ℝ (n : ℤ)
      have ih0 := ih n (by omega)
      have ih1 := ih (n + 1) (by omega)
      have hT : Chebyshev.T ℝ ((n + 2 : ℕ) : ℤ) =
          2 * X * Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ) - Chebyshev.T ℝ (n : ℤ) := by
        rw [heq, hrec]
        push_cast
        ring_nf
      rw [hT]
      have h2X0 : (2 * X * Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).coeff 0 = 0 := by
        have hmul : 2 * X * Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ) =
            X * (2 * Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)) := by ring
        rw [hmul, coeff_X_mul_zero]
      have h2X1 : (2 * X * Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).coeff 1 =
          2 * (Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).coeff 0 := by
        have hmul : 2 * X * Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ) =
            X * (2 * Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)) := by ring
        rw [hmul, coeff_X_mul, coeff_ofNat_mul]
      rw [coeff_sub, h2X0, zero_sub, coeff_sub, h2X1, ih0.1, ih0.2, ih1.1]
      by_cases hn : Even n
      · have hn1 : ¬ Even (n + 1) := by simpa [Nat.even_add_one] using hn
        have hn2 : Even (n + 2) := by simpa [Nat.even_add] using hn
        have hdiv : (n + 2) / 2 = n / 2 + 1 := by omega
        simp only [hn, hn1, hn2, ↓reduceIte, hdiv, pow_succ]
        ring_nf
        simp
      · have hn1 : Even (n + 1) := by simpa [Nat.even_add_one] using hn
        have hn2 : ¬ Even (n + 2) := by simpa [Nat.even_add] using hn
        have hdiv1 : (n + 1) / 2 = n / 2 + 1 := by
          obtain ⟨m, rfl⟩ := Nat.not_even_iff_odd.mp hn
          omega
        have hdiv2 : (n + 2) / 2 = n / 2 + 1 := by omega
        simp only [hn, hn1, hn2, ↓reduceIte, hdiv1, hdiv2, pow_succ]
        push_cast
        ring_nf
        simp

private lemma eq_39_helper (k : ℕ) (hk : Odd k) (a : ℕ → ℝ) :
    ∃ r ∈ Finset.range (k + 1), 1 / (k : ℝ) ≤
      |Real.cos (Real.pi * r / k) + ∑ j ∈ Finset.Icc 2 k, a j * Real.cos (Real.pi * r / k) ^ j| := by
  by_cases hk1_eq : k = 1
  · subst hk1_eq
    exact ⟨0, by simp, by simp⟩
  by_contra hlt
  push Not at hlt
  have hk_ge3 : 3 ≤ k := by
    obtain ⟨t, rfl⟩ := hk
    omega
  have hk_pos : 0 < k := by omega
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk_pos
  let P : ℝ[X] := X + ∑ j ∈ Finset.Icc 2 k, C (a j) * X ^ j
  have hP_eval : ∀ x : ℝ, P.eval x = x + ∑ j ∈ Finset.Icc 2 k, a j * x ^ j := by
    intro x
    simp [P, eval_finsetSum]
  have hP_deg : P.natDegree ≤ k := by
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · simp; omega
    · refine (natDegree_sum_le _ _).trans (Finset.sup_le fun j hj => ?_)
      refine (natDegree_C_mul_le _ _).trans ?_
      simp [(Finset.mem_Icc.mp hj).2]
  have hP0 : P.coeff 0 = 0 := by
    simp only [P, finsetSum_coeff, coeff_add, coeff_X_zero, coeff_C_mul_X_pow, zero_add]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj0 : 0 ≠ j := by omega
    simp [hj0]
  have hP1 : P.coeff 1 = 1 := by
    simp only [P, finsetSum_coeff, coeff_add, coeff_X_one, coeff_C_mul_X_pow]
    have hsum0 : (∑ j ∈ Finset.Icc 2 k, if 1 = j then a j else 0) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
      have hj1 : 1 ≠ j := by omega
      simp [hj1]
    rw [hsum0, add_zero]
  let s : ℝ := (-1 : ℝ) ^ (k / 2)
  have hs_sq : s * s = 1 := by simp [s, ← pow_add, ← two_mul]
  let Q : ℝ[X] := C (1 / (k : ℝ)) * Chebyshev.T ℝ (k : ℤ) - C s * P
  have hQ_deg : Q.natDegree ≤ k := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_C_mul_le _ _).trans ?_
      rw [Chebyshev.natDegree_T]
      simp
    · exact (natDegree_C_mul_le _ _).trans hP_deg
  have hk_not_even : ¬ Even k := Nat.not_even_iff_odd.mpr hk
  have hT01 := chebyshev_T_coeff01 k
  simp only [hk_not_even, ↓reduceIte] at hT01
  have hQ0 : Q.coeff 0 = 0 := by
    simp [Q, hT01.1, hP0]
  have hQ1 : Q.coeff 1 = 0 := by
    simp only [Q, coeff_sub, coeff_C_mul, hT01.2, hP1, mul_one]
    have hk_ne : (k : ℝ) ≠ 0 := hkR.ne'
    calc (1 / (k : ℝ)) * (s * (k : ℝ)) - s
        = s * ((k : ℝ) / (k : ℝ)) - s := by ring
      _ = 0 := by rw [div_self hk_ne]; ring
  let x : ℕ → ℝ := fun r => Real.cos (Real.pi * r / k)
  have hQ_sign : ∀ r ∈ Finset.range (k + 1), 0 < (-1 : ℝ) ^ r * Q.eval (x r) := by
    intro r hr
    have hT_eval : (Chebyshev.T ℝ (k : ℤ)).eval (x r) = (-1 : ℝ) ^ r := by
      simp only [x, Chebyshev.T_real_cos]
      have heq : (((k : ℤ) : ℝ)) * (Real.pi * r / k) = r * Real.pi := by
        push_cast
        field_simp [hkR.ne']
      rw [heq, Real.cos_nat_mul_pi]
    have hQ_eval : Q.eval (x r) = (-1 : ℝ) ^ r / (k : ℝ) - s * P.eval (x r) := by
      simp [Q, eval_sub, eval_mul, eval_C, hT_eval]
      ring
    have hP_lt : |s * P.eval (x r)| < 1 / (k : ℝ) := by
      rw [abs_mul]
      have hs_abs : |s| = 1 := by simp [s]
      rw [hs_abs, one_mul, hP_eval]
      exact hlt r hr
    have hbound := (abs_lt.mp hP_lt).2
    have hbound2 := (abs_lt.mp hP_lt).1
    rw [hQ_eval, mul_sub]
    have hpow : (-1 : ℝ) ^ r * ((-1 : ℝ) ^ r / (k : ℝ)) = 1 / (k : ℝ) := by
      rw [mul_div_assoc', ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [hpow]
    have hprod_lt : (-1 : ℝ) ^ r * (s * P.eval (x r)) < 1 / (k : ℝ) := by
      rcases neg_one_pow_eq_or ℝ r with h | h <;> rw [h] <;> linarith
    linarith
  have hQ_ne : Q ≠ 0 := by
    intro h0
    have := hQ_sign 0 (Finset.mem_range.mpr (by omega))
    rw [h0, eval_zero, mul_zero] at this
    linarith
  -- Write Q = X^2 * R with R.natDegree ≤ k - 2
  have hdiv : X ^ 2 ∣ Q := by
    rw [X_pow_dvd_iff]
    intro d hd
    interval_cases d
    · exact hQ0
    · exact hQ1
  obtain ⟨R, hQR⟩ := hdiv
  have hR_ne : R ≠ 0 := by
    intro h0; apply hQ_ne; rw [hQR, h0, mul_zero]
  have hR_deg : R.natDegree ≤ k - 2 := by
    have hX2 : (X ^ 2 : ℝ[X]) ≠ 0 := pow_ne_zero 2 X_ne_zero
    have hdeg_eq : Q.natDegree = 2 + R.natDegree := by
      rw [hQR, natDegree_mul hX2 hR_ne, natDegree_X_pow]
    omega
  -- Construct k - 1 distinct roots of R in (-1, 1) \ {0}
  let m : ℕ := k / 2
  have hk_eq : k = 2 * m + 1 := by
    obtain ⟨t, ht⟩ := hk
    omega
  let I : Finset ℕ := (Finset.range k).erase m
  have hI_card : I.card = k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range]
  have hx_anti : StrictAntiOn x (Finset.range (k + 1) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have ha0 : 0 ≤ Real.pi * (a : ℝ) / k := by positivity
    have hbpi : Real.pi * (b : ℝ) / k ≤ Real.pi := by
      rw [div_le_iff₀ hkR]
      have hbk : (b : ℝ) ≤ k := Nat.cast_le.mpr (by omega)
      nlinarith [Real.pi_pos]
    have hlt_ang : Real.pi * (a : ℝ) / k < Real.pi * (b : ℝ) / k := by
      refine div_lt_div_of_pos_right ?_ hkR
      exact mul_lt_mul_of_pos_left (Nat.cast_lt.mpr hab) Real.pi_pos
    exact Real.strictAntiOn_cos ⟨ha0, (lt_of_lt_of_le hlt_ang hbpi).le⟩
      ⟨(le_trans ha0 hlt_ang.le), hbpi⟩ hlt_ang
  have hroot : ∀ r ∈ I, ∃ y : ℝ, x (r + 1) < y ∧ y < x r ∧ y ≠ 0 ∧ R.eval y = 0 := by
    intro r hr
    have hr_lt : r < k := Finset.mem_range.mp (Finset.mem_erase.mp hr).2
    have hr_ne : r ≠ m := (Finset.mem_erase.mp hr).1
    have hxr1_lt : x (r + 1) < x r :=
      hx_anti (Finset.mem_range.mpr (by omega)) (Finset.mem_range.mpr (by omega)) (by omega)
    have hs1 := hQ_sign r (Finset.mem_range.mpr (by omega))
    have hs2 := hQ_sign (r + 1) (Finset.mem_range.mpr (by omega))
    have h0_mem : (0 : ℝ) ∈ Set.Icc (Q.eval (x (r + 1))) (Q.eval (x r)) ∨
        (0 : ℝ) ∈ Set.Icc (Q.eval (x r)) (Q.eval (x (r + 1))) := by
      rcases neg_one_pow_eq_or ℝ r with h | h
      · have h' : (-1 : ℝ) ^ (r + 1) = -1 := by rw [pow_succ, h]; ring
        rw [h, one_mul] at hs1
        rw [h', neg_one_mul] at hs2
        exact Or.inl ⟨by linarith, by linarith⟩
      · have h' : (-1 : ℝ) ^ (r + 1) = 1 := by rw [pow_succ, h]; ring
        rw [h, neg_one_mul] at hs1
        rw [h', one_mul] at hs2
        exact Or.inr ⟨by linarith, by linarith⟩
    have hcont : ContinuousOn (fun t => Q.eval t) (Set.Icc (x (r + 1)) (x r)) :=
      Q.continuous.continuousOn
    obtain ⟨y, hy_mem, hy_eq⟩ : ∃ y ∈ Set.Icc (x (r + 1)) (x r), Q.eval y = 0 := by
      rcases h0_mem with h0 | h0
      · exact intermediate_value_Icc hxr1_lt.le hcont h0
      · exact intermediate_value_Icc' hxr1_lt.le hcont h0
    have hy_lt1 : x (r + 1) < y := lt_of_le_of_ne hy_mem.1 (by
      rintro rfl
      rcases neg_one_pow_eq_or ℝ (r + 1) with h | h <;> rw [h, hy_eq, mul_zero] at hs2 <;> linarith)
    have hy_lt2 : y < x r := lt_of_le_of_ne hy_mem.2 (by
      rintro rfl
      rcases neg_one_pow_eq_or ℝ r with h | h <;> rw [h, hy_eq, mul_zero] at hs1 <;> linarith)
    have hy_ne0 : y ≠ 0 := by
      rcases lt_or_gt_of_ne hr_ne with hrm | hrm
      · have h1 : Real.pi * ((r + 1 : ℕ) : ℝ) / k < Real.pi / 2 := by
          rw [div_lt_div_iff₀ hkR (by norm_num)]
          have h2 : 2 * (r + 1) < k := by omega
          have h2R : (2 : ℝ) * ((r + 1 : ℕ) : ℝ) < k := by exact_mod_cast h2
          nlinarith [Real.pi_pos]
        have hpos : 0 < x (r + 1) := Real.cos_pos_of_mem_Ioo
          ⟨by linarith [div_nonneg (mul_nonneg Real.pi_pos.le (Nat.cast_nonneg (r + 1))) hkR.le, Real.pi_pos], h1⟩
        linarith
      · have h1 : Real.pi / 2 < Real.pi * (r : ℝ) / k := by
          rw [div_lt_div_iff₀ (by norm_num) hkR]
          have h2 : k < 2 * r := by omega
          have h2R : (k : ℝ) < 2 * (r : ℝ) := by exact_mod_cast h2
          nlinarith [Real.pi_pos]
        have h2 : Real.pi * (r : ℝ) / k ≤ Real.pi := by
          rw [div_le_iff₀ hkR]
          have hrk : (r : ℝ) ≤ k := by exact_mod_cast hr_lt.le
          nlinarith [Real.pi_pos]
        have hneg : x r < 0 := by
          have hlt0 : Real.pi - Real.pi * (r : ℝ) / k < Real.pi / 2 := by linarith
          have hle0 : -(Real.pi / 2) < Real.pi - Real.pi * (r : ℝ) / k := by linarith [Real.pi_pos]
          have hpos_cos : 0 < Real.cos (Real.pi - Real.pi * (r : ℝ) / k) :=
            Real.cos_pos_of_mem_Ioo ⟨hle0, hlt0⟩
          rw [Real.cos_pi_sub] at hpos_cos
          simp only [x]
          linarith
        linarith
    have hRy : R.eval y = 0 := by
      have hQ0y : (X ^ 2 * R).eval y = 0 := by rw [← hQR]; exact hy_eq
      rw [eval_mul, eval_pow, eval_X] at hQ0y
      exact (mul_eq_zero.mp hQ0y).resolve_left (pow_ne_zero 2 hy_ne0)
    exact ⟨y, hy_lt1, hy_lt2, hy_ne0, hRy⟩
  choose y hy1 hy2 _ hyR using hroot
  let S : Finset ℝ := I.image (fun r => if hr : r ∈ I then y r hr else 0)
  have hS_inj : ∀ r₁ ∈ I, ∀ r₂ ∈ I,
      (if hr₁ : r₁ ∈ I then y r₁ hr₁ else 0) = (if hr₂ : r₂ ∈ I then y r₂ hr₂ else 0) → r₁ = r₂ := by
    intro r₁ hr₁ r₂ hr₂ heq
    rw [dif_pos hr₁, dif_pos hr₂] at heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h12 | h12
    · have hxr : x r₂ ≤ x (r₁ + 1) := by
        by_cases he : r₂ = r₁ + 1
        · subst he; exact le_rfl
        · exact (hx_anti (Finset.mem_range.mpr (by have := (Finset.mem_erase.mp hr₁).2; rw [Finset.mem_range] at this; omega))
            (Finset.mem_range.mpr (by have := (Finset.mem_erase.mp hr₂).2; rw [Finset.mem_range] at this; omega))
            (by omega)).le
      linarith [hy1 r₁ hr₁, hy2 r₂ hr₂]
    · have hxr : x r₁ ≤ x (r₂ + 1) := by
        by_cases he : r₁ = r₂ + 1
        · subst he; exact le_rfl
        · exact (hx_anti (Finset.mem_range.mpr (by have := (Finset.mem_erase.mp hr₂).2; rw [Finset.mem_range] at this; omega))
            (Finset.mem_range.mpr (by have := (Finset.mem_erase.mp hr₁).2; rw [Finset.mem_range] at this; omega))
            (by omega)).le
      linarith [hy1 r₂ hr₂, hy2 r₁ hr₁]
  have hS_card : S.card = I.card := by
    rw [Finset.card_image_of_injOn]
    intro r₁ hr₁ r₂ hr₂ heq
    exact hS_inj r₁ (Finset.mem_coe.mp hr₁) r₂ (Finset.mem_coe.mp hr₂) heq
  have hS_sub : S.val ≤ R.roots := by
    rw [Multiset.le_iff_subset S.nodup]
    intro z hz
    have hz' : z ∈ S := hz
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz'
    rw [dif_pos hr, mem_roots hR_ne, IsRoot]
    exact hyR r hr
  have hcard_le : S.card ≤ R.natDegree :=
    (Multiset.card_le_card hS_sub).trans (card_roots' R)
  have hk1 : k - 1 ≤ k - 2 := by
    rw [← hI_card, ← hS_card]
    exact hcard_le.trans hR_deg
  omega

theorem solution {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool) (D : ℕ)
    (hD : 1 ≤ D) (k : ℕ) (hk : Odd k) :
    ∃ r ∈ Finset.range (k + 1), (m : ℝ) / (20 * Real.sqrt D * k) ≤
      |(m : ℝ) / 2 * gammaGrid D k r + PkSum tri rhs k (gammaGrid D k r)| := by
  by_cases hm0 : m = 0
  · subst hm0
    exact ⟨0, by simp, by simp⟩
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hD_pos : (0 : ℝ) < D := Nat.cast_pos.mpr (by omega)
  have hsqrt_pos : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD_pos
  have hden_pos : 0 < 10 * Real.sqrt D := by positivity
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by rintro rfl; exact Nat.not_odd_zero hk))
  let c : ℕ → ℝ := fun j =>
    if 3 ≤ j ∧ Odd j then
      ∑ i : Fin m, (1 / 8 : ℝ) * sgn rhs i * ((-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ) *
        avgZ (fun x =>
          let d := sgn rhs i
          let c₁ := cPoly tri rhs i 0 x
          let c₂ := cPoly tri rhs i 1 x
          let c₃ := cPoly tri rhs i 2 x
          (d + c₁ + c₂ + c₃) ^ j + (d + c₁ - c₂ - c₃) ^ j +
            (d - c₁ + c₂ - c₃) ^ j + (d - c₁ - c₂ + c₃) ^ j))
    else 0
  have hPkSum_eq : ∀ γ : ℝ, PkSum tri rhs k γ = ∑ j ∈ Finset.Icc 2 k, c j * γ ^ j := by
    intro γ
    simp only [PkSum, Pk]
    have hswap : ∀ i : Fin m,
        (1 / 8 : ℝ) * sgn rhs i *
          (∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
            γ ^ j * (-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ) *
              avgZ (fun x =>
                let d := sgn rhs i
                let c₁ := cPoly tri rhs i 0 x
                let c₂ := cPoly tri rhs i 1 x
                let c₃ := cPoly tri rhs i 2 x
                (d + c₁ + c₂ + c₃) ^ j + (d + c₁ - c₂ - c₃) ^ j +
                  (d - c₁ + c₂ - c₃) ^ j + (d - c₁ - c₂ + c₃) ^ j)) =
        ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j),
          ((1 / 8 : ℝ) * sgn rhs i * ((-1 : ℝ) ^ ((j - 1) / 2) / (j.factorial : ℝ) *
            avgZ (fun x =>
              let d := sgn rhs i
              let c₁ := cPoly tri rhs i 0 x
              let c₂ := cPoly tri rhs i 1 x
              let c₃ := cPoly tri rhs i 2 x
              (d + c₁ + c₂ + c₃) ^ j + (d + c₁ - c₂ - c₃) ^ j +
                (d - c₁ + c₂ - c₃) ^ j + (d - c₁ - c₂ + c₃) ^ j))) * γ ^ j := by
      intro i
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [hswap, Finset.sum_comm (s := Finset.univ)]
    have hfilt : (Finset.range (k + 1)).filter (fun j => 3 ≤ j ∧ Odd j) =
        (Finset.Icc 2 k).filter (fun j => 3 ≤ j ∧ Odd j) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨by omega, h2, h3⟩
    rw [hfilt, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · simp [c, hj, Finset.sum_mul]
    · simp [c, hj]
  let a : ℕ → ℝ := fun j => (20 * Real.sqrt D / (m : ℝ)) * c j / (10 * Real.sqrt D) ^ j
  obtain ⟨r, hr, hge⟩ := eq_39_helper k hk a
  refine ⟨r, hr, ?_⟩
  let x := Real.cos (Real.pi * r / k)
  have hgamma : gammaGrid D k r = x / (10 * Real.sqrt D) := rfl
  have hexpr : (m : ℝ) / 2 * gammaGrid D k r + PkSum tri rhs k (gammaGrid D k r) =
      ((m : ℝ) / (20 * Real.sqrt D)) * (x + ∑ j ∈ Finset.Icc 2 k, a j * x ^ j) := by
    rw [hgamma, hPkSum_eq]
    have hterm : ∀ j ∈ Finset.Icc 2 k,
        c j * (x / (10 * Real.sqrt D)) ^ j = ((m : ℝ) / (20 * Real.sqrt D)) * (a j * x ^ j) := by
      intro j _
      simp only [a]
      rw [div_pow]
      field_simp [hm_pos.ne', hden_pos.ne']
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    ring
  rw [hexpr, abs_mul, abs_of_pos (by positivity : 0 < (m : ℝ) / (20 * Real.sqrt D))]
  have hmul := mul_le_mul_of_nonneg_left hge (by positivity : 0 ≤ (m : ℝ) / (20 * Real.sqrt D))
  calc (m : ℝ) / (20 * Real.sqrt D * k)
      = (m : ℝ) / (20 * Real.sqrt D) * (1 / (k : ℝ)) := by ring
    _ ≤ (m : ℝ) / (20 * Real.sqrt D) * |x + ∑ j ∈ Finset.Icc 2 k, a j * x ^ j| := hmul
